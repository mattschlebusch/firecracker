// Copyright 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::fs;
use std::fs::File;
use std::io::{BufWriter, Read};
use std::path::Path;

use cpuid::{Cpuid, CpuidNewError};
use logger::{debug, error, info, warn};
use serde::{Deserialize, Serialize};

/// Contains types used to configure guest vCPUs.
pub mod cpu;

/// Contains all CPU feature configuration in binary format
/// Currently only contains CPUID configuration (x86).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CustomCpuConfiguration {
    /// Blob for architecture general features (CPUID for x86)
    pub base_arch_config: Cpuid,
}

/// Errors associated with processing CPU configuration
#[derive(Debug, thiserror::Error)]
pub enum GuestConfigurationError {
    /// Error while configuring CPU features via CPUID.
    #[error("Failed to configure CPU (CPUID) features")]
    CpuId(CpuidNewError),
    /// Error while configuration model-specific registers.
    #[error("Error while configuring CPU features via model-specific registers")]
    MSR,
    /// JSON library(serde) error processing JSON data.
    #[error("Error processing guest configuration in JSON format - [{0}]")]
    JsonError(serde_json::Error),
    /// Opening or reading the file was unsuccessful.
    #[error("Unable to use file specified [{0}].")]
    InvalidFilePath(String),
    /// Opening or reading the file was unsuccessful.
    #[error("Unable to use file specified [{0}]. \n[{1}]")]
    IOError(String, std::io::Error),
    /// Binary file operation was unsuccessful.
    #[error("Error handling binary file [{0}]. See error [{1}]")]
    BinaryFileOperationError(String, bincode::Error),
    /// Binary file not valid.
    #[error("Invalid or empty binary file specified [{0}].")]
    InvalidBinaryFileSpecified(String),
    /// Unsupported CPU platform.
    #[error("Provided CPUID configures CPU [{0}] that is not supported in Firecracker")]
    UnsupportedCpuPlatform(String),
}

/// guest config compiler function to write json from a source file
/// to a target file in a binary format
pub fn write_cpu_config_binary_file(
    target_path_str: &str,
    cpu_config: &CustomCpuConfiguration,
) -> Result<(), GuestConfigurationError> {
    let output_file = File::create(target_path_str)
        .map_err(|err| GuestConfigurationError::IOError(String::from(target_path_str), err))?;

    Ok(
        bincode::serialize_into(BufWriter::new(output_file), &cpu_config).map_err(|err| {
            GuestConfigurationError::BinaryFileOperationError(String::from(target_path_str), err)
        }),
    )?
}

/// Provides an example CPU configuration using the host's KVM supported CPUID functions.
pub fn snapshot_host_cpu_config(
    target_path_str: &str,
) -> Result<CustomCpuConfiguration, GuestConfigurationError> {
    info!("Building CPU configuration from host context");

    let cpu_config = CustomCpuConfiguration {
        base_arch_config: unsafe { Cpuid::new() }
            .map_err(|err| GuestConfigurationError::CpuId(err))?,
    };
    write_cpu_config_binary_file(target_path_str, &cpu_config)?;
    info!(
        "CPU configuration from host context written to [{}]",
        target_path_str
    );
    Ok(cpu_config)
}

/// Reads CPU config data from the filesystem
pub fn read_cpu_config_binary_file(
    file_path_str: &str,
) -> Result<CustomCpuConfiguration, GuestConfigurationError> {
    let file_path = Path::new(&file_path_str);
    warn!(
        "Loading binary file for CPU configuration - [{}]",
        file_path_str
    );

    let mut cpu_config_file = File::open(file_path)
        .map_err(|err| GuestConfigurationError::IOError(file_path_str.to_string(), err))?;
    let metadata = fs::metadata(&file_path)
        .map_err(|err| GuestConfigurationError::IOError(file_path_str.to_string(), err))?;

    if !metadata.is_file() {
        return Err(GuestConfigurationError::InvalidFilePath(
            file_path_str.to_string(),
        ));
    }

    let mut cpu_config_buffer = vec![0; metadata.len() as usize];
    let bytes_count = cpu_config_file
        .read(&mut cpu_config_buffer)
        .map_err(|err| GuestConfigurationError::IOError(file_path_str.to_string(), err))?;
    if bytes_count == 0 {
        return Err(GuestConfigurationError::InvalidBinaryFileSpecified(
            file_path_str.to_string(),
        ));
    }

    let cpu_config_result: Result<CustomCpuConfiguration, bincode::Error> =
        bincode::deserialize(&cpu_config_buffer);
    match cpu_config_result {
        Ok(cpu_config) => Ok(cpu_config),
        Err(err) => {
            error!("Error handling binary file: {:?}", err);
            Err(GuestConfigurationError::BinaryFileOperationError(
                String::from(file_path_str),
                err,
            ))
        }
    }
}

/// Converts JSON string of a Cpuid instance to an in-memory instance.
pub fn deserialize_cpu_config(
    cpu_config_str: &str,
) -> Result<CustomCpuConfiguration, GuestConfigurationError> {
    debug!(
        "Deserializing JSON CPU config structure \n{}",
        &cpu_config_str
    );
    match serde_json::from_str(cpu_config_str) {
        Ok(cpu_config) => {
            info!("Parsed JSON CPU config successfully");
            Ok(cpu_config)
        }
        Err(err) => {
            error!("Failed to parse JSON CPU config");
            Err(GuestConfigurationError::JsonError(err))
        }
    }
}

#[cfg(test)]
mod guest_config_unit_tests {
    use std::fs;
    use std::fs::read;
    use std::path::Path;

    use tempfile::Builder;

    use crate::{
        deserialize_cpu_config, read_cpu_config_binary_file, write_cpu_config_binary_file,
        GuestConfigurationError,
    };

    const TEST_CPU_TEMPLATE_JSON_FILE_PATH: &str =
        "../../resources/guest_configs/cpu/x86_64_user_config_template_example.json";
    #[test]
    fn test_custom_cpu_config_serialization_lifecycle() {
        let cpu_config_tempfile = Builder::new()
            .prefix("cpu-config-test")
            .suffix(".bin")
            .tempfile()
            .expect("Failed to create temporary file for testing CPU config");
        let cpu_config_file_path = fs::canonicalize(cpu_config_tempfile.path())
            .expect("Retrieving tempfile path required.");
        let path_str = cpu_config_file_path
            .to_str()
            .expect("Error retrieving file path.");

        let cpu_config_json_result =
            fs::read_to_string(Path::new(TEST_CPU_TEMPLATE_JSON_FILE_PATH));
        assert!(
            cpu_config_json_result.is_ok(),
            "{}",
            cpu_config_json_result.unwrap_err()
        );

        let deserialized_cpu_config_json_result =
            deserialize_cpu_config(cpu_config_json_result.unwrap().as_str());
        assert!(
            deserialized_cpu_config_json_result.is_ok(),
            "{}",
            deserialized_cpu_config_json_result.unwrap_err()
        );
        let deserialized_cpu_config = deserialized_cpu_config_json_result.unwrap();
        let write_cpu_config_file_result =
            write_cpu_config_binary_file(path_str, &deserialized_cpu_config);
        assert!(
            write_cpu_config_file_result.is_ok(),
            "{}",
            write_cpu_config_file_result.unwrap_err()
        );

        // Read the freshly written CPU config binary file.
        let read_cpu_config_file_result = read_cpu_config_binary_file(path_str);
        assert!(
            read_cpu_config_file_result.is_ok(),
            "{}",
            read_cpu_config_file_result.unwrap_err()
        );

        // Check that the CPU config deserialized from JSON is equal to what was read from
        // the freshly written binary file.
        assert_eq!(
            deserialized_cpu_config,
            read_cpu_config_file_result.unwrap()
        );
    }

    #[test]
    fn test_read_bin_file_errors() {
        const INVALID_FILE_NAME: &str = "not a file";
        let cpu_config_binary_file_result = read_cpu_config_binary_file(INVALID_FILE_NAME);
        assert!(
            cpu_config_binary_file_result.is_err(),
            "Expected IO error reading undefined file."
        );
        match cpu_config_binary_file_result.unwrap_err() {
            GuestConfigurationError::IOError(_, _) => {}
            _ => fail::fail_point!("GuestConfiguration::IOError error expected"),
        }

        let tempdir = Builder::new()
            .prefix("guest-config-test-dir")
            .tempdir()
            .expect("Failed to create temporary directory for testing");
        let directory_path =
            fs::canonicalize(tempdir.path()).expect("Retrieving tempdir path failed.");
        let path_string = String::from(
            directory_path
                .to_str()
                .expect("Error retrieving folder path as string."),
        );
        let cpu_config_binary_file_result = read_cpu_config_binary_file(path_string.as_str());
        assert!(cpu_config_binary_file_result.is_err());
        match cpu_config_binary_file_result.unwrap_err() {
            GuestConfigurationError::InvalidFilePath(_path_str) => {}
            _ => fail::fail_point!("GuestConfiguration::InvalidFilePath error expected"),
        }
    }
}
