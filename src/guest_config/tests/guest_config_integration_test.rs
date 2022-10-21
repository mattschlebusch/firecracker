// Copyright 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

/// Implemented as an integration test due to interactions
/// with KVM and will require a host environment with KVM
/// setup to run successfully.
#[cfg(test)]
#[cfg(target_os = "linux")]
mod guest_config_integ_tests {
    use std::fs;

    use tempfile::Builder;

    #[test]
    #[cfg(target_arch = "x86_64")]
    fn test_host_cpuid_snapshot() {
        let cpuid_tempfile = Builder::new()
            .prefix("cpuid-test")
            .suffix(".bin")
            .tempfile()
            .expect("Failed to create temporary file for testing CPUID");
        let cpuid_file_path =
            fs::canonicalize(cpuid_tempfile.path()).expect("Retrieving tempfile path required.");
        let path_str = cpuid_file_path
            .to_str()
            .expect("Error retrieving file path.");

        let write_snapshot_result = guest_config::snapshot_host_cpu_config(path_str);
        assert!(write_snapshot_result.is_ok());

        // Now read the snapshot file to test
        let read_snapshot_result = guest_config::read_cpu_config_binary_file(path_str);
        assert!(read_snapshot_result.is_ok());

        assert_eq!(
            write_snapshot_result.unwrap(),
            read_snapshot_result.unwrap()
        );
    }
}
