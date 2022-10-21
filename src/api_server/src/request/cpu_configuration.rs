// Copyright 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use guest_config::CustomCpuConfiguration;
use logger::{log_dev_preview_warning, IncMetric, METRICS};

use super::super::VmmAction;
use crate::parsed_request;
use crate::parsed_request::{Error, ParsedRequest};
use crate::request::Body;

pub(crate) fn parse_put_cpu_config(body: &Body) -> Result<ParsedRequest, Error> {
    METRICS.put_api_requests.cpu_cfg_count.inc();
    log_dev_preview_warning("User-defined CPU configuration", Option::None);

    // Convert the API request into a a deserialized/binary format
    let cpu_config =
        serde_json::from_slice::<CustomCpuConfiguration>(body.raw()).map_err(|err| {
            METRICS.put_api_requests.cpu_cfg_fails.inc();
            parsed_request::Error::SerdeJson(err)
        })?;

    Ok(ParsedRequest::new_sync(VmmAction::PutCpuConfiguration(
        cpu_config,
    )))
}

#[cfg(test)]
mod api_cpu_configuration_unit_tests {
    use std::fs;
    use std::path::Path;

    use logger::{IncMetric, METRICS};
    use micro_http::Body;
    use vmm::rpc_interface::VmmAction;

    use super::*;
    use crate::parsed_request::tests::vmm_action_from_request;

    const TEST_CPU_TEMPLATE_JSON_FILE_PATH: &str =
        "../../resources/guest_configs/cpu/x86_64_user_config_template_example.json";

    #[test]
    fn test_parse_put_cpu_config_request() {
        // Bootstrap some test data first
        let user_cpu_template_read_result =
            fs::read_to_string(Path::new(TEST_CPU_TEMPLATE_JSON_FILE_PATH));
        assert!(&user_cpu_template_read_result.is_ok());

        let user_cpu_template_string = user_cpu_template_read_result.unwrap();
        let user_config_request_result =
            guest_config::deserialize_cpu_config(user_cpu_template_string.as_str());
        assert!(user_config_request_result.is_ok());
        let test_cpu_config: CustomCpuConfiguration = user_config_request_result.unwrap();

        // Test that applying a CPU config is successful on x86_64 while on aarch64, it is not.
        {
            match vmm_action_from_request(
                parse_put_cpu_config(&Body::new(user_cpu_template_string.as_bytes())).unwrap(),
            ) {
                VmmAction::PutCpuConfiguration(received_cpu_config) => {
                    // Test that the CPU config to be used for KVM config is the
                    // the same that was read in from a test file.
                    assert_eq!(test_cpu_config, received_cpu_config);
                }
                _ => panic!("Test failed - Expected VmmAction::PutCpuConfiguration() call"),
            }
        }
    }

    /// Test basic API server validations like JSON sanity/legibility
    /// Any testing or validation done involving KVM or OS specific context
    /// need to be done in integration testing (api_cpu_configuration_integ_tests)
    #[test]
    fn test_parse_put_cpu_config_request_errors() {
        let mut expected_err_count = METRICS.put_api_requests.cpu_cfg_fails.count() + 1;

        // Test case for invalid payload
        let cpu_config_result = parse_put_cpu_config(&Body::new("<invalid_payload>"));
        assert!(cpu_config_result.is_err());
        assert_eq!(
            METRICS.put_api_requests.cpu_cfg_fails.count(),
            expected_err_count
        );
        expected_err_count += 1;

        // Test empty request fails
        assert!(parse_put_cpu_config(&Body::new(r#"{ }"#)).is_err());
        assert_eq!(
            METRICS.put_api_requests.cpu_cfg_fails.count(),
            expected_err_count
        );
    }
}
