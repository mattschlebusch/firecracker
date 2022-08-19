// Copyright 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use guest_config::cpu::cpu_config::CustomCpuConfigurationApiRequest;
use logger::{IncMetric, METRICS};

use super::super::VmmAction;
use crate::parsed_request::{Error, ParsedRequest};
use crate::request::Body;

pub(crate) fn parse_put_cpu_config(body: &Body) -> Result<ParsedRequest, Error> {
    METRICS.put_api_requests.cpu_cfg_count.inc();
    Ok(ParsedRequest::new_sync(VmmAction::PutCpuConfiguration(
        serde_json::from_slice::<CustomCpuConfigurationApiRequest>(body.raw()).map_err(|err| {
            METRICS.put_api_requests.cpu_cfg_fails.inc();
            err
        })?,
    )))
}

#[cfg(test)]
mod tests {
    use guest_config::cpu::cpu_config::CpuConfigurationAttribute;
    use logger::{IncMetric, METRICS};
    use micro_http::Body;
    use vmm::rpc_interface::VmmAction;

    use super::*;
    use crate::parsed_request::tests::vmm_action_from_request;

    #[test]
    fn test_parse_put_cpu_config_request_errors() {
        // Test case for invalid payload
        let cpu_config_result = parse_put_cpu_config(&Body::new("<invalid_payload>"));
        assert!(cpu_config_result.is_err());
        assert!(METRICS.put_api_requests.cpu_cfg_fails.count() > 0);

        // Test empty request fails
        assert!(parse_put_cpu_config(&Body::new(r#"{ }"#)).is_err());
    }

    #[test]
    fn test_parse_put_cpu_config_request() {
        let path_str = "/tmp/cpuid-test-file.bin";
        // Test basic request is successful
        let config_request_string = get_correct_json_input(Some(String::from(path_str)));
        let expected_config = CustomCpuConfigurationApiRequest {
            base_arch_features_template_path: String::from(path_str),
            cpu_feature_overrides: vec![
                CpuConfigurationAttribute {
                    name: String::from("ssbd"),
                    is_enabled: false,
                },
                CpuConfigurationAttribute {
                    name: String::from("ibrs"),
                    is_enabled: true,
                },
            ],
        };

        match vmm_action_from_request(
            parse_put_cpu_config(&Body::new(config_request_string.as_str())).unwrap(),
        ) {
            VmmAction::PutCpuConfiguration(config_request) => {
                assert_eq!(config_request, expected_config)
            }
            _ => panic!("Test failed - Expected VmmAction::PutCpuConfiguration() call"),
        }

        // Test that applying a CPU config is successful on x86_64 while on aarch64, it is not.
        #[cfg(target_arch = "x86_64")]
        {
            match vmm_action_from_request(
                parse_put_cpu_config(&Body::new(config_request_string.as_str())).unwrap(),
            ) {
                VmmAction::PutCpuConfiguration(config_request) => {
                    assert_eq!(config_request, expected_config)
                }
                _ => panic!("Test failed - Expected VmmAction::PutCpuConfiguration() call"),
            }
        }

        #[cfg(target_arch = "aarch64")]
        {
            assert!(parse_put_cpu_config(&Body::new(body)).is_err());
        }
    }

    // test helper for generating correct JSON input data
    fn get_correct_json_input(arch_features_file_path: Option<String>) -> String {
        format!(
            r#"
        {{
          "base_arch_features_template_path": "{}",
          "cpu_feature_overrides": [
            {{
              "name" : "ssbd",
              "is_enabled" : false
            }},
            {{
              "name" : "ibrs",
              "is_enabled" : true
            }}
          ]
        }}
        "#,
            arch_features_file_path.unwrap_or(String::from("/tmp/cpuid-test.json"))
        )
    }
}
