// Copyright 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#[cfg(test)]
mod api_cpu_configuration_integ_tests {
    use std::io::{Read, Write};
    use std::os::unix::net::UnixStream;
    use std::path::{Path, PathBuf};
    use std::sync::mpsc::channel;
    use std::{fs, thread};

    use api_server::ApiServer;
    use format_bytes::format_bytes;
    use logger::ProcessTimeReporter;
    use parameterized::parameterized;
    use utils::eventfd::EventFd;
    use utils::tempfile::TempFile;
    use vmm::seccomp_filters::{get_filters, SeccompConfig};

    const HTTP_OK_RESPONSE: &str = "HTTP/1.1 200";
    const TEST_CPU_TEMPLATE_JSON_FILE_PATH: &str =
        "../../resources/guest_configs/cpu/x86_64_user_config_template_example.json";
    const TEST_AMD_CPU_TEMPLATE_JSON_FILE_PATH: &str =
        "../../resources/guest_configs/cpu/x86_64_amd_user_config_template_example.json";

    #[parameterized(cpu_config_path = {
        TEST_CPU_TEMPLATE_JSON_FILE_PATH, TEST_AMD_CPU_TEMPLATE_JSON_FILE_PATH
    }, api_payload_size = {
        19849, 52
    })]
    #[cfg(target_arch = "x86_64")]
    #[cfg(target_os = "linux")]
    fn test_put_cpu_config(cpu_config_path: &str, api_payload_size: usize) {
        let mut tmp_socket = TempFile::new().unwrap();
        tmp_socket.remove().unwrap();
        let path_to_socket = tmp_socket.as_path().to_str().unwrap().to_owned();
        let api_thread_path_to_socket = path_to_socket.clone();

        let to_vmm_fd = EventFd::new(libc::EFD_NONBLOCK).unwrap();
        let (api_request_sender, _from_api) = channel();
        let (_to_api, vmm_response_receiver) = channel();
        let seccomp_filters = get_filters(SeccompConfig::Advanced).unwrap();
        let (socket_ready_sender, socket_ready_receiver) = channel();

        let mut api_server = ApiServer::new(api_request_sender, vmm_response_receiver, to_vmm_fd);
        thread::Builder::new()
            .name("fc_api_integ_test".to_owned())
            .spawn(move || {
                api_server
                    .bind_and_run(
                        PathBuf::from(api_thread_path_to_socket),
                        ProcessTimeReporter::new(Some(1), Some(1), Some(1)),
                        seccomp_filters.get("api").unwrap(),
                        api_payload_size,
                        socket_ready_sender,
                    )
                    .unwrap();
            })
            .unwrap();

        // Wait for the server to be available for requests
        socket_ready_receiver.recv().unwrap();
        let mut sock = UnixStream::connect(PathBuf::from(path_to_socket)).unwrap();

        // Send PUT /cpu-config request.
        assert!(sock
            .write_all(build_http_put_cpu_config_request(cpu_config_path).as_slice())
            .is_ok());
        let mut buf = [0; 265];
        assert!(sock.read(&mut buf).unwrap() > 0);
        let server_response = String::from_utf8_lossy(&buf);
        assert!(
            &server_response.to_string().contains(HTTP_OK_RESPONSE),
            "Successful response (200 OK) expected from API server but received: \n\r{}",
            server_response.to_string(),
        );
    }

    fn build_http_put_cpu_config_request(cpu_config_path: &str) -> Vec<u8> {
        let cpu_template_read_result = fs::read(Path::new(cpu_config_path));
        assert!(cpu_template_read_result.is_ok());
        let cpu_template_json_string = cpu_template_read_result.unwrap();

        let content_length = cpu_template_json_string.len() + 16;
        format_bytes!(
            b"PUT http://localhost/cpu-config HTTP/1.1\r\n\
            Content-Type: application/json\r\n\
            Content-Length: {}\r\n\r\n{{\
            \"payload\": \"{}\"\r\n\
            }}",
            content_length,
            cpu_template_json_string,
        )
    }
}
