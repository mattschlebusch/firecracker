# Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
"""Tests for the user-defined CPU feature configurability."""

import platform
import pytest

from framework import utils
from framework.artifacts import ArtifactCollection, ArtifactSet
from framework.builder import MicrovmBuilder
import framework.utils_cpuid as cpuid_utils

PLATFORM = platform.machine()


@pytest.mark.skipif(
    PLATFORM != "x86_64",
    reason="CPU features are masked only on x86_64 supported architectures.",
)
@pytest.mark.skipif(
    cpuid_utils.get_cpu_vendor() != cpuid_utils.CpuVendor.INTEL,
    reason="CPU configurability is only available on Intel.",
)
@pytest.mark.parametrize(
    "test_cpu_config_path",
    [
        ("framework/resources/cpu_template_config_x86_64_t2s.json"),
    ],
)
def test_cpu_config_params(test_microvm_with_api, test_cpu_config_path):
    """
    Test microvm start with user-defined cpu configuration.

    @type: functional
    """
    test_microvm = test_microvm_with_api
    test_microvm.cpu_cfg.put(test_cpu_config_path)
    test_microvm.spawn()

    cpu_vendor = utils_cpuid.get_cpu_vendor()

    check_for_failed_start = (
        (cpu_vendor == utils_cpuid.CpuVendor.AMD and fail_amd)
        or (cpu_vendor == utils_cpuid.CpuVendor.INTEL and fail_intel)
        or (platform.machine() == "aarch64" and fail_aarch64)
    )

    if check_for_failed_start:
        test_microvm.check_any_log_message(
            [
                "Building VMM configured from cmdline json failed: ",
                "Configuration for VMM from one single json failed",
            ]
        )
    else:
        test_microvm.check_log_message(
            "Successfully started microvm that was configured " "from one single json"
        )
