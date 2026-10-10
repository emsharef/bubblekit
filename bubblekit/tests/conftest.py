import importlib.util
import os
import sys

import numpy as np
import pytest

LAB_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))


@pytest.fixture
def rng():
    return np.random.default_rng(20261009)


def load_lab(name, rel):
    """Load a module from the research lab's tree, or skip the test when the lab code is not present."""
    path = os.path.join(LAB_ROOT, rel)
    if not os.path.exists(path):
        pytest.skip(f"lab reference code not available: {rel}")
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod
