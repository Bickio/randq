import pytest
import z3


@pytest.fixture
def empty_model():
    s = z3.Solver()
    s.check()
    return s.model()
