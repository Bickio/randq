import pytest

from arithmetic.integer import Integer
from base.variable import Variable
from logic.boolean import Boolean
from logic.conditional import if_else


def test_if_else_types():
    with pytest.raises(TypeError):
        if_else(Boolean(True), Boolean(True), Integer(1))
    with pytest.raises(NotImplementedError):
        if_else(Boolean(True), Variable(), Variable())


@pytest.mark.parametrize(
    "cond,a,b,difficulty",
    [
        (False, True, False, 1),
        (False, False, True, 1),
        (True, True, False, 1),
        (True, False, True, 1),
    ],
)
def test_if_else_boolean(cond, a, b, difficulty, empty_model):
    bool_cond = Boolean(cond, difficulty=3)
    bool_a = Boolean(a, difficulty=5)
    bool_b = Boolean(b, difficulty=7)
    result = if_else(bool_cond, bool_a, bool_b)
    result.override_used()
    assert empty_model.eval(result.value(), model_completion=True) == (a if cond else b)
    assert empty_model.eval(result.difficulty(), model_completion=True) == difficulty
    assert empty_model.eval(bool_cond.difficulty(), model_completion=True) == 3
    if cond:
        assert empty_model.eval(bool_a.difficulty(), model_completion=True) == 5
        assert empty_model.eval(bool_b.difficulty(), model_completion=True) == 0
    else:
        assert empty_model.eval(bool_a.difficulty(), model_completion=True) == 0
        assert empty_model.eval(bool_b.difficulty(), model_completion=True) == 7
