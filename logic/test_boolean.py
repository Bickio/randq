import pytest
import z3

from logic.boolean import Boolean


def test_empty_constructor():
    b = Boolean()
    assert isinstance(b.value(), z3.BoolRef)


def test_bool_constructor():
    b = Boolean(True)
    assert isinstance(b.value(), z3.BoolRef)


def test_bool_ref_constructor():
    b = Boolean(z3.Bool("test"))
    assert isinstance(b.value(), z3.BoolRef)


@pytest.mark.parametrize(
    "a,b,difficulty",
    [
        (False, False, 1),
        (False, True, 1),
        (True, False, 1),
        (True, True, 1),
    ],
)
def test_and(a, b, difficulty, empty_model):
    result = Boolean(a) & Boolean(b)
    result.override_used()
    assert isinstance(result, Boolean)
    assert isinstance(result.value(), z3.BoolRef)
    assert empty_model.eval(result.value(), model_completion=True) == (a and b)
    assert empty_model.eval(result.difficulty(), model_completion=True) == difficulty


@pytest.mark.parametrize(
    "a,b,difficulty",
    [
        (False, False, 1),
        (False, True, 1),
        (True, False, 1),
        (True, True, 1),
    ],
)
def test_or(a, b, difficulty, empty_model):
    result = Boolean(a) | Boolean(b)
    result.override_used()
    assert isinstance(result, Boolean)
    assert isinstance(result.value(), z3.BoolRef)
    assert empty_model.eval(result.value(), model_completion=True) == (a or b)
    assert empty_model.eval(result.difficulty(), model_completion=True) == difficulty


@pytest.mark.parametrize(
    "a,difficulty",
    [
        (False, 1),
        (True, 1),
    ],
)
def test_not(a, difficulty, empty_model):
    result = ~Boolean(a)
    result.override_used()
    assert isinstance(result, Boolean)
    assert isinstance(result.value(), z3.BoolRef)
    assert bool(empty_model.eval(result.value(), model_completion=True)) != a
    assert empty_model.eval(result.difficulty(), model_completion=True) == difficulty
