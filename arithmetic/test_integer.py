import pytest
import z3

from .integer import Integer


def test_empty_constructor():
    i = Integer()
    assert isinstance(i.value(), z3.ArithRef)


def test_int_constructor():
    i = Integer(1)
    assert isinstance(i.value(), z3.ArithRef)


def test_arith_ref_constructor():
    i = Integer(z3.Int("test"))
    assert isinstance(i.value(), z3.ArithRef)


def test_construct_parents():
    Integer(parents={Integer(), Integer()})


@pytest.fixture
def empty_model():
    s = z3.Solver()
    s.check()
    return s.model()


@pytest.mark.parametrize(
    "a,b,difficulty",
    [
        (1, 6, 2),
        (-2, 8, 3),
        (2, -5, 3),
        (-3, -8, 4),
        (10, 1, 3),
        (15, -28, 5),
        (-1004, -152, 9),
    ],
)
def test_add(a, b, difficulty, empty_model):
    result = Integer(a) + Integer(b)
    assert isinstance(result, Integer)
    assert isinstance(result.value(), z3.ArithRef)
    assert empty_model.eval(result.value(), model_completion=True) == a + b
    assert empty_model.eval(result.difficulty(), model_completion=True) == difficulty


@pytest.mark.parametrize(
    "a,b,difficulty",
    [
        (1, 6, 3),
        (-2, 8, 4),
        (2, -5, 4),
        (-3, -8, 5),
        (10, 1, 4),
        (15, -28, 6),
        (-1004, -152, 10),
    ],
)
def test_subtract(a, b, difficulty, empty_model):
    result = Integer(a) - Integer(b)
    assert isinstance(result, Integer)
    assert isinstance(result.value(), z3.ArithRef)
    assert empty_model.eval(result.value(), model_completion=True) == a - b
    assert empty_model.eval(result.difficulty(), model_completion=True) == difficulty


@pytest.mark.parametrize(
    "a,b,difficulty",
    [
        (1, 6, 2),
        (-2, 8, 4),
        (2, -5, 4),
        (-3, -8, 8),
        (10, 1, 4),
        (15, -28, 12),
        (-1004, -152, 40),
    ],
)
def test_multiply(a, b, difficulty, empty_model):
    result = Integer(a) * Integer(b)
    assert isinstance(result, Integer)
    assert isinstance(result.value(), z3.ArithRef)
    assert empty_model.eval(result.value(), model_completion=True) == a * b
    assert empty_model.eval(result.difficulty(), model_completion=True) == difficulty


@pytest.mark.parametrize(
    "a,b,difficulty",
    [
        (1, 6, 5),
        (-2, 8, 8),
        (2, -5, 4),
        (-3, -8, 8),
        (10, 1, 0),
        (15, -28, 54),
    ],
)
def test_power(a, b, difficulty, empty_model):
    result = Integer(a) ** Integer(b)
    assert isinstance(result, Integer)
    assert isinstance(result.value(), z3.ArithRef)
    assert empty_model.eval(result.value(), model_completion=True) == a**b
    assert empty_model.eval(result.difficulty(), model_completion=True) == difficulty
