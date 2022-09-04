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
    result.override_used()
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
    result.override_used()
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
    result.override_used()
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
    result.override_used()
    assert isinstance(result, Integer)
    assert isinstance(result.value(), z3.ArithRef)
    assert empty_model.eval(result.value(), model_completion=True) == a**b
    assert empty_model.eval(result.difficulty(), model_completion=True) == difficulty


@pytest.mark.parametrize(
    "a,b,difficulty",
    [
        (6, 1, 2),
        (6, 2, 2),
        (6, 3, 2),
        (12, 3, 4),
        (12, -3, 8),
    ],
)
def test_divide(a, b, difficulty, empty_model):
    result = Integer(a) // Integer(b)
    result.override_used()
    assert isinstance(result, Integer)
    assert isinstance(result.value(), z3.ArithRef)
    assert empty_model.eval(result.value(), model_completion=True) == a / b
    assert empty_model.eval(result.difficulty(), model_completion=True) == difficulty


def test_divide_constraint():
    s = z3.Solver()
    a = Integer(5)
    b = Integer(2)
    result = a // b
    result.override_used()
    s.add(a.constraints())
    s.add(b.constraints())
    s.add(result.constraints())
    assert s.check() == z3.unsat


@pytest.mark.parametrize(
    "a,b,difficulty",
    [
        (6, 4, 2),
        (5, 2, 2),
        (7, 3, 2),
        (14, 3, 4),
        (26, -3, 8),
        (-26, 3, 6),
        (-26, -3, 12),
    ],
)
def test_mod(a, b, difficulty, empty_model):
    result = Integer(a) % Integer(b)
    result.override_used()
    assert isinstance(result, Integer)
    assert isinstance(result.value(), z3.ArithRef)
    assert empty_model.eval(result.value(), model_completion=True) == a % abs(b)
    assert empty_model.eval(result.difficulty(), model_completion=True) == difficulty


@pytest.mark.parametrize(
    "a,b",
    [
        (1, 0),
        (2, 3),
        (-1, 2),
        (12, 5),
        (2, -1),
        (1, 1),
        (-3, -3),
    ],
)
def test_inequality(a, b, empty_model):
    i_a = Integer(a)
    i_b = Integer(b)
    less = i_a < i_b
    greater = i_a > i_b
    less_equal = i_a <= i_b
    greater_equal = i_a >= i_b
    for result in [less, greater, less_equal, greater_equal]:
        result.override_used()
        assert empty_model.eval(result.difficulty(), model_completion=True) == 1
    assert empty_model.eval(less.value(), model_completion=True) == (a < b)
    assert empty_model.eval(greater.value(), model_completion=True) == (a > b)
    assert empty_model.eval(less_equal.value(), model_completion=True) == (a <= b)
    assert empty_model.eval(greater_equal.value(), model_completion=True) == (a >= b)


def test_min_max():
    i = Integer(maximum=1, minimum=1)
    s = z3.Solver()
    s.add(*i.constraints())
    s.check()
    model = s.model()
    assert model.eval(i.value(), model_completion=True) == 1
