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


def test_add():
    a = Integer(1)
    b = Integer(2)
    c = a + b
    assert isinstance(c, Integer)
    assert isinstance(c.value(), z3.ArithRef)
    assert str(c.value()) == "1 + 2"


def test_subtract():
    a = Integer(3)
    b = Integer(2)
    c = a - b
    assert isinstance(c, Integer)
    assert isinstance(c.value(), z3.ArithRef)
    assert str(c.value()) == "3 - 2"
