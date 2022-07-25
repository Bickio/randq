from .variable import Variable


def test_constructor():
    Variable()


def test_difficulty():
    v = Variable(difficulty=1)
    assert v.difficulty() == 1


def test_ancestors():
    a = Variable()
    b = Variable(parents={a})
    c = Variable(parents={a, b})
    d = Variable(parents={c})
    assert d.ancestors() == {a, b, c}
