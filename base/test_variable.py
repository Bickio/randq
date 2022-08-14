from .variable import Variable


def test_constructor():
    Variable()


def test_difficulty(empty_model):
    v = Variable(difficulty=1)
    v.override_used()
    assert empty_model.eval(v.difficulty(), model_completion=True) == 1


def test_ancestors():
    a = Variable()
    b = Variable(parents={a})
    c = Variable(parents={a, b})
    d = Variable(parents={c})
    assert d.ancestors() == {a, b, c}


def test_used_default(empty_model):
    a = Variable()
    assert not empty_model.eval(a.used(), model_completion=True)


def test_used_override(empty_model):
    a = Variable()
    a.override_used()
    assert empty_model.eval(a.used(), model_completion=True)


def test_add_dependent(empty_model):
    a = Variable()
    b = Variable(parents={a})
    b.override_used()
    assert empty_model.eval(a.used(), model_completion=True)


def test_add_dependent_condition(empty_model):
    a = Variable()
    b = Variable(parents={a}, auto_dependents=False)
    b.override_used()
    a.add_dependent(b, False)
    assert not empty_model.eval(a.used(), model_completion=True)


def test_unused_difficulty(empty_model):
    a = Variable(difficulty=5)
    assert empty_model.eval(a.difficulty(), model_completion=True) == 0
