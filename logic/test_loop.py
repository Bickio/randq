import pytest
import z3

from arithmetic.integer import Integer
from logic.boolean import Boolean
from logic.loop import while_cond


def test_no_loop(empty_model):
    def cond(x):
        return Boolean(False)

    def loop(x):
        return x

    result = while_cond(cond, loop, Integer(0))
    result.override_used()
    assert empty_model.eval(result.value(), model_completion=True) == 0
    assert empty_model.eval(result.difficulty(), model_completion=True) == 1


@pytest.mark.parametrize(
    "stop,difficulty",
    [
        (0, 2),
        (1, 6),
        (2, 10),
        (3, 14),
    ],
)
def test_counter(stop: int, difficulty: int, empty_model: z3.ModelRef):
    def cond(x):
        return x < Integer(stop)

    def loop(x):
        return x + Integer(1)

    result = while_cond(cond, loop, Integer(0), 5)
    result.override_used()
    assert empty_model.eval(result.value(), model_completion=True) == stop
    assert empty_model.eval(result.difficulty(), model_completion=True) == 1
    assert (
        empty_model.eval(result.total_difficulty(), model_completion=True) == difficulty
    )
