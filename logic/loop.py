from typing import TypeVar, Callable

import z3

from base.variable import Variable
from logic.boolean import Boolean
from logic.conditional import if_else

T = TypeVar("T")


def while_cond(
    condition: Callable[[T], Boolean],
    loop: Callable[[T], T],
    initial: T,
    max_loops=10,
):
    cond = condition(initial)
    result = loop(initial)
    if max_loops == 0:
        if isinstance(initial, Variable):
            initial.constraints().append(z3.Not(cond.value()))
        elif (
            isinstance(initial, tuple)
            and len(initial) > 0
            and isinstance(initial[0], Variable)
        ):
            initial[0].constraints().append(z3.Not(cond.value()))
        else:
            raise NotImplementedError("while_cond does not support this type T")
        return if_else(
            cond,
            initial,
            initial,
        )
    return if_else(
        cond,
        while_cond(condition, loop, result, max_loops=max_loops - 1),
        initial,
    )
