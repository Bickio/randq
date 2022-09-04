import z3

from arithmetic.integer import Integer
from base.variable import Variable
from logic.boolean import Boolean


def if_else(condition: Boolean, if_value: Variable, else_value: Variable):
    if isinstance(if_value, tuple) and isinstance(else_value, tuple):
        if_values, else_values = if_value, else_value
    else:
        if_values, else_values = (if_value,), (else_value,)

    results = []
    for if_val, else_val in zip(if_values, else_values):
        for cl in (Boolean, Integer):
            if isinstance(if_val, cl) and isinstance(else_val, cl):
                result = cl(
                    z3.If(condition.value(), if_val.value(), else_val.value()),
                    parents={condition, if_val, else_val},
                    difficulty=1,
                    auto_dependents=False,
                )
                break
        else:
            if type(if_val) != type(else_val):
                raise TypeError("if_val and else_val must be the same type")
            else:
                raise NotImplementedError("Variable type not supported by if_else")
        if_val.add_dependent(result, condition.value())
        else_val.add_dependent(result, z3.Not(condition.value()))
        condition.add_dependent(result)
        results.append(result)
    if len(results) == 1:
        return results[0]
    else:
        return tuple(results)
