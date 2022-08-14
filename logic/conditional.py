import z3

from arithmetic.integer import Integer
from base.variable import Variable
from logic.boolean import Boolean


def if_else(condition: Boolean, if_value: Variable, else_value: Variable):
    for cl in (Boolean, Integer):
        if isinstance(if_value, cl) and isinstance(else_value, cl):
            result = cl(
                z3.If(condition.value(), if_value.value(), else_value.value()),
                parents={condition, if_value, else_value},
                difficulty=1,
                auto_dependents=False,
            )
            break
    else:
        if type(if_value) != type(else_value):
            raise TypeError("if_value and else_value must be the same type")
        else:
            raise NotImplementedError("Variable type not supported by if_else")
    condition.add_dependent(result)
    if_value.add_dependent(result, condition.value())
    else_value.add_dependent(result, z3.Not(condition.value()))
    return result
