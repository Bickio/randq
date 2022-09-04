from typing import Dict, Any, Tuple

from arithmetic.integer import Integer
from base.question import Question
from logic.loop import while_cond


class EuclideanAlgorithm(Question):
    @staticmethod
    def givens():
        return {
            "a": Integer(minimum=0, maximum=99),
            "b": Integer(minimum=0, maximum=99),
        }

    @staticmethod
    def solve(givens):
        a, b = givens["a"], givens["b"]
        a, b = while_cond(
            EuclideanAlgorithm.condition,
            EuclideanAlgorithm.loop,
            (a, b),
        )
        return a

    @staticmethod
    def condition(val: Tuple[Integer, Integer]):
        a, b = val
        return b != Integer(0)

    @staticmethod
    def loop(val: Tuple[Integer, Integer]):
        a, b = val
        return b, a % b

    @staticmethod
    def format_question(givens: Dict[str, Any]):
        return (
            f"Use the euclidean algorithm to find the GCD of"
            f" {givens['a']} and {givens['b']}"
        )

    @staticmethod
    def format_answer(answer: Any):
        return f"{answer}"


def main():
    q1 = EuclideanAlgorithm(min_difficulty=50, max_difficulty=60)
    for i, (prompt, answer, difficulty) in zip(range(10), q1.variations()):
        print(prompt)
        print("Answer:", answer)
        print("Difficulty:", difficulty)
        print()


if __name__ == "__main__":
    main()
