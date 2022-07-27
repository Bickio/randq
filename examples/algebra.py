"""
Questions formats taken from:
NZQA Level 1 Mathematics and Statistics 2021
91027 Apply algebraic procedures in solving problems
Paper A
"""
from typing import Any, Dict

from arithmetic.integer import Integer
from base.question import Question


class QuestionOne(Question):
    @staticmethod
    def givens():
        return {
            "x": Integer(minimum=-9, maximum=9),
            "y": Integer(minimum=-9, maximum=9),
            "a": Integer(minimum=2, maximum=9),
            "b": Integer(minimum=2, maximum=9),
        }

    @staticmethod
    def solve(givens):
        return (
            givens["a"] * (givens["x"] ** Integer(2))
            - givens["b"] * givens["x"] * givens["y"]
        )

    @staticmethod
    def format_question(givens: Dict[str, Any]):
        return (
            f"Find the value of {givens['a']}x^2 - {givens['b']}xy "
            f"when x={givens['x']} and y={givens['y']}."
        )

    @staticmethod
    def format_answer(answer: Any):
        return str(answer)


def main():
    q1 = QuestionOne(min_difficulty=10, max_difficulty=12)
    for i, (prompt, answer, difficulty) in zip(range(10), q1.variations()):
        print(prompt)
        print(answer)
        print("Difficulty:", difficulty)


if __name__ == "__main__":
    main()
