from typing import Dict, Any

from arithmetic.integer import Integer
from base.question import Question


class AdditionQuestion(Question):
    @staticmethod
    def givens() -> Dict[str, Integer]:
        return {
            "a": Integer(),
            "b": Integer(),
        }

    @staticmethod
    def solve(givens: Dict[str, Integer]) -> Integer:
        return givens["a"] + givens["b"]

    @staticmethod
    def format_question(givens: Dict[str, Any]):
        return f"What is {givens['a']} + {givens['b']}?"

    @staticmethod
    def format_answer(answer: Any):
        return str(answer)


def test_addition_question():
    q = AdditionQuestion()
    question_text, answer_text = q.generate()
    assert question_text == "What is 0 + 0?"
    assert answer_text == "0"
    question_text, answer_text = q.generate()
    assert question_text == "What is 2 + 2?"
    assert answer_text == "4"
