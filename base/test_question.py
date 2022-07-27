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
    generator = q.variations()
    question_text, answer_text, difficulty = next(generator)
    assert question_text.startswith("What is ")
    assert answer_text.isdigit() or (
        answer_text.startswith("-") and answer_text[1:].isdigit()
    )


def test_difficulty():
    q = AdditionQuestion(min_difficulty=2, max_difficulty=2)
    num_variations = 0
    for q_text, a_text, difficulty in q.variations():
        assert difficulty == 2
        num_variations += 1
    assert num_variations == 100
