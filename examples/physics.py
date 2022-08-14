from typing import Any, Dict

from arithmetic.integer import Integer
from base.question import Question
from logic.conditional import if_else


def solve_reaching_terminal(gravity, total_time, terminal_velocity, time_to_terminal):
    distance_to_terminal = (gravity * time_to_terminal ** Integer(2)) // Integer(2)
    remaining_time = total_time - time_to_terminal
    remaining_distance = remaining_time * terminal_velocity
    return distance_to_terminal + remaining_distance


def solve_not_reaching_terminal(gravity, total_time):
    return (gravity * total_time ** Integer(2)) // Integer(2)


class TerminalVelocity(Question):
    @staticmethod
    def givens():
        return {
            "time": Integer(minimum=0, maximum=60),
            "terminal_velocity": Integer(minimum=50, maximum=100),
        }

    @staticmethod
    def solve(givens):
        gravity = Integer(10)
        total_time: Integer = givens["time"]
        terminal_velocity: Integer = givens["terminal_velocity"]
        time_to_terminal = terminal_velocity // gravity
        return if_else(
            time_to_terminal > total_time,
            solve_not_reaching_terminal(gravity, total_time),
            solve_reaching_terminal(
                gravity, total_time, terminal_velocity, time_to_terminal
            ),
        )

    @staticmethod
    def format_question(givens: Dict[str, Any]):
        return (
            f"A skydiver jumps from a plane.\n"
            f"His terminal velocity is {givens['terminal_velocity']}m/s.\n"
            "Assume gravity is 10m/s^2.\n"
            f"How far has he fallen after {givens['time']} seconds?"
        )

    @staticmethod
    def format_answer(answer: Any):
        return f"{answer}m"


def main():
    q1 = TerminalVelocity(min_difficulty=25, max_difficulty=40)
    for i, (prompt, answer, difficulty) in zip(range(10), q1.variations()):
        print(prompt)
        print("Answer:", answer)
        print("Difficulty:", difficulty)
        print()


if __name__ == "__main__":
    main()
