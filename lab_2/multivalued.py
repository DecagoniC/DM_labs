"""Интерпретатор многозначных логик и проверка семантических свойств формул.

Лабораторная работа №2, вариант 3.

Поддерживаются три логические системы:
  * cl — классическая двузначная логика, значения {0, 1};
  * k3 — сильная трёхзначная логика Клини, значения {0, 1/2, 1};
  * l3 — трёхзначная логика Лукасевича, значения {0, 1/2, 1}.

Семантика связок:
  ¬a     = 1 − a
  a ∧ b  = min(a, b)
  a ∨ b  = max(a, b)
  a →K3 b = max(1 − a, b)
  a →L3 b = min(1, 1 − a + b)

Значения истинности хранятся как fractions.Fraction, поэтому 1/2 точное.
"""

import re
import sys
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from pathlib import Path


class ParseError(Exception):
    """Строка не является правильно построенной формулой."""


class EvaluationError(Exception):
    """Не заданы значения всех переменных формулы."""


# ---------------------------------------------------------------------------
# Синтаксическое дерево и парсер
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Var:
    name: str


@dataclass(frozen=True)
class Not:
    child: "Formula"


@dataclass(frozen=True)
class And:
    left: "Formula"
    right: "Formula"


@dataclass(frozen=True)
class Or:
    left: "Formula"
    right: "Formula"


@dataclass(frozen=True)
class Imp:
    left: "Formula"
    right: "Formula"


Formula = Var | Not | And | Or | Imp

NOT_TOKENS = {"¬", "~", "!"}
AND_TOKENS = {"∧", "&", "^"}
OR_TOKENS = {"∨", "|"}
IMP_TOKENS = {"→", "⊃", ">"}


def show(formula: Formula) -> str:
    """Каноническая запись формулы (полностью расставлены скобки)."""
    if isinstance(formula, Var):
        return formula.name
    if isinstance(formula, Not):
        return "¬" + show(formula.child)
    if isinstance(formula, And):
        symbol = "∧"
    elif isinstance(formula, Or):
        symbol = "∨"
    else:
        symbol = "→"
    return "(" + show(formula.left) + symbol + show(formula.right) + ")"


def tokenize(text: str) -> list[tuple[str, str]]:
    tokens: list[tuple[str, str]] = []
    index = 0
    while index < len(text):
        char = text[index]
        if char.isspace():
            index += 1
            continue
        two = text[index : index + 2]
        if two in {"->", "=>"}:
            tokens.append(("imp", two))
            index += 2
            continue
        if two in {"\\/", "||"}:
            tokens.append(("or", two))
            index += 2
            continue
        if two in {"/\\", "&&"}:
            tokens.append(("and", two))
            index += 2
            continue
        if char in NOT_TOKENS:
            tokens.append(("not", char))
            index += 1
            continue
        if char in AND_TOKENS:
            tokens.append(("and", char))
            index += 1
            continue
        if char in OR_TOKENS:
            tokens.append(("or", char))
            index += 1
            continue
        if char in IMP_TOKENS:
            tokens.append(("imp", char))
            index += 1
            continue
        if char == "(":
            tokens.append(("lparen", char))
            index += 1
            continue
        if char == ")":
            tokens.append(("rparen", char))
            index += 1
            continue
        if char.isalpha():
            if index + 1 < len(text) and text[index + 1].isalpha():
                raise ParseError
            tokens.append(("var", char))
            index += 1
            continue
        raise ParseError
    return tokens


class Parser:
    """Приоритет: ¬ > ∧ > ∨ > →; бинарные связки левоассоциативны."""

    def __init__(self, tokens: list[tuple[str, str]]):
        self.tokens = tokens
        self.pos = 0

    def peek(self) -> tuple[str, str] | None:
        if self.pos < len(self.tokens):
            return self.tokens[self.pos]
        return None

    def eat(self, kind: str | None = None) -> tuple[str, str]:
        token = self.peek()
        if token is None or (kind is not None and token[0] != kind):
            raise ParseError
        self.pos += 1
        return token

    def parse(self) -> Formula:
        if not self.tokens:
            raise ParseError
        formula = self.parse_imp()
        if self.peek() is not None:
            raise ParseError
        return formula

    def parse_imp(self) -> Formula:
        left = self.parse_or()
        while self.peek() is not None and self.peek()[0] == "imp":
            self.eat("imp")
            right = self.parse_or()
            left = Imp(left, right)
        return left

    def parse_or(self) -> Formula:
        left = self.parse_and()
        while self.peek() is not None and self.peek()[0] == "or":
            self.eat("or")
            right = self.parse_and()
            left = Or(left, right)
        return left

    def parse_and(self) -> Formula:
        left = self.parse_not()
        while self.peek() is not None and self.peek()[0] == "and":
            self.eat("and")
            right = self.parse_not()
            left = And(left, right)
        return left

    def parse_not(self) -> Formula:
        if self.peek() is not None and self.peek()[0] == "not":
            self.eat("not")
            return Not(self.parse_not())
        return self.parse_atom()

    def parse_atom(self) -> Formula:
        token = self.peek()
        if token is None:
            raise ParseError
        if token[0] == "var":
            self.eat("var")
            return Var(token[1])
        if token[0] == "lparen":
            self.eat("lparen")
            formula = self.parse_imp()
            self.eat("rparen")
            return formula
        raise ParseError


def parse(text: str) -> Formula:
    return Parser(tokenize(text)).parse()


# ---------------------------------------------------------------------------
# Значения истинности и логические системы
# ---------------------------------------------------------------------------

ZERO = Fraction(0)
HALF = Fraction(1, 2)
ONE = Fraction(1)

ASSIGN_RE = re.compile(r"^([^\W\d_])=(0|1|1/2|0\.5|½)$", re.UNICODE)


def format_value(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def parse_value(text: str) -> Fraction:
    cleaned = text.strip().replace("½", "1/2")
    if cleaned == "0.5":
        cleaned = "1/2"
    try:
        return Fraction(cleaned)
    except (ValueError, ZeroDivisionError):
        raise ValueError(f"недопустимое значение истинности: {text!r}") from None


@dataclass(frozen=True)
class LogicSystem:
    key: str
    title: str
    values: tuple[Fraction, ...]


CLASSICAL = LogicSystem("cl", "Классическая двузначная логика", (ZERO, ONE))
KLEENE = LogicSystem("k3", "Сильная трёхзначная логика Клини", (ZERO, HALF, ONE))
LUKASIEWICZ = LogicSystem(
    "l3", "Трёхзначная логика Лукасевича", (ZERO, HALF, ONE)
)
SYSTEMS = {system.key: system for system in (CLASSICAL, KLEENE, LUKASIEWICZ)}


def evaluate(
    formula: Formula, assignment: dict[str, Fraction], system: LogicSystem
) -> Fraction:
    """Значение формулы при данной оценке переменных в данной системе."""
    if isinstance(formula, Var):
        try:
            return assignment[formula.name]
        except KeyError:
            raise EvaluationError(
                f"не задано значение переменной {formula.name}"
            ) from None
    if isinstance(formula, Not):
        return ONE - evaluate(formula.child, assignment, system)
    if isinstance(formula, And):
        return min(
            evaluate(formula.left, assignment, system),
            evaluate(formula.right, assignment, system),
        )
    if isinstance(formula, Or):
        return max(
            evaluate(formula.left, assignment, system),
            evaluate(formula.right, assignment, system),
        )
    left = evaluate(formula.left, assignment, system)
    right = evaluate(formula.right, assignment, system)
    if system.key == "l3":
        return min(ONE, ONE - left + right)
    return max(ONE - left, right)


def collect_vars(formula: Formula) -> list[str]:
    """Различные переменные формулы в порядке первого появления."""
    found: list[str] = []

    def walk(node: Formula) -> None:
        if isinstance(node, Var):
            if node.name not in found:
                found.append(node.name)
            return
        if isinstance(node, Not):
            walk(node.child)
            return
        walk(node.left)
        walk(node.right)

    walk(formula)
    return found


def collect_vars_many(formulas: list[Formula]) -> list[str]:
    found: list[str] = []
    for formula in formulas:
        for name in collect_vars(formula):
            if name not in found:
                found.append(name)
    return found


def format_assignment(assignment: dict[str, Fraction]) -> str:
    return ", ".join(
        f"{name}={format_value(value)}" for name, value in assignment.items()
    )


# ---------------------------------------------------------------------------
# Анализ одной формулы
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Analysis:
    formula: Formula
    system: LogicSystem
    variables: tuple[str, ...]
    rows: tuple[tuple[tuple[Fraction, ...], Fraction], ...]

    @property
    def values(self) -> tuple[Fraction, ...]:
        return tuple(value for _, value in self.rows)

    @property
    def is_valid(self) -> bool:
        """Общезначима: во всех интерпретациях значение 1."""
        return all(value == ONE for value in self.values)

    @property
    def is_satisfiable(self) -> bool:
        """Выполнима: существует интерпретация со значением 1."""
        return any(value == ONE for value in self.values)

    @property
    def is_identically_false(self) -> bool:
        """Тождественно ложна: во всех интерпретациях значение 0."""
        return all(value == ZERO for value in self.values)

    @property
    def counterexamples(self) -> tuple[tuple[dict[str, Fraction], Fraction], ...]:
        """Интерпретации, где значение не равно 1 (контрпримеры к общезначимости)."""
        return tuple(
            (dict(zip(self.variables, combo)), value)
            for combo, value in self.rows
            if value != ONE
        )

    @property
    def classification(self) -> str:
        if self.is_valid:
            return "общезначима (тавтология)"
        if not self.is_satisfiable:
            if self.is_identically_false:
                return "невыполнима и тождественно ложна (все значения 0)"
            other = ", ".join(
                format_value(value) for value in sorted(set(self.values) - {ONE})
            )
            return (
                "невыполнима (нет значения 1), но не тождественно ложна "
                f"(принимает значения: {other})"
            )
        return "выполнима, но не общезначима (есть контрпримеры)"


def analyze(formula: Formula, system: LogicSystem) -> Analysis:
    variables = tuple(sorted(collect_vars(formula)))
    rows = []
    for combo in product(system.values, repeat=len(variables)):
        assignment = dict(zip(variables, combo))
        rows.append((combo, evaluate(formula, assignment, system)))
    return Analysis(formula, system, variables, tuple(rows))


# ---------------------------------------------------------------------------
# Логическое следование
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ConsequenceRow:
    assignment: dict[str, Fraction]
    premise_values: tuple[Fraction, ...]
    conclusion_value: Fraction


@dataclass(frozen=True)
class ConsequenceResult:
    premises: tuple[Formula, ...]
    conclusion: Formula
    system: LogicSystem
    variables: tuple[str, ...]
    satisfying_rows: tuple[ConsequenceRow, ...]
    counterexamples: tuple[ConsequenceRow, ...]

    @property
    def status(self) -> str:
        if not self.satisfying_rows:
            return "inconsistent"
        if self.counterexamples:
            return "not_entailed"
        return "entailed"

    @property
    def verdict(self) -> str:
        if self.status == "entailed":
            return "следует"
        if self.status == "not_entailed":
            return "не следует"
        return "посылки несовместны (следует вакуумно)"


def check_consequence(
    premises: list[Formula], conclusion: Formula, system: LogicSystem
) -> ConsequenceResult:
    """Семантическая проверка A1, ..., An |= B.

    Контрпример — интерпретация, где все посылки равны 1, а заключение не равно 1.
    """
    variables = tuple(sorted(collect_vars_many([*premises, conclusion])))
    satisfying: list[ConsequenceRow] = []
    counterexamples: list[ConsequenceRow] = []
    for combo in product(system.values, repeat=len(variables)):
        assignment = dict(zip(variables, combo))
        premise_values = tuple(
            evaluate(premise, assignment, system) for premise in premises
        )
        if all(value == ONE for value in premise_values):
            conclusion_value = evaluate(conclusion, assignment, system)
            row = ConsequenceRow(assignment, premise_values, conclusion_value)
            satisfying.append(row)
            if conclusion_value != ONE:
                counterexamples.append(row)
    return ConsequenceResult(
        tuple(premises),
        conclusion,
        system,
        variables,
        tuple(satisfying),
        tuple(counterexamples),
    )


# ---------------------------------------------------------------------------
# Сравнение систем
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ValueDifference:
    assignment: dict[str, Fraction]
    left_key: str
    left_value: Fraction
    right_key: str
    right_value: Fraction


@dataclass(frozen=True)
class Comparison:
    formula: Formula
    analyses: dict[str, Analysis]
    k3_vs_l3: tuple[ValueDifference, ...]
    cl_vs_k3: tuple[ValueDifference, ...]
    cl_vs_l3: tuple[ValueDifference, ...]

    @property
    def properties(self) -> dict[str, tuple[bool, bool, bool]]:
        return {
            key: (
                analysis.is_valid,
                analysis.is_satisfiable,
                analysis.is_identically_false,
            )
            for key, analysis in self.analyses.items()
        }

    @property
    def properties_match(self) -> bool:
        return len(set(self.properties.values())) == 1


def compare_systems(formula: Formula) -> Comparison:
    """Сравнить значения и свойства формулы в cl, K3 и L3.

    K3 и L3 сравниваются на всех трёхзначных интерпретациях, а классическая
    логика — с ними на булевых интерпретациях (0/1), где она определена.
    """
    analyses = {key: analyze(formula, system) for key, system in SYSTEMS.items()}

    k3_vs_l3: list[ValueDifference] = []
    for (combo_k3, value_k3), (_, value_l3) in zip(
        analyses["k3"].rows, analyses["l3"].rows
    ):
        if value_k3 != value_l3:
            assignment = dict(zip(analyses["k3"].variables, combo_k3))
            k3_vs_l3.append(
                ValueDifference(assignment, "k3", value_k3, "l3", value_l3)
            )

    def versus_classical(other_key: str) -> tuple[ValueDifference, ...]:
        differences: list[ValueDifference] = []
        other = analyses[other_key]
        for combo, value in other.rows:
            if not all(item in (ZERO, ONE) for item in combo):
                continue
            assignment = dict(zip(other.variables, combo))
            classical_value = evaluate(formula, assignment, CLASSICAL)
            if classical_value != value:
                differences.append(
                    ValueDifference(
                        assignment, "cl", classical_value, other_key, value
                    )
                )
        return tuple(differences)

    return Comparison(
        formula,
        analyses,
        tuple(k3_vs_l3),
        versus_classical("k3"),
        versus_classical("l3"),
    )


# ---------------------------------------------------------------------------
# Вариант 3
# ---------------------------------------------------------------------------

VARIANT = 3

TASK1 = [
    ("F1", "p ∨ ¬p"),
    ("F2", "(p → q) → (¬q → ¬p)"),
    ("F3", "¬(p ∨ ¬p)"),
    ("F4", "(p ∧ q) ∨ (¬p ∧ r)"),
    ("F5", "((p → q) ∧ (p → ¬q)) → ¬p"),
]

TASK2 = [
    ("R1", ["p ∨ q", "p → r", "q → s", "(r ∨ s) → t", "t → u"], "u"),
    ("R2", ["p → q", "q → (r ∨ s)", "r → t", "s → t", "t → u"], "¬p ∨ u"),
    (
        "R3",
        ["p ∨ q", "p → s", "r → s", "s → t", "t → u"],
        "u ∧ ((p → q) ∨ (q → p))",
    ),
    ("R4", ["p ∨ q", "p → r", "q → s", "r → t", "s → t"], "p → q"),
]


# ---------------------------------------------------------------------------
# Отчёт в Markdown
# ---------------------------------------------------------------------------


def yes_no(flag: bool) -> str:
    return "да" if flag else "нет"


def markdown_table(headers: list[str], rows: list[list[str]]) -> str:
    lines = [
        "| " + " | ".join(headers) + " |",
        "| " + " | ".join("---" for _ in headers) + " |",
    ]
    for row in rows:
        lines.append("| " + " | ".join(row) + " |")
    return "\n".join(lines)


def truth_table_markdown(analysis: Analysis) -> str:
    headers = [*analysis.variables, show(analysis.formula)]
    rows = [
        [*(format_value(value) for value in combo), format_value(result)]
        for combo, result in analysis.rows
    ]
    return markdown_table(headers, rows)


def properties_table_markdown(analyses: dict[str, Analysis]) -> str:
    headers = [
        "Система",
        "Общезначима",
        "Выполнима",
        "Тождественно ложна",
        "Контрпримеров",
        "Статус",
    ]
    rows = []
    for key in SYSTEMS:
        analysis = analyses[key]
        rows.append(
            [
                key,
                yes_no(analysis.is_valid),
                yes_no(analysis.is_satisfiable),
                yes_no(analysis.is_identically_false),
                str(len(analysis.counterexamples)),
                analysis.classification,
            ]
        )
    return markdown_table(headers, rows)


def describe_differences(
    differences: tuple[ValueDifference, ...],
    left: str,
    right: str,
    scope: str,
    total: int,
) -> str:
    if not differences:
        return f"- {left} и {right}: значения совпадают во всех {total} {scope}."
    first = differences[0]
    return (
        f"- {left} и {right}: расхождения в {len(differences)} из {total} "
        f"{scope}; например, при {format_assignment(first.assignment)}: "
        f"{left} = {format_value(first.left_value)}, "
        f"{right} = {format_value(first.right_value)}."
    )


def comparison_lines(comparison: Comparison) -> list[str]:
    k3_total = len(comparison.analyses["k3"].rows)
    boolean_total = sum(
        1
        for combo, _ in comparison.analyses["k3"].rows
        if all(value in (ZERO, ONE) for value in combo)
    )
    lines = [
        describe_differences(
            comparison.k3_vs_l3,
            "K3",
            "L3",
            "трёхзначных интерпретациях",
            k3_total,
        ),
        describe_differences(
            comparison.cl_vs_k3,
            "cl",
            "K3",
            "булевых интерпретациях (0/1)",
            boolean_total,
        ),
        describe_differences(
            comparison.cl_vs_l3,
            "cl",
            "L3",
            "булевых интерпретациях (0/1)",
            boolean_total,
        ),
    ]
    if comparison.properties_match:
        lines.append(
            "- Семантические свойства (общезначимость, выполнимость, "
            "тождественная ложность) во всех системах совпадают."
        )
    else:
        lines.append("- Семантические свойства различаются:")
        for key in SYSTEMS:
            analysis = comparison.analyses[key]
            lines.append(
                f"  - {key}: общезначима — {yes_no(analysis.is_valid)}, "
                f"выполнима — {yes_no(analysis.is_satisfiable)}, "
                f"тождественно ложна — {yes_no(analysis.is_identically_false)}."
            )
    return lines


def consequence_example(row: ConsequenceRow) -> str:
    return (
        f"{format_assignment(row.assignment)}; "
        f"заключение = {format_value(row.conclusion_value)}"
    )


def build_report() -> str:
    lines: list[str] = []

    def add(text: str = "") -> None:
        lines.append(text)

    add("# Лабораторная работа №2")
    add()
    add(
        "**Тема:** интерпретатор многозначных логик и проверка "
        "семантических свойств формул."
    )
    add()
    add(f"**Вариант:** {VARIANT}.")
    add()
    add("**Пояснение задачи и теория:** [theory.md](theory.md).")
    add()
    add("## Логические системы и семантика")
    add()
    add(markdown_table(
        ["Система", "Обозначение", "Значения истинности"],
        [
            ["Классическая двузначная логика", "cl", "0, 1"],
            ["Сильная трёхзначная логика Клини", "k3", "0, 1/2, 1"],
            ["Трёхзначная логика Лукасевича", "l3", "0, 1/2, 1"],
        ],
    ))
    add()
    add(markdown_table(
        ["Связка", "Правило вычисления"],
        [
            ["¬a", "1 − a"],
            ["a ∧ b", "min(a, b)"],
            ["a ∨ b", "max(a, b)"],
            ["a →K3 b", "max(1 − a, b)"],
            ["a →L3 b", "min(1, 1 − a + b)"],
        ],
    ))
    add()
    add("**Соглашения:**")
    add()
    add("- **общезначима** — значение 1 при всех интерпретациях;")
    add("- **выполнима** — существует интерпретация со значением 1;")
    add(
        "- **невыполнима** — нет ни одной интерпретации со значением 1; "
        "это не то же самое, что тождественная ложность;"
    )
    add("- **тождественно ложна** — значение 0 при всех интерпретациях;")
    add(
        "- для логического следования контрпример — интерпретация, в которой "
        "все посылки равны 1, а заключение не равно 1."
    )
    add()

    example = parse("p → q")
    add("**Пример из задания.** Для формулы p → q при p = q = 1/2:")
    add()
    add(
        markdown_table(
            ["Система", "Значение"],
            [
                [
                    "K3",
                    format_value(
                        evaluate(example, {"p": HALF, "q": HALF}, KLEENE)
                    ),
                ],
                [
                    "L3",
                    format_value(
                        evaluate(example, {"p": HALF, "q": HALF}, LUKASIEWICZ)
                    ),
                ],
            ],
        )
    )
    add()

    add("## Задание 1. Исследование логических формул")
    add()
    for name, text in TASK1:
        formula = parse(text)
        analyses = {key: analyze(formula, SYSTEMS[key]) for key in SYSTEMS}
        comparison = compare_systems(formula)
        add(f"### {name} = {show(formula)}")
        add()
        add("**Таблицы истинности.**")
        add()
        for key in SYSTEMS:
            add(f"#### {SYSTEMS[key].title} ({key})")
            add()
            add(truth_table_markdown(analyses[key]))
            add()
        add("**Свойства формулы.**")
        add()
        add(properties_table_markdown(analyses))
        add()
        add("**Примеры контрпримеров (значение не равно 1):**")
        add()
        for key in SYSTEMS:
            analysis = analyses[key]
            if not analysis.counterexamples:
                add(f"- {key}: контрпримеров нет (формула общезначима).")
                continue
            first_by_value: dict[Fraction, dict[str, Fraction]] = {}
            for assignment, value in analysis.counterexamples:
                first_by_value.setdefault(value, assignment)
            parts = [
                f"{format_assignment(first_by_value[value])} → "
                f"{format_value(value)}"
                for value in sorted(first_by_value)
            ]
            add(f"- {key}: " + "; ".join(parts) + ".")
        add()
        add("**Сравнение систем.**")
        add()
        lines.extend(comparison_lines(comparison))
        add()

    add("## Задание 2. Проверка логического следования")
    add()
    for name, premise_texts, conclusion_text in TASK2:
        premises = [parse(text) for text in premise_texts]
        conclusion = parse(conclusion_text)
        add(f"### {name}")
        add()
        add("Посылки:")
        add()
        for premise in premises:
            add(f"- {show(premise)}")
        add()
        add(f"Заключение: **{show(conclusion)}**")
        add()
        rows = []
        for key in SYSTEMS:
            result = check_consequence(premises, conclusion, SYSTEMS[key])
            example = (
                consequence_example(result.counterexamples[0])
                if result.counterexamples
                else "—"
            )
            rows.append(
                [
                    key,
                    str(len(result.satisfying_rows)),
                    result.verdict,
                    str(len(result.counterexamples)),
                    example,
                ]
            )
        add(markdown_table(
            [
                "Система",
                "Интерпретаций, где все посылки = 1",
                "Следует",
                "Контрпримеров",
                "Пример контрпримера",
            ],
            rows,
        ))
        add()

    add("## Выводы")
    add()
    add("**Задание 1.**")
    add()
    for name, text in TASK1:
        formula = parse(text)
        parts = []
        for key in SYSTEMS:
            analysis = analyze(formula, SYSTEMS[key])
            parts.append(f"{key} — {analysis.classification}")
        add(f"- {name}: " + "; ".join(parts) + ".")
    add()
    add("**Задание 2.**")
    add()
    for name, premise_texts, conclusion_text in TASK2:
        premises = [parse(text) for text in premise_texts]
        conclusion = parse(conclusion_text)
        parts = []
        for key in SYSTEMS:
            result = check_consequence(premises, conclusion, SYSTEMS[key])
            parts.append(f"{key} — {result.verdict}")
        add(f"- {name}: " + "; ".join(parts) + ".")
    add()

    notes: list[str] = []
    for name, text in TASK1:
        formula = parse(text)
        for key in SYSTEMS:
            analysis = analyze(formula, SYSTEMS[key])
            if not analysis.is_satisfiable and not analysis.is_identically_false:
                example = next(
                    (
                        (assignment, value)
                        for assignment, value in analysis.counterexamples
                        if value != ZERO
                    ),
                    None,
                )
                detail = (
                    f"; например, {format_assignment(example[0])} → "
                    f"{format_value(example[1])}"
                    if example
                    else ""
                )
                notes.append(
                    f"- {name} в {key}: нет интерпретаций со значением 1, "
                    "то есть формула невыполнима, но не тождественно ложна"
                    f"{detail}."
                )
    if notes:
        add("**Замечания.**")
        add()
        lines.extend(notes)
        add()

    add("## Как воспроизвести")
    add()
    add("```text")
    add("cd lab_2")
    add("python multivalued.py            # интерактивный режим")
    add("python multivalued.py demo       # примеры варианта 3")
    add("python multivalued.py --report   # пересоздать этот отчёт")
    add("```")
    add()
    return "\n".join(lines) + "\n"


def default_report_path() -> str:
    return str(Path(__file__).resolve().with_name("report.md"))


def write_report(path: str | None = None) -> None:
    target = Path(path or default_report_path())
    target.write_text(build_report(), encoding="utf-8")
    print(f"Отчёт сохранён: {target.resolve()}")


# ---------------------------------------------------------------------------
# Консольный интерфейс
# ---------------------------------------------------------------------------

BANNER = """\
Интерпретатор многозначных логик. Лабораторная работа №2, вариант 3.
Системы: cl — классическая, k3 — Клини, l3 — Лукасевича.
Связки: ¬ (~, !), ∧ (&, ^, /\\), ∨ (|, \\/), → (->, =>, >, ⊃).
Приоритет: ¬ > ∧ > ∨ > →; бинарные связки левоассоциативны.
"""

HELP = """\
Команды:
  table [cl|k3|l3|all] <формула>
        таблица истинности и семантические свойства;
  eval <cl|k3|l3|all> <формула> p=1 q=1/2 ...
        значение при заданной оценке переменных;
  follow <cl|k3|l3|all> <посылки через запятую> |= <заключение>
        проверка логического следования;
  compare <формула>
        таблицы в трёх системах и их сравнение;
  demo  — примеры варианта 3;
  report [файл] — сохранить отчёт (по умолчанию report.md рядом с программой);
  help, exit.
Если ввести просто формулу, будет выполнено сравнение систем.
"""

SYSTEM_KEYS = {"cl", "k3", "l3", "all"}


def print_help() -> None:
    print(BANNER)
    print(HELP)


def format_cli_table(analysis: Analysis) -> str:
    headers = [*analysis.variables, show(analysis.formula)]
    rows = [
        [*(format_value(value) for value in combo), format_value(result)]
        for combo, result in analysis.rows
    ]
    widths = [
        max([len(header), *(len(row[index]) for row in rows)])
        for index, header in enumerate(headers)
    ]
    lines = ["  ".join(header.ljust(widths[index]) for index, header in enumerate(headers))]
    lines.append("  ".join("-" * width for width in widths))
    for row in rows:
        lines.append(
            "  ".join(
                row[index].ljust(widths[index]) for index in range(len(headers))
            )
        )
    return "\n".join(lines)


def print_analysis(analysis: Analysis, limit: int = 3) -> None:
    print(format_cli_table(analysis))
    print(f"Статус: {analysis.classification}")
    print(
        "Общезначима: "
        f"{yes_no(analysis.is_valid)}; выполнима: {yes_no(analysis.is_satisfiable)}; "
        f"тождественно ложна: {yes_no(analysis.is_identically_false)}."
    )
    print(f"Контрпримеров (значение ≠ 1): {len(analysis.counterexamples)}")
    for assignment, value in analysis.counterexamples[:limit]:
        print(f"  {format_assignment(assignment)} → {format_value(value)}")
    if len(analysis.counterexamples) > limit:
        print(f"  ... ещё {len(analysis.counterexamples) - limit}")


def systems_for(spec: str) -> list[str]:
    if spec not in SYSTEM_KEYS:
        raise ValueError("система должна быть одной из: cl, k3, l3, all")
    if spec == "all":
        return list(SYSTEMS)
    return [spec]


def split_system(rest: str) -> tuple[str, str]:
    parts = rest.split(None, 1)
    if not parts:
        raise ValueError("не указана формула")
    first = parts[0].lower()
    if first in SYSTEM_KEYS:
        if len(parts) == 1:
            raise ValueError("не указана формула")
        return first, parts[1]
    return "all", rest


def cmd_table(rest: str) -> None:
    spec, text = split_system(rest)
    formula = parse(text)
    for key in systems_for(spec):
        analysis = analyze(formula, SYSTEMS[key])
        print(f"\n{SYSTEMS[key].title} ({key})")
        print_analysis(analysis)


def cmd_eval(rest: str) -> None:
    parts = rest.split()
    if not parts:
        raise ValueError("укажите систему, формулу и оценки переменных")
    spec = parts[0].lower()
    assignments: dict[str, Fraction] = {}
    formula_tokens: list[str] = []
    for token in parts[1:]:
        token = token.strip(",")
        if not token:
            continue
        match = ASSIGN_RE.match(token)
        if match:
            assignments[match.group(1)] = parse_value(match.group(2))
        else:
            formula_tokens.append(token)
    formula_text = " ".join(formula_tokens)
    if not formula_text:
        raise ValueError("не указана формула")
    if not assignments:
        raise ValueError("не указана ни одна оценка вида p=1, q=1/2")
    formula = parse(formula_text)
    variables = collect_vars(formula)
    missing = [name for name in variables if name not in assignments]
    if missing:
        raise ValueError(
            "не заданы значения переменных: " + ", ".join(missing)
        )
    extra = [name for name in assignments if name not in variables]
    if extra:
        print("Примечание: лишние оценки игнорируются: " + ", ".join(extra))
    for key in systems_for(spec):
        system = SYSTEMS[key]
        bad = [
            f"{name}={format_value(value)}"
            for name, value in assignments.items()
            if value not in system.values
        ]
        if bad:
            print(
                f"{key}: пропущено — значения {', '.join(bad)} "
                "недопустимы в этой системе."
            )
            continue
        value = evaluate(formula, assignments, system)
        print(
            f"{key}: {show(formula)} = {format_value(value)} "
            f"при {format_assignment(assignments)}"
        )


def cmd_follow(rest: str) -> None:
    if "|=" not in rest:
        raise ValueError("разделите посылки и заключение символом |=")
    left, conclusion_text = rest.split("|=", 1)
    parts = left.split()
    if not parts:
        raise ValueError("не указана система")
    spec = parts[0].lower()
    if spec not in SYSTEM_KEYS:
        raise ValueError("первым укажите систему: cl, k3, l3 или all")
    premise_text = " ".join(parts[1:])
    premise_texts = [
        item.strip() for item in re.split(r"[,;]", premise_text) if item.strip()
    ]
    if not premise_texts:
        raise ValueError("не указаны посылки")
    if not conclusion_text.strip():
        raise ValueError("не указано заключение")
    premises = [parse(item) for item in premise_texts]
    conclusion = parse(conclusion_text)
    for key in systems_for(spec):
        result = check_consequence(premises, conclusion, SYSTEMS[key])
        print(f"\n{SYSTEMS[key].title} ({key}): {result.verdict}")
        print(
            "Интерпретаций, где все посылки = 1: "
            f"{len(result.satisfying_rows)}"
        )
        print(f"Контрпримеров: {len(result.counterexamples)}")
        for row in result.counterexamples[:3]:
            print(f"  {consequence_example(row)}")
        if len(result.counterexamples) > 3:
            print(f"  ... ещё {len(result.counterexamples) - 3}")


def cmd_compare(rest: str) -> None:
    formula = parse(rest)
    comparison = compare_systems(formula)
    for key in SYSTEMS:
        analysis = comparison.analyses[key]
        print(f"\n{SYSTEMS[key].title} ({key})")
        print_analysis(analysis)
    print("\nСравнение систем:")
    for line in comparison_lines(comparison):
        print(line)


def run_demo() -> None:
    print("=== Задание 1. Исследование формул (вариант 3) ===")
    for name, text in TASK1:
        formula = parse(text)
        print(f"\n{name} = {show(formula)}")
        for key in SYSTEMS:
            analysis = analyze(formula, SYSTEMS[key])
            print(
                f"  {key}: {analysis.classification}; "
                f"контрпримеров: {len(analysis.counterexamples)}"
            )
        comparison = compare_systems(formula)
        for line in comparison_lines(comparison):
            print("  " + line)

    print("\n=== Задание 2. Логическое следование (вариант 3) ===")
    for name, premise_texts, conclusion_text in TASK2:
        premises = [parse(text) for text in premise_texts]
        conclusion = parse(conclusion_text)
        print(f"\n{name}:")
        for premise in premises:
            print(f"  посылка: {show(premise)}")
        print(f"  заключение: {show(conclusion)}")
        for key in SYSTEMS:
            result = check_consequence(premises, conclusion, SYSTEMS[key])
            print(
                f"  {key}: {result.verdict}; "
                f"интерпретаций с посылками = 1: {len(result.satisfying_rows)}; "
                f"контрпримеров: {len(result.counterexamples)}"
            )
            if result.counterexamples:
                print(f"    пример: {consequence_example(result.counterexamples[0])}")


def configure_stdio() -> None:
    for stream in (sys.stdin, sys.stdout, sys.stderr):
        reconfigure = getattr(stream, "reconfigure", None)
        if reconfigure is None:
            continue
        try:
            reconfigure(encoding="utf-8")
        except Exception:
            pass


def interactive() -> None:
    print_help()
    while True:
        try:
            line = input("\n> ")
        except EOFError:
            print()
            break
        text = line.strip()
        if not text:
            continue
        command, _, rest = text.partition(" ")
        command = command.lower()
        try:
            if command in {"exit", "quit", "выход"}:
                break
            if command in {"help", "?", "помощь"}:
                print_help()
            elif command == "table":
                cmd_table(rest)
            elif command == "eval":
                cmd_eval(rest)
            elif command == "follow":
                cmd_follow(rest)
            elif command == "compare":
                cmd_compare(rest)
            elif command == "demo":
                run_demo()
            elif command == "report":
                write_report(rest.strip() or None)
            else:
                cmd_compare(text)
        except ParseError:
            print("Ошибка: строка не является правильно построенной формулой.")
        except (ValueError, EvaluationError) as error:
            print(f"Ошибка: {error}")


def main() -> None:
    configure_stdio()
    args = sys.argv[1:]
    if args:
        if args[0] in {"-h", "--help"}:
            print_help()
            return
        if args[0] == "--report":
            write_report(args[1] if len(args) > 1 else None)
            return
        if args[0] == "demo":
            run_demo()
            return
        print(f"Неизвестный аргумент: {args[0]}")
        print("Использование: python multivalued.py [--report [файл]] [demo]")
        return
    interactive()


if __name__ == "__main__":
    main()
