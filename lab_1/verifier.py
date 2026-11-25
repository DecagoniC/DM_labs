"""Верификатор доказательств для лабораторной работы №1, вариант 3.

Программа не проверяет истинность формулы. Она принимает строку, если та
является правильно построенной формулой и получается за один шаг из аксиом,
определения или уже принятых формул.

Связки: ¬, ∨, ⊃. Импликация левоассоциативна и слабее дизъюнкции:
p⊃q⊃r читается как (p⊃q)⊃r, а p∨q⊃r — как (p∨q)⊃r.
"""

from __future__ import annotations

import sys
from dataclasses import dataclass


class ParseError(Exception):
    """Строка не является правильно построенной формулой."""


@dataclass(frozen=True)
class Var:
    name: str


@dataclass(frozen=True)
class Not:
    child: "Formula"


@dataclass(frozen=True)
class Or:
    left: "Formula"
    right: "Formula"


@dataclass(frozen=True)
class Imp:
    left: "Formula"
    right: "Formula"


Formula = Var | Not | Or | Imp

NOT_TOKENS = {"¬", "~", "!"}
OR_TOKENS = {"∨", "|", "\\/"}
IMP_TOKENS = {"⊃", "→", "->", "=>", ">"}


def show(formula: Formula) -> str:
    if isinstance(formula, Var):
        return formula.name
    if isinstance(formula, Not):
        return "¬" + show(formula.child)
    symbol = "∨" if isinstance(formula, Or) else "⊃"
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
        if two in {"->", "=>", "\\/"}:
            kind = "imp" if two in {"->", "=>"} else "or"
            tokens.append((kind, two))
            index += 2
            continue
        if char in NOT_TOKENS:
            tokens.append(("not", char))
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
        left = self.parse_not()
        while self.peek() is not None and self.peek()[0] == "or":
            self.eat("or")
            right = self.parse_not()
            left = Or(left, right)
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


AXIOM_TEXTS = [
    "p⊃p∨q",
    "p∨p⊃p",
    "p∨(q∨r)⊃q∨(p∨r)",
    "(q⊃s)⊃(p∨q⊃p∨s)",
    "¬¬p⊃p",
    "(¬q⊃¬p)⊃(p⊃q)",
]


def collect_vars(formula: Formula, found: list[str]) -> None:
    if isinstance(formula, Var):
        if formula.name not in found:
            found.append(formula.name)
        return
    if isinstance(formula, Not):
        collect_vars(formula.child, found)
        return
    collect_vars(formula.left, found)
    collect_vars(formula.right, found)


def substitute(formula: Formula, variable: str, replacement: Formula) -> Formula:
    if isinstance(formula, Var):
        if formula.name == variable:
            return replacement
        return formula
    if isinstance(formula, Not):
        return Not(substitute(formula.child, variable, replacement))
    if isinstance(formula, Or):
        return Or(
            substitute(formula.left, variable, replacement),
            substitute(formula.right, variable, replacement),
        )
    return Imp(
        substitute(formula.left, variable, replacement),
        substitute(formula.right, variable, replacement),
    )


def match_substitution(
    source: Formula, target: Formula, variable: str, box: dict[str, Formula]
) -> bool:
    """Проверяет, что target получается заменой всех вхождений variable в source."""
    if isinstance(source, Var) and source.name == variable:
        previous = box.get("value")
        if previous is None:
            box["value"] = target
            return True
        return previous == target
    if type(source) is not type(target):
        return False
    if isinstance(source, Var) and isinstance(target, Var):
        return source.name == target.name
    if isinstance(source, Not) and isinstance(target, Not):
        return match_substitution(source.child, target.child, variable, box)
    if isinstance(source, (Or, Imp)) and isinstance(target, (Or, Imp)):
        return match_substitution(
            source.left, target.left, variable, box
        ) and match_substitution(source.right, target.right, variable, box)
    return False


def find_beta(source: Formula, target: Formula) -> tuple[str, Formula] | None:
    """Одна подстановка одной переменной. Одновременные подстановки не подходят."""
    if source == target:
        return None
    names: list[str] = []
    collect_vars(source, names)
    for name in names:
        box: dict[str, Formula] = {}
        if not match_substitution(source, target, name, box):
            continue
        replacement = box.get("value")
        if replacement is None or replacement == Var(name):
            continue
        if substitute(source, name, replacement) == target:
            return name, replacement
    return None


def or_side(inner: Formula) -> Formula:
    return Or(Not(inner), inner)


def imp_side(inner: Formula) -> Formula:
    return Imp(Imp(Not(inner), inner), inner)


def match_or_side(formula: Formula) -> Formula | None:
    if (
        isinstance(formula, Or)
        and isinstance(formula.left, Not)
        and formula.right == formula.left.child
    ):
        return formula.left.child
    return None


def match_imp_side(formula: Formula) -> Formula | None:
    if not isinstance(formula, Imp) or not isinstance(formula.left, Imp):
        return None
    nested = formula.left
    if not isinstance(nested.left, Not):
        return None
    inner = nested.left.child
    if nested.right == inner and formula.right == inner:
        return inner
    return None


def definition_steps(formula: Formula) -> list[tuple[Formula, Formula, bool]]:
    """Одна замена подформулы по определению ¬X∨X = (¬X⊃X)⊃X.

    Третий элемент истинен, если ¬X∨X заменено на (¬X⊃X)⊃X.
    """
    steps: list[tuple[Formula, Formula, bool]] = []
    left_match = match_or_side(formula)
    if left_match is not None:
        steps.append((imp_side(left_match), left_match, True))
    right_match = match_imp_side(formula)
    if right_match is not None:
        steps.append((or_side(right_match), right_match, False))
    if isinstance(formula, Not):
        for child, inner, forward in definition_steps(formula.child):
            steps.append((Not(child), inner, forward))
    elif isinstance(formula, (Or, Imp)):
        kind = type(formula)
        for left, inner, forward in definition_steps(formula.left):
            steps.append((kind(left, formula.right), inner, forward))
        for right, inner, forward in definition_steps(formula.right):
            steps.append((kind(formula.left, right), inner, forward))
    return steps


def justify(formula: Formula, axioms: list[Formula], derived: list[Formula]) -> str | None:
    shown = show(formula)
    for number, axiom in enumerate(axioms, 1):
        if formula == axiom:
            return f"Формула {shown} является аксиомой {number}"

    sources = [*axioms, *derived]
    for source in sources:
        beta = find_beta(source, formula)
        if beta is None:
            continue
        variable, replacement = beta
        return (
            f"Формула {shown} выводима из формулы {show(source)} "
            f"по правилу бета с подстановкой формулы {show(replacement)} "
            f"вместо переменной {variable}"
        )

    for source in sources:
        if isinstance(source, Imp) and source.right == formula and source.left in sources:
            return (
                f"Формула {shown} выводима из формул {show(source)} и "
                f"{show(source.left)} по правилу modus ponens"
            )

    for source in sources:
        for result, inner, forward in definition_steps(source):
            if result != formula:
                continue
            left_side = show(or_side(inner))
            right_side = show(imp_side(inner))
            if forward:
                change = f"{left_side} заменено на {right_side}"
            else:
                change = f"{right_side} заменено на {left_side}"
            return (
                f"Формула {shown} выводима из формулы {show(source)} "
                f"заменой по определению: {change}"
            )
    return None


class Verifier:
    def __init__(self) -> None:
        self.axioms = [parse(text) for text in AXIOM_TEXTS]
        self.derived: list[Formula] = []

    def submit(self, text: str) -> str:
        try:
            formula = parse(text)
        except ParseError:
            return "Ошибка: строка не является правильно построенной формулой."
        if formula in self.derived:
            return f"Формула {show(formula)} уже есть в списке выведенных формул."
        message = justify(formula, self.axioms, self.derived)
        if message is None:
            return (
                f"Формула {show(formula)} не выводима за один шаг из аксиом, "
                "определения и ранее выведенных формул."
            )
        self.derived.append(formula)
        return message


def configure_stdio() -> None:
    for stream in (sys.stdin, sys.stdout, sys.stderr):
        reconfigure = getattr(stream, "reconfigure", None)
        if reconfigure is None:
            continue
        try:
            reconfigure(encoding="utf-8")
        except Exception:
            pass


def print_axioms(verifier: Verifier) -> None:
    for number, axiom in enumerate(verifier.axioms, 1):
        print(f"  {number}) {show(axiom)}")
    print("  Определение: (¬p∨p) = ((¬p⊃p)⊃p)")


def print_derived(verifier: Verifier) -> None:
    if not verifier.derived:
        print("Список выведенных формул пуст.")
        return
    print("Выведенные формулы:")
    for number, formula in enumerate(verifier.derived, 1):
        print(f"  {number}) {show(formula)}")


BANNER = """\
Верификатор доказательств. Вариант 3.
Связки: ¬ (~, !), ∨ (|, \\/), ⊃ (->, =>, >, →).
Импликация левоассоциативна: p⊃q⊃r означает (p⊃q)⊃r.
Команды: list — выведенные формулы, axioms — аксиомы, help — справка, exit — выход.
"""


def main() -> None:
    configure_stdio()
    verifier = Verifier()
    print(BANNER)
    print("Аксиомы:")
    print_axioms(verifier)
    print()
    while True:
        try:
            line = input("> ")
        except EOFError:
            print()
            break
        command = line.strip().lower()
        if command == "":
            print_derived(verifier)
            continue
        if command in {"exit", "quit"}:
            break
        if command == "list":
            print_derived(verifier)
            continue
        if command == "axioms":
            print_axioms(verifier)
            continue
        if command in {"help", "?"}:
            print(BANNER)
            continue
        print(verifier.submit(line))


if __name__ == "__main__":
    main()
