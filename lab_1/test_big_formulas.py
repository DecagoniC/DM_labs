"""Большие формулы для общей проверки верификатора (не из методички).

Здесь проверяются:
  * примеры парсера из методички;
  * большие β-вхождения каждой из шести аксиом варианта 3;
  * большая MP-цепочка: A = (BIG∨BIG)⊃BIG, затем A⊃(A∨q), затем A∨q;
  * замена по определению: одно вхождение за шаг, все сразу — отвергается;
  * обратная замена по определению в большом контексте;
  * одновременная подстановка двух переменных и подстановка не во все
    вхождения переменной — отвергаются;
  * случайные деревья: parse(show(f)) == f;
  * длинные цепочки импликаций и глубокие отрицания;
  * все варианты записи связок.

Запуск: python test_big_formulas.py
"""

import random

from verifier import (
    Imp,
    Not,
    Or,
    Var,
    Verifier,
    definition_steps,
    find_beta,
    parse,
    show,
    substitute,
)

# Подставляемая большая формула; содержит два вхождения ¬X∨X.
BIG_TEXT = "((a⊃b)∨(¬(c∨d)∨(c∨d)))⊃((¬e∨e)⊃(a∨b))"


def v(name: str) -> Var:
    return Var(name)


def big():
    return parse(BIG_TEXT)


def count_or_sides(formula) -> int:
    """Сколько вхождений ¬X∨X содержит формула."""
    count = 0
    if isinstance(formula, Or) and isinstance(formula.left, Not):
        if formula.left.child == formula.right:
            count += 1
    if isinstance(formula, Not):
        return count + count_or_sides(formula.child)
    if isinstance(formula, (Or, Imp)):
        return count + count_or_sides(formula.left) + count_or_sides(formula.right)
    return count


def replace_first_definition(formula):
    """Заменить первое (сверху вниз) вхождение ¬X∨X на (¬X⊃X)⊃X.

    Возвращает (новая_формула, X) или None, если вхождений нет.
    Реализовано независимо от definition_steps, чтобы тест не был тавтологией.
    """
    if isinstance(formula, Or) and isinstance(formula.left, Not):
        inner = formula.left.child
        if inner == formula.right:
            return Imp(Imp(Not(inner), inner), inner), inner
    if isinstance(formula, Not):
        found = replace_first_definition(formula.child)
        return (Not(found[0]), found[1]) if found else None
    if isinstance(formula, (Or, Imp)):
        found = replace_first_definition(formula.left)
        if found:
            return type(formula)(found[0], formula.right), found[1]
        found = replace_first_definition(formula.right)
        if found:
            return type(formula)(formula.left, found[0]), found[1]
    return None


def replace_all_definitions(formula):
    """Заменить сразу ВСЕ вхождения ¬X∨X (заведомо больше одного шага)."""
    if isinstance(formula, Or) and isinstance(formula.left, Not):
        inner = formula.left.child
        if inner == formula.right:
            return Imp(Imp(Not(inner), inner), inner)
    if isinstance(formula, Not):
        return Not(replace_all_definitions(formula.child))
    if isinstance(formula, Or):
        return Or(
            replace_all_definitions(formula.left),
            replace_all_definitions(formula.right),
        )
    if isinstance(formula, Imp):
        return Imp(
            replace_all_definitions(formula.left),
            replace_all_definitions(formula.right),
        )
    return formula


def replace_first_var(formula, name: str, replacement):
    """Заменить только ПЕРВОЕ вхождение переменной (нарушение правила β)."""
    if isinstance(formula, Var):
        if formula.name == name:
            return replacement, True
        return formula, False
    if isinstance(formula, Not):
        child, done = replace_first_var(formula.child, name, replacement)
        return (Not(child), True) if done else (formula, False)
    if isinstance(formula, (Or, Imp)):
        left, done = replace_first_var(formula.left, name, replacement)
        if done:
            return type(formula)(left, formula.right), True
        right, done = replace_first_var(formula.right, name, replacement)
        if done:
            return type(formula)(formula.left, right), True
    return formula, False


def build_mp_session():
    """Сеанс из трёх шагов с большими формулами.

    A = (BIG∨BIG)⊃BIG получается из аксиомы 2 подстановкой p := BIG,
    A⊃(A∨q) — из аксиомы 1 подстановкой p := A,
    A∨q — из этих двух формул по modus ponens.
    """
    big_formula = big()
    a = Imp(Or(big_formula, big_formula), big_formula)
    step2 = Imp(a, Or(a, v("q")))
    step3 = Or(a, v("q"))
    verifier = Verifier()
    first = verifier.submit(show(a))
    second = verifier.submit(show(step2))
    third = verifier.submit(show(step3))
    return verifier, a, step2, step3, first, second, third


def test_methodology_parser_examples() -> None:
    valid = "(((a) → b)) → (f → ((p → (q))))"
    assert parse(valid) == parse("(a⊃b)⊃(f⊃(p⊃q))")

    verifier = Verifier()
    rejected = [
        "p → (p → p))",
        "mn → (p → p)",
        "q → (p p)",
        "→ a → b → c",
        "a → b → c →",
    ]
    for text in rejected:
        assert verifier.submit(text).startswith("Ошибка"), text


def test_methodology_proof_session_is_for_other_variants() -> None:
    """Сеанс p⊃p из методички использует аксиомы K и S (варианты 1–2).

    В варианте 3 таких аксиом нет, поэтому все шаги обязаны отвергаться.
    """
    steps = [
        "(s → (r → q)) → ((s → r) → (s → q))",
        "(p → (r → q)) → ((p → r) → (p → q))",
        "(p → (r → p)) → ((p → r) → (p → p))",
        "(p → (r → p))",
        "p → r → (p → p)",
        "(p → (q → p)) → (p → p)",
        "(p → p)",
    ]
    verifier = Verifier()
    for text in steps:
        assert "не выводима" in verifier.submit(text), text
    assert verifier.derived == []


def test_large_beta_instances_of_all_six_axioms() -> None:
    big_formula = big()
    cases = [
        ("p⊃p∨q", "p"),
        ("p∨p⊃p", "p"),
        ("p∨(q∨r)⊃q∨(p∨r)", "p"),
        ("(q⊃s)⊃(p∨q⊃p∨s)", "q"),
        ("¬¬p⊃p", "p"),
        ("(¬q⊃¬p)⊃(p⊃q)", "p"),
    ]
    for text, variable in cases:
        target = substitute(parse(text), variable, big_formula)
        verifier = Verifier()
        message = verifier.submit(show(target))
        assert "по правилу бета" in message, text
        assert f"вместо переменной {variable}" in message, text
        assert show(big_formula) in message, text
        assert verifier.derived == [target], text


def test_beta_replacement_may_contain_the_same_variable() -> None:
    source = parse("p⊃p∨q")
    replacement = parse("p⊃r")
    target = substitute(source, "p", replacement)
    assert find_beta(source, target) == ("p", replacement)


def test_large_modus_ponens_chain() -> None:
    _, a, step2, step3, first, second, third = build_mp_session()
    assert "по правилу бета" in first
    assert "по правилу бета" in second
    assert third == (
        f"Формула {show(step3)} выводима из формул {show(step2)} и {show(a)} "
        "по правилу modus ponens"
    )


def test_large_definition_one_occurrence_per_step() -> None:
    verifier, _, _, step3, _, _, _ = build_mp_session()
    assert count_or_sides(step3) == 6
    forward = [step for step in definition_steps(step3) if step[2]]
    assert len(forward) == 6

    single, inner = replace_first_definition(step3)
    message = verifier.submit(show(single))
    assert "заменой по определению" in message
    assert f"{show(Or(Not(inner), inner))} заменено на " in message
    assert f"{show(Imp(Imp(Not(inner), inner), inner))}" in message

    all_at_once = replace_all_definitions(step3)
    assert all_at_once != step3
    assert "не выводима" in verifier.submit(show(all_at_once))


def test_large_backward_definition() -> None:
    big_formula = big()
    inner = Imp(Not(big_formula), big_formula)
    target = Imp(inner, big_formula)
    verifier = Verifier()
    verifier.derived.append(target)
    message = verifier.submit(show(Or(Not(big_formula), big_formula)))
    assert "заменой по определению" in message
    assert (
        f"{show(target)} заменено на {show(Or(Not(big_formula), big_formula))}"
        in message
    )


def test_atomic_substitutions_are_rejected() -> None:
    verifier, _, _, step3, _, _, _ = build_mp_session()
    replacement = parse("(f∨g)⊃¬h")

    simultaneous = substitute(
        substitute(step3, "a", replacement), "q", v("r")
    )
    assert "не выводима" in verifier.submit(show(simultaneous))

    partial, done = replace_first_var(step3, "a", replacement)
    assert done
    assert "не выводима" in verifier.submit(show(partial))


def test_repeated_large_formula() -> None:
    verifier, _, _, step3, _, _, _ = build_mp_session()
    assert verifier.submit(show(step3)) == (
        f"Формула {show(step3)} уже есть в списке выведенных формул."
    )


def test_random_large_roundtrip() -> None:
    rng = random.Random(20261125)
    alphabet = "pqrsabcd"

    def make(depth: int):
        if depth == 0 or rng.random() < 0.3:
            return Var(rng.choice(alphabet))
        kind = rng.choice(("not", "or", "imp"))
        if kind == "not":
            return Not(make(depth - 1))
        left, right = make(depth - 1), make(depth - 1)
        return Or(left, right) if kind == "or" else Imp(left, right)

    for _ in range(200):
        formula = make(5)
        assert parse(show(formula)) == formula


def test_long_chain_and_deep_negation() -> None:
    chain = v("p")
    for _ in range(100):
        chain = Imp(chain, v("p"))
    assert parse("p" + "->p" * 100) == chain
    assert parse(show(chain)) == chain

    negated = v("p")
    for _ in range(100):
        negated = Not(negated)
    assert parse("~" * 100 + "p") == negated
    assert parse(show(negated)) == negated


def test_all_token_spellings_on_big_formula() -> None:
    formula = big()
    text = show(formula)
    variants = [
        text.replace("⊃", "->"),
        text.replace("⊃", "=>"),
        text.replace("⊃", "→"),
        text.replace("⊃", ">"),
        text.replace("∨", "|"),
        text.replace("∨", "\\/"),
        text.replace("¬", "~"),
        text.replace("¬", "!"),
        text.replace("⊃", "->").replace("∨", "|").replace("¬", "~"),
    ]
    for variant in variants:
        assert parse(variant) == formula, variant


def test_large_syntax_errors() -> None:
    text = show(big())
    broken = [
        text[:-1],
        text + ")",
        text.replace("⊃", "&", 1),
        text.replace("a", "ab", 1),
    ]
    verifier = Verifier()
    for variant in broken:
        assert verifier.submit(variant).startswith("Ошибка"), variant


def main() -> None:
    tests = [item for name, item in globals().items() if name.startswith("test_")]
    for test in tests:
        test()
        print("ok", test.__name__)
    print(f"passed {len(tests)}")


if __name__ == "__main__":
    main()
