"""Проверки интерпретатора многозначных логик (лабораторная работа №2).

Запуск: python test_multivalued.py
"""

from multivalued import (
    CLASSICAL,
    HALF,
    KLEENE,
    LUKASIEWICZ,
    ONE,
    SYSTEMS,
    ZERO,
    And,
    EvaluationError,
    Imp,
    Not,
    Or,
    ParseError,
    TASK1,
    TASK2,
    Var,
    analyze,
    build_report,
    check_consequence,
    compare_systems,
    evaluate,
    format_value,
    parse,
    show,
)


def v(name: str) -> Var:
    return Var(name)


def get_rule(name: str):
    for rule_name, premise_texts, conclusion_text in TASK2:
        if rule_name == name:
            return (
                [parse(text) for text in premise_texts],
                parse(conclusion_text),
            )
    raise KeyError(name)


def test_parser_precedence() -> None:
    assert parse("p∧q∨r") == Or(And(v("p"), v("q")), v("r"))
    assert parse("p∨q→r") == Imp(Or(v("p"), v("q")), v("r"))
    assert parse("p→q→r") == Imp(Imp(v("p"), v("q")), v("r"))
    assert parse("¬p∧q") == And(Not(v("p")), v("q"))
    assert parse("p∧q∧r") == And(And(v("p"), v("q")), v("r"))
    assert parse("p→q∧r") == Imp(v("p"), And(v("q"), v("r")))
    assert parse("p∨q∧r") == Or(v("p"), And(v("q"), v("r")))


def test_parser_spellings() -> None:
    base = parse("¬p∧q→r")
    assert parse("~p & q -> r") == base
    assert parse("(!p ^ q) => r") == base
    assert parse(r"~p /\ q -> r") == base
    assert parse("p ∨ q") == parse(r"p \/ q")
    assert parse("p ∨ q") == parse("p | q")
    assert parse("p → q") == parse("p ⊃ q")
    assert parse("p → q") == parse("p > q")


def test_parser_errors() -> None:
    samples = [
        "p→",
        "→p",
        "p q",
        "pq",
        "p∧",
        "(p∧q",
        "p∧q)",
        "",
        "p ∧ ∨ q",
        "p1",
        "p & ",
    ]
    for sample in samples:
        try:
            parse(sample)
        except ParseError:
            continue
        raise AssertionError(f"должно быть ошибкой: {sample!r}")


def test_show_roundtrip() -> None:
    for text in ["p", "¬¬p", "p∧(q∨¬r)", "((p→q)∧(p→¬q))→¬p"]:
        formula = parse(text)
        assert parse(show(formula)) == formula


def test_format_value() -> None:
    assert format_value(ZERO) == "0"
    assert format_value(HALF) == "1/2"
    assert format_value(ONE) == "1"


def test_table_sizes() -> None:
    assert len(analyze(parse("p"), CLASSICAL).rows) == 2
    assert len(analyze(parse("p"), KLEENE).rows) == 3
    assert len(analyze(parse("p∧q"), CLASSICAL).rows) == 4
    assert len(analyze(parse("p∧q"), KLEENE).rows) == 9
    assert len(analyze(parse("p∧q∧r"), LUKASIEWICZ).rows) == 27


def test_lab_example_implication() -> None:
    formula = parse("p → q")
    assert evaluate(formula, {"p": HALF, "q": HALF}, KLEENE) == HALF
    assert evaluate(formula, {"p": HALF, "q": HALF}, LUKASIEWICZ) == ONE


def test_connectives_semantics() -> None:
    assignment = {"p": HALF, "q": ZERO}
    assert evaluate(parse("¬p"), assignment, KLEENE) == HALF
    assert evaluate(parse("p∨q"), assignment, KLEENE) == HALF
    assert evaluate(parse("p∧q"), assignment, KLEENE) == ZERO


def test_evaluation_requires_all_variables() -> None:
    try:
        evaluate(parse("p∧q"), {"p": ONE}, KLEENE)
    except EvaluationError:
        return
    raise AssertionError("ожидалась EvaluationError")


def test_f1_classical_but_not_many_valued_validity() -> None:
    formula = parse("p ∨ ¬p")
    assert analyze(formula, CLASSICAL).is_valid
    k3 = analyze(formula, KLEENE)
    l3 = analyze(formula, LUKASIEWICZ)
    assert not k3.is_valid and not l3.is_valid
    assert ({"p": HALF}, HALF) in k3.counterexamples
    assert ({"p": HALF}, HALF) in l3.counterexamples


def test_f2_contraposition_k3_vs_l3() -> None:
    formula = parse("(p → q) → (¬q → ¬p)")
    assert analyze(formula, CLASSICAL).is_valid
    assert not analyze(formula, KLEENE).is_valid
    assert analyze(formula, LUKASIEWICZ).is_valid


def test_f3_unsatisfiable_but_not_identically_false() -> None:
    formula = parse("¬(p ∨ ¬p)")
    classical = analyze(formula, CLASSICAL)
    assert classical.is_identically_false
    assert not classical.is_satisfiable

    for system in (KLEENE, LUKASIEWICZ):
        analysis = analyze(formula, system)
        assert not analysis.is_satisfiable
        assert not analysis.is_identically_false
        assert HALF in analysis.values
        assert "не тождественно ложна" in analysis.classification


def test_f4_satisfiable_everywhere() -> None:
    formula = parse("(p ∧ q) ∨ (¬p ∧ r)")
    for system in SYSTEMS.values():
        analysis = analyze(formula, system)
        assert analysis.is_satisfiable
        assert not analysis.is_valid


def test_f5_classical_validity_only() -> None:
    formula = parse("((p → q) ∧ (p → ¬q)) → ¬p")
    assert analyze(formula, CLASSICAL).is_valid
    assert not analyze(formula, KLEENE).is_valid
    assert not analyze(formula, LUKASIEWICZ).is_valid


def test_consequence_r1_entailed_everywhere() -> None:
    premises, conclusion = get_rule("R1")
    for system in SYSTEMS.values():
        result = check_consequence(premises, conclusion, system)
        assert result.status == "entailed", system.key
        assert result.counterexamples == ()


def test_consequence_r2_between_k3_and_l3() -> None:
    premises, conclusion = get_rule("R2")
    assert check_consequence(premises, conclusion, CLASSICAL).status == "entailed"
    assert check_consequence(premises, conclusion, KLEENE).status == "entailed"
    l3 = check_consequence(premises, conclusion, LUKASIEWICZ)
    assert l3.status == "not_entailed"
    assert any(row.conclusion_value == HALF for row in l3.counterexamples)


def test_consequence_r3_and_r4_fail() -> None:
    for name in ("R3", "R4"):
        premises, conclusion = get_rule(name)
        for system in SYSTEMS.values():
            result = check_consequence(premises, conclusion, system)
            assert result.status == "not_entailed", (name, system.key)
            assert result.counterexamples


def test_inconsistent_premises_are_reported_separately() -> None:
    premises = [parse("p"), parse("¬p")]
    conclusion = parse("q")
    for system in SYSTEMS.values():
        result = check_consequence(premises, conclusion, system)
        assert result.status == "inconsistent"
        assert "несовместны" in result.verdict
        assert result.satisfying_rows == ()
        assert result.counterexamples == ()


def test_counterexample_allows_conclusion_half() -> None:
    result = check_consequence([parse("p")], parse("q"), KLEENE)
    assert result.status == "not_entailed"
    assert any(
        row.assignment == {"p": ONE, "q": HALF}
        and row.conclusion_value == HALF
        for row in result.counterexamples
    )

    classical = check_consequence([parse("p")], parse("q"), CLASSICAL)
    assert classical.status == "not_entailed"
    assert any(
        row.assignment == {"p": ONE, "q": ZERO}
        for row in classical.counterexamples
    )


def test_comparison_of_systems() -> None:
    f1 = compare_systems(parse("p ∨ ¬p"))
    assert f1.k3_vs_l3 == ()
    assert f1.cl_vs_k3 == ()
    assert not f1.properties_match
    assert f1.analyses["cl"].is_valid
    assert not f1.analyses["k3"].is_valid

    f2 = compare_systems(parse("(p → q) → (¬q → ¬p)"))
    assert len(f2.k3_vs_l3) == 3
    assert f2.cl_vs_k3 == ()
    assert not f2.properties_match
    assert not f2.analyses["k3"].is_valid
    assert f2.analyses["l3"].is_valid

    f4 = compare_systems(parse("(p ∧ q) ∨ (¬p ∧ r)"))
    assert f4.properties_match
    assert f4.k3_vs_l3 == ()
    assert f4.cl_vs_k3 == ()
    assert f4.cl_vs_l3 == ()


def test_variant_formulas_parse() -> None:
    for _, text in TASK1:
        parse(text)
    for _, premise_texts, conclusion_text in TASK2:
        for text in premise_texts:
            parse(text)
        parse(conclusion_text)


def test_report_contains_required_sections() -> None:
    report = build_report()
    markers = [
        "# Лабораторная работа №2",
        "Вариант:** 3",
        "Задание 1",
        "Задание 2",
        "F1",
        "F5",
        "R1",
        "R4",
        "Выводы",
        "невыполнима",
        "K3",
        "L3",
    ]
    for marker in markers:
        assert marker in report, marker


def main() -> None:
    tests = [item for name, item in globals().items() if name.startswith("test_")]
    for test in tests:
        test()
        print("ok", test.__name__)
    print(f"passed {len(tests)}")


if __name__ == "__main__":
    main()
