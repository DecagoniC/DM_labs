"""Проверки разбора формул и правил варианта 3."""

from verifier import (
    Imp,
    Not,
    Or,
    Var,
    Verifier,
    definition_steps,
    find_beta,
    justify,
    parse,
    show,
)


def v(name: str) -> Var:
    return Var(name)


def test_axioms_have_expected_trees() -> None:
    verifier = Verifier()
    expected = [
        Imp(v("p"), Or(v("p"), v("q"))),
        Imp(Or(v("p"), v("p")), v("p")),
        Imp(Or(v("p"), Or(v("q"), v("r"))), Or(v("q"), Or(v("p"), v("r")))),
        Imp(Imp(v("q"), v("s")), Imp(Or(v("p"), v("q")), Or(v("p"), v("s")))),
        Imp(Not(Not(v("p"))), v("p")),
        Imp(Imp(Not(v("q")), Not(v("p"))), Imp(v("p"), v("q"))),
    ]
    assert verifier.axioms == expected


def test_left_associativity_and_precedence() -> None:
    assert parse("p->q->r") == Imp(Imp(v("p"), v("q")), v("r"))
    assert parse("p⊃q⊃r") == parse("(p⊃q)⊃r")
    assert parse("p->r->(p->p)") == parse("(p->r)->(p->p)")
    assert parse("p->r->(p->p)") != parse("p->(r->(p->p))")
    assert parse("p|q->r") == Imp(Or(v("p"), v("q")), v("r"))
    assert parse("p->q|r") == Imp(v("p"), Or(v("q"), v("r")))
    assert parse("~p|q") == Or(Not(v("p")), v("q"))
    assert parse("~p->q") == Imp(Not(v("p")), v("q"))
    assert parse("~~p->p") == Imp(Not(Not(v("p"))), v("p"))
    assert parse("p|q|r") == Or(Or(v("p"), v("q")), v("r"))


def test_extra_parentheses_are_ignored() -> None:
    assert parse("(((a)->b))->(f->((p->(q))))") == parse("(a->b)->(f->(p->q))")
    assert parse("(((p)|p))->(p)") == parse("p|p->p")


def test_syntax_errors() -> None:
    samples = [
        "p->(p->p))",
        "mn->(p->p)",
        "q->(p p)",
        "->a->b->c",
        "a->b->c->",
        "((p)",
        "p q",
        "",
        "   ",
        "p->",
        "(p|q",
        "1",
        "p & q",
    ]
    verifier = Verifier()
    for sample in samples:
        message = verifier.submit(sample)
        assert message.startswith("Ошибка"), sample


def test_pretty_printer_roundtrip() -> None:
    def forms(depth: int) -> list:
        if depth == 0:
            return [v("p"), v("q")]
        smaller = forms(depth - 1)
        result = list(smaller)
        for item in smaller:
            result.append(Not(item))
        for left in smaller:
            for right in smaller:
                result.append(Or(left, right))
                result.append(Imp(left, right))
        return result

    for formula in forms(2):
        assert parse(show(formula)) == formula


def test_exact_axiom_and_beta() -> None:
    verifier = Verifier()
    axiom = verifier.submit("(p\\/p)->p")
    assert axiom == "Формула ((p∨p)⊃p) является аксиомой 2"
    beta = verifier.submit("(a\\/a)->a")
    assert beta == (
        "Формула ((a∨a)⊃a) выводима из формулы ((p∨p)⊃p) "
        "по правилу бета с подстановкой формулы a вместо переменной p"
    )
    complex_step = verifier.submit("((r->s)\\/(r->s))->(r->s)")
    assert "подстановкой формулы (r⊃s) вместо переменной p" in complex_step


def test_beta_replaces_only_one_variable() -> None:
    source = parse("p|q")
    assert find_beta(source, parse("a|b")) is None
    assert find_beta(source, parse("a|q")) == ("p", v("a"))
    assert find_beta(parse("p|p"), parse("(r->s)|(r->s)")) == ("p", parse("r->s"))
    verifier = Verifier()
    verifier.derived.append(source)
    assert "не выводима" in verifier.submit("a|b")
    assert "правилу бета" in verifier.submit("a|q")


def test_modus_ponens_needs_both_premises() -> None:
    verifier = Verifier()
    verifier.derived.append(parse("(q|q)->q"))
    assert "не выводима" in verifier.submit("q")
    verifier.derived.append(parse("q|q"))
    message = verifier.submit("q")
    assert message == (
        "Формула q выводима из формул ((q∨q)⊃q) и (q∨q) по правилу modus ponens"
    )


def test_modus_ponens_can_use_an_axiom() -> None:
    verifier = Verifier()
    verifier.derived.append(parse("p|p"))
    message = verifier.submit("p")
    assert message == (
        "Формула p выводима из формул ((p∨p)⊃p) и (p∨p) по правилу modus ponens"
    )


def test_definition_both_directions_and_one_occurrence() -> None:
    verifier = Verifier()
    verifier.derived.append(parse("~q|q"))
    forward = verifier.submit("(~q->q)->q")
    assert forward == (
        "Формула ((¬q⊃q)⊃q) выводима из формулы (¬q∨q) "
        "заменой по определению: (¬q∨q) заменено на ((¬q⊃q)⊃q)"
    )

    verifier = Verifier()
    verifier.derived.append(parse("(~p->p)->p"))
    backward = verifier.submit("~p|p")
    assert "((¬p⊃p)⊃p) заменено на (¬p∨p)" in backward

    verifier = Verifier()
    verifier.derived.append(parse("~(p|q)|(p|q)"))
    complex = verifier.submit("(~(p|q)->(p|q))->(p|q)")
    assert "(¬(p∨q)∨(p∨q)) заменено на ((¬(p∨q)⊃(p∨q))⊃(p∨q))" in complex

    verifier = Verifier()
    verifier.derived.append(parse("(~p|p)|(~p|p)"))
    assert "не выводима" in verifier.submit("((~p->p)->p)|((~p->p)->p)")
    one = verifier.submit("((~p->p)->p)|(~p|p)")
    assert "заменой по определению" in one
    assert len(definition_steps(parse("(~p|p)|(~p|p)"))) == 2


def test_definition_inside_context() -> None:
    verifier = Verifier()
    verifier.derived.append(parse("(~q|q)->r"))
    message = verifier.submit("((~q->q)->q)->r")
    assert message.startswith(
        "Формула (((¬q⊃q)⊃q)⊃r) выводима из формулы ((¬q∨q)⊃r)"
    )


def test_rejected_formula_is_not_stored() -> None:
    verifier = Verifier()
    verifier.submit("p")
    assert verifier.derived == []
    verifier.submit("p|p->p")
    verifier.submit("p")
    assert [show(item) for item in verifier.derived] == ["((p∨p)⊃p)"]


def test_repeated_formula() -> None:
    verifier = Verifier()
    verifier.submit("p|p->p")
    again = verifier.submit("((p)|p)->p")
    assert again == "Формула ((p∨p)⊃p) уже есть в списке выведенных формул."
    assert len(verifier.derived) == 1


def main() -> None:
    tests = [item for name, item in globals().items() if name.startswith("test_")]
    for test in tests:
        test()
        print("ok", test.__name__)
    print(f"passed {len(tests)}")


if __name__ == "__main__":
    main()
