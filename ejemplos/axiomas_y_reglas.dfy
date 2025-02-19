module axioma_de_la_asignacion {
    function E(x: int): int
    predicate P(x: int)

    method test()
    {
        var x: int := 0;
        assume {:axiom} P(E(x));
        x := E(x);
        assert P(x);
    }
}

module regla_del_fortalecimiento_de_la_precondicion {
    predicate P(x: int)
    predicate P'(x: int)
    predicate Q(x: int)

    method S(x: int)
        requires P'(x)
        ensures Q(x)

    method test(x: int)
    {
        assume forall x: int :: P(x) ==> P'(x);
        assume P(x);
        S(x);
        assert Q(x); 
    }
}

module regla_del_debilitamiento_de_la_poscondicion {
    predicate P(x: int)
    predicate Q(x: int)
    predicate Q'(x: int)

    method S(x: int)
        requires P(x)
        ensures Q'(x)

    method test(x: int)
    {
        assume forall x: int :: Q'(x) ==> Q(x);
        assume P(x);
        S(x);
        assert Q(x); 
    }
}

module regla_de_la_conjuncion_de_especificaciones {
    predicate P1(x: int)
    predicate Q1(x: int)
    predicate P2(x: int)
    predicate Q2(x: int)

    method {:axiom} S(x: int)
        requires P1(x) || P2(x)
        ensures if P1(x) then Q1(x) else true
        ensures if P2(x) then Q2(x) else true

    method test(x: int)
    {
        assume {:axiom} P1(x) && P2(x);
        S(x);
        assert Q1(x) && Q2(x);
    }
}

module regla_de_la_disyuncion_de_especificaciones {
    predicate P1(x: int)
    predicate Q1(x: int)
    predicate P2(x: int)
    predicate Q2(x: int)

    method {:axiom} S(x: int)
        requires P1(x) || P2(x)
        ensures if P1(x) then Q1(x) else true
        ensures if P2(x) then Q2(x) else true

    method test(x: int)
    {
        assume {:axiom} P1(x) || P2(x);
        S(x);
        assert Q1(x) || Q2(x);
    }
}

module regla_de_la_composicion{
    predicate P(x: int)
    predicate Q(x: int)
    predicate R(x: int)

    method {:axiom} S1(x: int)
        requires P(x)
        ensures R(x)

    method {:axiom} S2(x: int)
        requires R(x)
        ensures Q(x)

    method test(x: int)
    {
        assume {:axiom} P(x);
        S1(x);
        S2(x);
        assert Q(x);
    }
}

module regla_de_la_alternativa{
    predicate P(x: int)
    predicate Q(x: int)
    function B(x: int): bool

    method {:axiom} S(x: int)
        requires P(x) && B(x)
        ensures Q(x)

    method {:axiom} T(x: int)
        requires P(x) && !B(x)
        ensures Q(x)

    method test(x: int)
    {
        assume {:axiom} P(x);
        if B(x) {
            S(x);
        } else {
            T(x);
        }
        assert Q(x);
    }
}

module regla_de_la_repeticion{
    function B(x: int): bool
    function E(x: int): int
    predicate I(x: int)

    method {:axiom} S(x: int) returns (x': int)
        requires I(x) && B(x)
        ensures I(x')
        ensures E(x') < E(x)

    method test(){
        assume {:axiom} forall x: int :: I(x) && B(x) ==> E(x) >= 0;
        var x: int := 0;
        assume {:axiom} I(x);
        while B(x)
            decreases E(x)
            invariant I(x)
        {
            assert I(x) && B(x);
            x := S(x);
        }
        assert I(x) && !B(x);
    }
}