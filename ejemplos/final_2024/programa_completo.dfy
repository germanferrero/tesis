function sum_imp_f(A: seq<int>, i: int): int
    requires 0 <= i <= |A|
{
    if i <= 0
        then 0
        else (
            if A[i-1] % 2 == 1
                then A[i-1] + sum_imp_f(A, i - 1)
                else sum_imp_f(A, i -1)
        )
}

method test_sum_imp_f()
{
    assert sum_imp_f([1,2,3,4,5], 0) == 0;
    assert sum_imp_f([1,2,3,4,5], 1) == 1;
    assert sum_imp_f([1,2,3,4,5], 2) == 1;
    assert sum_imp_f([1,2,3,4,5], 3) == 4;
    assert sum_imp_f([1,2,3,4,5], 4) == 4;
    assert sum_imp_f([1,2,3,4,5], 5) == 9;
}

function factorial_f(i: int): int
    requires i >= 0
{
    if i == 0 then 1 else i * factorial_f(i - 1)
}

predicate Q_k(r: bool, A: seq<int>, k: int)
{
    0 <= k <= |A|
    && r == (forall i: int :: 0 <= i <= k
                ==> sum_imp_f(A, i) <= factorial_f(i))
}

predicate Q(r: bool, A: seq<int>)
{
    Q_k(r, A, |A|)
}

method test_Q(){
    assert Q(true, [1,2,3,4,5]);
    assert factorial_f(1) < 7;
    assert Q(false, [7,2,3,4,5]);
}

predicate invariante(r: bool, A: seq<int>, k: int, sum_imp: int, i_fact: int)
{
    0 <= k <= |A|
    && sum_imp == sum_imp_f(A, k)
    && i_fact == factorial_f(k)
    && Q_k(r, A, k)
}


method inicializacion(A: seq<int>)
    returns (i: int, r: bool, sum_imp: int, i_fact: int)
    ensures invariante(r, A, i, sum_imp, i_fact)
{
    i := 0;
    r := true;
    sum_imp := 0;
    i_fact := 1;
}

method cuerpo(r:bool, A: seq<int>, i: int, sum_imp: int, i_fact: int)
    returns (r': bool, i': int, sum_imp':int , i_fact':int)
    requires r && i < |A|
    requires invariante(r, A, i, sum_imp, i_fact)
    ensures invariante(r', A, i', sum_imp', i_fact')
    ensures i' > i
{
    if A[i] % 2 == 1 {
        sum_imp' := sum_imp + A[i];
    } else {
        sum_imp' := sum_imp;
    }
    i_fact' := (i + 1) * i_fact;
    r' := sum_imp' <= i_fact';
    i' := i + 1;
}


method ejercicio(A: seq<int>)
    returns (r: bool)
    ensures Q(r, A)
{
    var i: int, sum_imp: int, i_fact: int;
    i, r, sum_imp, i_fact := inicializacion(A);
    while r && i < |A|
        decreases |A| - i
        invariant invariante(r, A, i, sum_imp, i_fact)
    {
        r, i, sum_imp, i_fact := cuerpo(r, A, i, sum_imp, i_fact);
    }
}