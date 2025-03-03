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
    && r == (forall i: int :: 0 <= i <= k ==> sum_imp_f(A, i) <= factorial_f(i))
}

predicate Q(r: bool, A: seq<int>)
{
    Q_k(r, A, |A|)
}

predicate invariante(r: bool, A: seq<int>, k: int)
{
    Q_k(r, A, k)
}

method inicializacion(A: seq<int>)
    returns (i: int, r: bool)
    ensures invariante(r, A, i)

method cuerpo(r:bool, A: seq<int>, i: int)
    returns (r': bool, i': int)
    requires r && i < |A|
    requires invariante(r, A, i)
    ensures invariante(r', A, i')
    ensures i' > i

method ejercicio(A: seq<int>)
    returns (r: bool)
    ensures Q(r, A)
{
    var i: int;
    i, r := inicializacion(A);
    while r && i < |A|
        decreases |A| - i
        invariant invariante(r, A, i)
    {
        r, i := cuerpo(r, A, i);
    }
    return r;
}