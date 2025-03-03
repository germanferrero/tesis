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

method test_factorial_f() {
    assert factorial_f(0) == 1;
    assert factorial_f(1) == 1;
    assert factorial_f(2) == 2;
    assert factorial_f(3) == 6;
    assert factorial_f(4) == 24;
}

predicate Q(r: bool, A: seq<int>)
{
    r == (forall i: int :: 0 <= i <= |A| ==> sum_imp_f(A, i) <= factorial_f(i))
}

method ejercicio(A: seq<int>)
    returns (r: bool)
    ensures Q(r, A)