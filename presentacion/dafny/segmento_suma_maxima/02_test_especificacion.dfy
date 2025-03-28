function suma(p:nat, q:nat, A: seq<int>): int
    requires 0 <= p <= q <= |A|
{
    if q <= p then 0 else suma(p, q-1, A) + A[q-1]
}

predicate es_suma_maxima(A: seq<int>, r: int) {
    (exists p, q :: 0 <= p <= q <= |A| && suma(p, q, A) == r) &&
    (forall i, j :: 0 <= i <= j <= |A| ==> suma(i, j, A) <= r)
}

method test_suma()
{
    assert suma(0, 3, [1,2,-3,4,5]) == 0;
    assert suma(0, 4, [1,2,-3,4,5]) == 4;
    assert suma(3, 5, [1,2,-3,4,5]) == 9;
    assert suma(4, 4, [1,2,-3,4,5]) == 0;
}

method test_es_suma_maxima(){
    assert suma(0, 4, [1,2,-2,4]) == 5;
    assert es_suma_maxima([1,2,-2,4], 5);
    assert es_suma_maxima([1,2,-3], 3);
    assert suma(0, 3, [1,2,3]) == 6;
    assert es_suma_maxima([1,2,3], 6);
}

method segmento_de_suma_maxima(A: seq<int>) returns (r: int)
    ensures es_suma_maxima(A, r)