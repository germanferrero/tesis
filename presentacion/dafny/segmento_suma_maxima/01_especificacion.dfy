function suma(p:nat, q:nat, A: seq<int>): int
    requires 0 <= p <= q <= |A|
{
    if q <= p then 0 else suma(p, q-1, A) + A[q-1]
}

predicate es_suma_maxima(A: seq<int>, r: int) {
    (exists p, q :: 0 <= p <= q <= |A| && suma(p, q, A) == r) &&
    (forall i, j :: 0 <= i <= j <= |A| ==> suma(i, j, A) <= r)
}

method segmento_de_suma_maxima(A: seq<int>) returns (r: int)
    ensures es_suma_maxima(A, r)