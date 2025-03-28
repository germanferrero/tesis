function suma(p:nat, q:nat, A: seq<int>): int
    requires 0 <= p <= q <= |A|
{
    if q <= p then 0 else suma(p, q-1, A) + A[q-1]
}

predicate es_suma_maxima(A: seq<int>, r: int) {
    (exists p, q :: 0 <= p <= q <= |A| && suma(p, q, A) == r) &&
    (forall i, j :: 0 <= i <= j <= |A| ==> suma(i, j, A) <= r)
}

predicate invariante(k: int, A: seq<int>, r: int){
    0 <= k <= |A| &&
    (exists p, q :: 0 <= p <= q <= k && suma(p, q, A) == r) &&
    (forall i, j :: 0 <= i <= j <= k ==> suma(i, j, A) <= r)
}

method segmento_de_suma_maxima(A: seq<int>) returns (r: int)
    ensures es_suma_maxima(A, r)
{
    var k: int, u: int := *, *;
    r := *;
    assume invariante(k, A, r);
    while (k < |A|)
        decreases |A| - k
        invariant invariante(k, A, r)
}