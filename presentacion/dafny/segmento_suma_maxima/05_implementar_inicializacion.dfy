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

method inicializacion(A: seq<int>)
    returns (k: int, r: int)
    ensures invariante(k, A, r)
{
    k := 0;
    r := 0;
    assert suma(0, 0, A) == 0;
}

method cuerpo(k: int, A: seq<int>, r: int)
    returns (k': int, r': int)
    requires k < |A|
    requires invariante(k, A, r)
    ensures invariante(k', A, r')
    ensures k' > k

method segmento_de_suma_maxima(A: seq<int>) returns (r: int)
    ensures es_suma_maxima(A, r)
{
    var k: int, u: int;
    k, r := inicializacion(A);
    while (k < |A|)
        decreases |A| - k
        invariant invariante(k, A, r)
    {
        k, r := cuerpo(k, A, r);
    }
}