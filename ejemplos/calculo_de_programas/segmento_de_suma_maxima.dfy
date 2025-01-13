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
    assert es_suma_maxima([1,2,-3], 3);
    assert suma(0, 3, [1,2,3]) == 6;
    assert es_suma_maxima([1,2,3], 6);
}

predicate invariante(k: int, A: seq<int>, r: int, u: int){
    0 <= k <= |A| &&
    (exists p_u :: 0 <= p_u <= k && suma(p_u, k, A) == u) &&
    (forall i :: 0 <= i <= k ==> suma(i, k, A) <= u) &&
    (exists p, q :: 0 <= p <= q <= k && suma(p, q, A) == r) &&
    (forall i, j :: 0 <= i <= j <= k ==> suma(i, j, A) <= r)
}

method inicializacion(A: seq<int>) returns (k: int, r: int, u: int)
    ensures invariante(k, A, r, u)
{
    k := 0;
    r := 0;
    u := 0;
    assert suma(0, 0, A) == 0;
}

method cuerpo(k: int, A: seq<int>, r: int, u:int) returns (k': int, r': int, u': int)
    requires k < |A|
    requires invariante(k, A, r, u)
    ensures invariante(k', A, r', u')
    ensures k' > k
{
    if u + A[k] < 0 {
        u' := 0;
        assert suma(k+1, k+1, A) == u';
    } else {
        u' := u + A[k];
        ghost var p_u :| (0 <= p_u <= k && suma(p_u, k, A) == u) && (forall i :: 0 <= i <= k ==> suma(i, k, A) <= u);
        assert suma(p_u, k+1, A) == u';
    }
    if u' > r {
        r' := u';
    } else {
        r' := r;
    }
    k' := k + 1;
}

method segmento_de_suma_maxima(A: seq<int>) returns (r: int)
    ensures es_suma_maxima(A, r)
{
    var k: int, u: int;
    k, r, u := inicializacion(A);
    while (k < |A|)
        decreases |A| - k
        invariant invariante(k, A, r, u)
    {
        k, r, u := cuerpo(k, A, r, u);
    }
}