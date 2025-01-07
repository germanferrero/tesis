function suma(p:nat, q:nat, A: seq<int>): int
    requires 0 <= p <= q <= |A|
{
    if q <= p then 0 else suma(p, q-1, A) + A[q-1]
}

method segmento_de_suma_maxima(A: seq<int>) returns (r: int, p: nat, q: nat)
    ensures 0 <= p <= q <= |A|
    ensures r == suma(p, q, A)
    ensures forall i, j :: 0 <= i <= j <= |A| ==> suma(i, j, A) <= r
{
    var n, u := 0, 0;
    var u_p := 0;
    p, q := 0, 0;
    r := 0;
    while n < |A|
        decreases |A| - n
        invariant 0 <= n <= |A|
        invariant 0 <= u_p <= n
        invariant u == suma(u_p, n, A)
        invariant forall i :: 0 <= i <= n ==> suma(i, n, A) <= u
        invariant 0 <= p <= q <= |A|
        invariant r == suma(p, q, A)
        invariant forall i, j :: 0 <= i <= j <= n ==> suma(i, j, A) <= r
    {
        if u + A[n] > r {
            r := u + A[n];
            p := u_p;
            q := n + 1;
        }
        if u + A[n] > 0 {
            u := u + A[n];
        } else {
            u_p := n + 1;
            u := 0;
        }
        n := n + 1;
    }
}