function pow_2(exp: nat): nat
    decreases exp
{
    if exp == 0 then 1 else 2 * pow_2(exp-1)
}

method max_pot_2(n: nat) returns (p: nat)
    requires n > 0
    ensures pow_2(p) <= n &&  pow_2(p+1) > n
{
    p := 0;
    var np : nat := 1;
    while pow_2(np) <= n
        invariant np == p + 1
        invariant pow_2(p) <= n
    {
        p := np;
        np := p + 1;
    }
}

method max_pot_2_r(n: nat) returns (k: nat)
    requires n > 0
    ensures 0 < k <= n && 2 * k > n && exists j: nat :: k == pow_2(j)
{
    var p: nat := max_pot_2(n);
    k := pow_2(p);
}