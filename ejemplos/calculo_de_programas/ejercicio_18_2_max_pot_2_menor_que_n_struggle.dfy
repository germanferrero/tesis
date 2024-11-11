function pow_2(exp: nat): nat 
    decreases exp
{
    if exp == 0 then 1 else 2 * pow_2(exp-1)
}

method max_pot_2(n: nat) returns (k: nat)
    requires n > 0
    ensures 0 < k <= n && 2 * k > n && exists j: nat :: k == pow_2(j)
{
    k := 1;
    while n >= 2 * k
        invariant 0 < k <= n
        invariant exists j: nat :: k == pow_2(j)
    {
        k := 2 * k;
    }
}