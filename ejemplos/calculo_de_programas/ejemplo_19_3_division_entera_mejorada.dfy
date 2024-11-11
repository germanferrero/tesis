function pot_2(exp: nat): nat
    decreases exp
{
    if exp == 0 then 1 else 2 * pot_2(exp-1)
}

method max_pot_2(n: nat, y: nat) returns (p: nat)
    requires n > 0
    requires n >= y
    requires y > 0
    ensures pot_2(p) * y <= n  &&  pot_2(p+1) * y > n
{
    p := 0;
    var next_p : nat := 1;
    while pot_2(next_p) * y <= n
        invariant next_p == p + 1
        invariant pot_2(p) * y <= n
    {
        p := next_p;
        next_p := p + 1;
    }
}

method max_pot_2_menor_a(n: nat, y: int) returns (k: nat)
    requires n > 0
    requires n >= y
    requires y > 0
    ensures 0 < k * y <= n && 2 * (k * y) > n && exists j: nat :: k == pot_2(j)
{
    var p: nat := max_pot_2(n, y);
    k := pot_2(p);
}

method division_entera(x: int, y: int) returns (q: int, r: int)
    requires x >= 0 && y > 0
    ensures x == q * y + r && 0 <= r && r < y
{
    q := 0;
    r := x;
    while r >= y
        invariant x == q * y + r
        invariant r >= 0
    {
        var p2 := max_pot_2_menor_a(r, y);
        q := q + p2;
        r := r - p2 * y;
    }
}

// Con este ejercicio empecé chusmeando en el libro qué estrategia habían tomado para disminuir
// la cantidad de iteraciones. Luego, cansado, intenté implementarlo, y no lo logré hasta que
// lo agarrué descansado y dividí el problema en partes. Aislando max_pot_2_menor_a a su propio método,
// axiomatizarlo, primero, ver que me ayudaba a verificar division_entera. Y luego implementarlo.