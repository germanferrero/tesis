function fibonacci_f(n: nat): nat {
    if n == 0 then 0 else if n == 1 then 1 else fibonacci_f(n-1) + fibonacci_f(n-2)
}

method fibonacci (n: nat) returns (r: nat)
    ensures r == fibonacci_f(n)
{
    if n == 0 {
        return 0;
    } else if n == 1 {
        return 1;
    } else {
        var fib_pp: nat := 0;
        var fib_p: nat := 1;
        var i := 2;
        while i != n
            invariant fib_pp == fibonacci_f(i-2)
            invariant fib_p == fibonacci_f(i-1)
            invariant i <= n
            decreases n - i
        {
            var fib_tmp := fib_pp;
            fib_pp := fib_p;
            fib_p := fib_p + fib_tmp;
            i := i + 1;
        }
        return fib_pp + fib_p;
    }
}

// Este salió sin inconvenientes. Empecé escribiendo fibonacci_f.
// Luego la especificacion del metodo y la estructura if elseif else del cuerpo.
// Continué por pensar en la estrategia, ir aumentando i hasta llegar a n.
// manteniendo como invariante que en fib_pp y fib_p tendria siempre
// fibonacci_f(i-2) e fibonacci_f(i-1) respectivamente.
// Opté por la guarda i != n junto con el invariante i <= n, luego de la experiencia con el ejemplo_19_5.
// Terminé de escribirlo y estaba verificado.
