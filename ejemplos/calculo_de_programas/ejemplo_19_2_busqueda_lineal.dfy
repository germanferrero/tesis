method linear_search(f: nat -> bool) returns (x: nat)
    requires exists n : nat :: f(n)
    ensures f(x) && forall i : nat :: i < x ==> !f(i)
{
    x := 0;
    ghost var n : nat :| f(n);
    while !f(x)
        decreases n - x
        invariant forall i : nat :: i < x ==> !f(i)
    {
        x := x + 1;
    }
}

method bounded_linear_search(f: nat -> bool, max_bound: nat) returns (x: nat)
    requires exists n : nat :: n <= max_bound && f(n)
    ensures f(x) && forall i : nat :: i < x ==> !f(i)
{
    x := 0;
    while !f(x) && x <= max_bound
        decreases max_bound - x
        invariant forall i : nat :: i < x ==> !f(i)
    {
        x := x + 1;
    }
}


// Este ejercicio no salió hasta que introduje
// ghost var n : nat :| f(n);
// Que permitió la cláusula decresas n - x
// ghost permite declarar variables que no serán utilizadas por el compilador, pero si por el
// el verificador. El verificador entiende el tipo nat como los naturales en términos matemáticos
// un conjunto infinito de valores. Referenciar un elemento arbitrario de ese conjunto tiene sentido
// para el verificador, no así para el compilador.
// Que este programa esté verificado, significa que el programa compilado cumpla con su especificicación?
// Ciertamente no, si el natural para el cual vale f(n) no puede ser expresado en los bits utilizados
// por el tipo que utilice el compilador.
