function exponenciacion_de_enteros_f(A: nat, B: nat): nat
    decreases B
{
    if (B == 0) then 1 else A * exponenciacion_de_enteros_f(A, B-1)
}

method exponenciacion_de_enteros(A: nat, B: nat) returns (r: nat)
    ensures r == exponenciacion_de_enteros_f(A, B)
{
    var i: nat := 0;
    r := 1;
    while i != B
        invariant r == exponenciacion_de_enteros_f(A, i)
        invariant i <= B
        decreases B - i
    {
        r := r * A;
        i := i + 1;
    }
}


// Este ejercicio salio bastante directo salvo que al principio tenía:
// method exponenciacion_de_enteros(A: nat, B: nat) returns (r: nat)
//     ensures r == exponenciacion_de_enteros_f(A, B)
// {
//     var i: nat := 0;
//     r := 1;
//     while i < B
//         invariant r == exponenciacion_de_enteros_f(A, i)
//         decreases B - i
//     {
//         r := r * A;
//         i := i + 1;
//     }
// }
// Y eso no anduvo. Metí un assert(i == B) abajo del while, para ver si estaba pudiendo
// probar eso Dafny y no. Luego cambié por i != B la guarda, y solo luego de eso y agregar el
// invariante invariant i <= B. Salió andando.