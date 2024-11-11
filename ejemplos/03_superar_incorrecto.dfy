method superar_incorrecto(x: int) returns (y: int)
    ensures y > x
    requires x > 0
{
    y := x * 2;
}