method transferir(x: int, y: int, n: int)
    returns (x': int, y': int)
    ensures x' + y' == x + y
{
    x' := x - n;
    y' := y + n;
}
