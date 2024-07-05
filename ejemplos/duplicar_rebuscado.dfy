method duplicar(x: int) returns (y: int)
  requires x >= 0
  ensures y == x * 2
{
    y := x;
    var k := 0;
    while k < x 
        invariant k <= x && y == x + k
    {
        k := k + 1; 
        y := y + 1;
    }
}