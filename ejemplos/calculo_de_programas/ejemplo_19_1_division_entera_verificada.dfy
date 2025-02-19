method division_entera(x: int, y: int) returns (q: int, r: int)
    requires x > 0 && y > 0
    ensures x == q * y + r && 0 <= r < y
{
    q := 0;
    r := x;
    while r >= y
        invariant x == q * y + r && r >= 0
        decreases r
    {
        q := q + 1;
        r := r - y;
    }
}