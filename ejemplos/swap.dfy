class estado {
    var x: int
    var y: int
}

method swap(sigma: estado)
    modifies sigma
    ensures sigma.x == old(sigma.y) && sigma.y == old(sigma.x)
{
    var tmp: int;
    tmp := sigma.x;
    sigma.x := sigma.y;
    sigma.y := tmp;
}
