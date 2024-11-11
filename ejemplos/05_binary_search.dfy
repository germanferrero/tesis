method BinarySearch(a: array<int>, key: int) returns (index: int)
    requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    //requires forall i :: 0 <= i < a.Length - 1 ==> a[i] <= a[i + 1] // Con este solo, no logra verificarlo.

    ensures 0 <= index ==> index < a.Length && a[index] == key
    ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
{
    var l, r := 0, a.Length;
    while l < r
        invariant 0 <= l <= r <= a.Length
        invariant forall i ::
         0 <= i < a.Length && !(l <= i < r) ==> a[i] != key
    {
        var m := (l + r) / 2;
        if a[m] < key {
            l := m + 1;
        } else if key < a[m] {
            r := m;
        } else {
            return m;
        }
    }

    return -1;
}
