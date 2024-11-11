method BinarySearch(arr: array<int>, target: int) returns (index: int)
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    //requires forall i :: 0 <= i < arr.Length - 1 ==> arr[i] <= arr[i + 1]  // Precondition: the array must be sorted
    ensures 0 <= index ==> index < arr.Length && arr[index] == target  // If index is valid, it points to the target
    ensures index < 0 ==> forall i :: 0 <= i < arr.Length - 1 ==> arr[i] != target  // If index equals the length of arr, target is not in arr
{
    var left, right := 0, arr.Length;
    var found := -1;

    while left < right
        invariant 0 <= left <= right <= arr.Length  // Invariant: left and right are within bounds
        invariant forall i ::
         0 <= i < arr.Length && !(left <= i < right) ==> arr[i] != target
    {
        var mid := (left + right) / 2;
        if arr[mid] < target {
            left := mid + 1;  // Search in the right half
        } else if target < arr[mid] {
            right := mid;  // Search in the left half
        } else {
            return mid;
        }
    }
    return -1;
}
