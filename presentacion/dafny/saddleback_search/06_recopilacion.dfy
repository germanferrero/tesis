method busqueda_por_acorralamiento(A: array2<int>, val: int)
  returns(x: int, y: int)
  requires forall i, j, j' ::
             0 <= i < A.Length0 && 0 <= j < j' < A.Length1
             ==> A[i,j] <= A[i, j']
  requires forall i, i', j ::
             0 <= j < A.Length1 && 0 <= i < i' < A.Length0
             ==> A[i,j] <= A[i', j]
  requires exists x, y ::
             0 <= x < A.Length0 && 0 <= y < A.Length1 && A[x, y] == val
  ensures 0 <= x < A.Length0 && 0 <= y < A.Length1
  ensures A[x, y] == val
{
  var i, j := A.Length0 - 1, 0;
  while (A[i,j] != val)
    invariant 0 <= i < A.Length0 && 0 <= j < A.Length1
    invariant exists x, y ::
                0 <= x <= i && j <= y < A.Length1 && A[x, y] == val
    decreases i + A.Length1 - j
  {
    if val > A[i, j] {
      j := j + 1;
      i := i;
    } else {
      i := i - 1;
      j := j;
    }
  }
  return i, j;
}