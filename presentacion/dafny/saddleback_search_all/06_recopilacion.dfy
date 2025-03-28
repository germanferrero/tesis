method busqueda_por_acorralamiento(A: array2<int>, val: int)
  returns (r: seq<(int,int)>)
  requires (forall i, j, j' ::
              (0 <= i < A.Length0 && 0 <= j < j' < A.Length1 ==> A[i,j] < A[i, j']))
           &&
           (forall i, i', j ::
              (0 <= j < A.Length1 && 0 <= i < i' < A.Length0 ==> A[i,j] < A[i', j])
           )
  requires A.Length0 >= 1 && A.Length1 >=1
  ensures forall i,j :: 0 <= i< A.Length0 && 0 <= j < A.Length1
                        ==> A[i, j] == val ==> (i, j) in r
{
  var i := A.Length0 - 1;
  var j := 0;
  r := [];
  while ((i > -1 && j < A.Length1))
    invariant -1 <= i < A.Length0 && 0 <= j <= A.Length1
    invariant forall i', j' ::
                0 <= i' < A.Length0 && 0 <= j' < A.Length1 && A[i', j'] == val
                ==> ((i', j') in r || (0 <= i' <= i && j <= j' < A.Length1))
    decreases i + A.Length1 - j
  {
    if val == A[i, j] {
      r := r + [(i, j)];
      i := i - 1;
      j := j + 1;
    }
    else if val > A[i, j] {
      r := r;
      j := j + 1;
      i := i;

    } else {
      r := r;
      i := i - 1;
      j := j;
    }
  }
  return r;
}
