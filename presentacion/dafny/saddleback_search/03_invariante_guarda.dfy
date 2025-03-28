predicate es_una_matriz_ordenada(A: array2<int>)
  reads A
{
  (forall i, j, j' ::
    (0 <= i < A.Length0 && 0 <= j < j' < A.Length1 ==> A[i,j] <= A[i, j']))
  &&
  (forall i, i', j ::
    (0 <= j < A.Length1 && 0 <= i < i' < A.Length0 ==> A[i,j] <= A[i', j])
  )
}

predicate contiene_el_valor(A: array2<int>, val: int)
  reads A
{
  exists x, y :: 0 <= x < A.Length0 && 0 <= y < A.Length1 && A[x, y] == val
}

predicate contiene_el_valor_en_la_posicion(A: array2<int>, val: int, x: int, y: int)
  reads A
{
  0 <= x < A.Length0 && 0 <= y < A.Length1
  && A[x, y] == val
}

predicate invariante(A: array2<int>, i: int, j: int, val: int)
  reads A
{
  es_una_matriz_ordenada(A)
  && 0 <= i < A.Length0 && 0 <= j < A.Length1
  && exists x, y :: 0 <= x <= i && j <= y < A.Length1 && A[x, y] == val
}

method busqueda_por_acorralamiento(A: array2<int>, val: int)
  returns(x: int, y: int)
  requires es_una_matriz_ordenada(A)
  requires contiene_el_valor(A, val)
  ensures contiene_el_valor_en_la_posicion(A, val, x, y)
{
  var i, j := *, *;
  assume invariante(A, i, j, val);
  while (A[i,j] != val)
    invariant invariante(A, i, j, val)
  return i, j;
}

// i, j := my_while(A, i, j, val);
// method my_while(A: array2<int>, i: int, j:int , val: int)
//   returns(i': int, j':int )
//   requires invariante(A, i, j, val)
//   ensures invariante(A, i', j', val) && A[i',j'] == val