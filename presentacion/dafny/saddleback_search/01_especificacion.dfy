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

method busqueda_por_acorralamiento(A: array2<int>, val: int)
  returns(x: int, y: int)
  requires es_una_matriz_ordenada(A)
  requires contiene_el_valor(A, val)
  ensures contiene_el_valor_en_la_posicion(A, val, x, y)