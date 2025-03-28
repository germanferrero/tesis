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


method test_es_una_matriz_ordenada() {
  var A := new int[3,3];
  A[2,0], A[2,1], A[2,2] := 7, 8, 9;
  A[1,0], A[1,1], A[1,2] := 4, 5, 5;
  A[0,0], A[0,1], A[0,2] := 1, 2, 5;
  assert es_una_matriz_ordenada(A);
  A := new int[3,3];
  A[2,0], A[2,1], A[2,2] := 3, 8, 9;
  A[1,0], A[1,1], A[1,2] := 4, 5, 5;
  A[0,0], A[0,1], A[0,2] := 1, 2, 5;
  assert A[2,0] < A[1,0];
  assert !es_una_matriz_ordenada(A);
}

method test_busqueda_por_acorralamiento() {
  var A := new int[3,3];
  A[2,0], A[2,1], A[2,2] := 7, 8, 9;
  A[1,0], A[1,1], A[1,2] := 4, 5, 5;
  A[0,0], A[0,1], A[0,2] := 1, 2, 5;
  assert A[1,0] == 4;
  var x, y := busqueda_por_acorralamiento(A, 4);
  assert (x, y) == (1, 0);
  x, y := busqueda_por_acorralamiento(A, 5);
  assert (x, y) == (1,1)
         || (x, y) == (1,2)
         || (x, y) == (0,2);
}