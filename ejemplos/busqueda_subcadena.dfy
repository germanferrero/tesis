predicate esta_en(s: string, w: string, k: int)
{
  0 < |w| <= |s| && 0 <= k <= |s| - |w| &&
  forall i: int :: k <= i < k + |w| ==> s[i] == w[i - k]
}

method test_esta_en_cuando_esta(){
  assert esta_en("casa", "casa", 0);
  assert esta_en("casa", "cas", 0);
  assert esta_en("casa", "ca", 0);
  assert esta_en("casa", "c", 0);
  assert esta_en("casa", "asa", 1);
  assert esta_en("casa", "as", 1);
  assert esta_en("casa", "a", 1);
  assert esta_en("casa", "sa", 2);
  assert esta_en("casa", "s", 2);
  assert esta_en("casa", "a", 3);
}

lemma si_esta_coincide_el_primer_caracter()
  ensures forall s:string, w: string, k: int ::
            (esta_en(s, w, k)) ==> s[k] == w[0]
{
}

method test_esta_en_cuando_no_esta(){
  assert !esta_en("casa", "d", 0) by {
    si_esta_coincide_el_primer_caracter();
  }
}


predicate invariante(s:string, w: string, i: int, k: int)
{
  i <= k &&
  esta_en(s, w, k)
}

method inicializacion(s: string, w: string, ghost k: int) returns (i: int)
  requires esta_en(s, w, k)
  ensures invariante(s, w, i, k)
{
  return 0;
}

method cuerpo(s: string, w: string, ghost k: int, i: int) returns (i': int)
  requires !esta_en(s, w, i)
  requires invariante(s, w, i, k)
  ensures invariante(s, w, i', k)
  ensures i' > i
{
  i' := i + 1;
}

method busqueda_subcadena(s: string, w: string) returns (k: int)
  requires exists j :: esta_en(s, w, j)
  ensures esta_en(s, w, k)
{
  ghost var gk: int :| esta_en(s, w, gk);
  var i: int;
  i := inicializacion(s, w, gk);
  while (!esta_en(s, w, i))
    decreases gk - i
    invariant invariante(s, w, i, gk)
  {
    i := cuerpo(s, w, gk, i);
  }
  return i;
}