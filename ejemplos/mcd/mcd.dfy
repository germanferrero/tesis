predicate es_el_mcd(d: int, m: int, n: int)
{
    0 < d <= n &&
    m % d == 0 &&
    n % d == 0 &&
    forall d' :: 
        (0 < d' <= n && m % d' == 0 && n % d' == 0)
            ==> d' <= d
}


method test_es_el_mcd_numeros_chicos(){
    assert es_el_mcd(1, 8, 3);
    assert !es_el_mcd(2, 8, 3);
    assert es_el_mcd(5, 2345, 5000);
    assert !es_el_mcd(4, 2345, 5000);
    assert es_el_mcd(1, 49163, 9113);
}

predicate invariante(d: int, m': int, n': int) {
    && es_el_mcd(d, m', n')
    && (m' % n' == 0 ==> d == n')
}

method inicializacion(ghost d: int, m: int, n: int) returns (m': int, n': int)
    requires 0 < n <= m
    requires es_el_mcd(d, m, n)
    ensures invariante(d, m', n')
{
    m' := m;
    n' := n;
}

lemma {:axiom} mcd_del_modulo(d:int, m:int, n:int)
    requires es_el_mcd(d, m, n)
    requires n > 0
    ensures es_el_mcd(d, n, m % n)

method cuerpo(ghost d: int, m: int, n: int) returns (m': int, n': int)
    requires invariante(d, m, n)
    ensures invariante(d, m', n')
    ensures m' % n' < m % n
{
    assert es_el_mcd(d, n, m % n) by {
        mcd_del_modulo(d, m, n);
    }
    var r := m % n;
    m' := n;
    n' := r;
}

lemma {:axiom} existe_un_mcd(m:int, n:int)
    ensures exists d: int :: es_el_mcd(d, m, n)

method maximo_comun_divisor(m: int, n: int) returns (mcd: int)
    requires 0 < n <= m
    ensures es_el_mcd(mcd, m, n)
{
    assert exists d: int :: es_el_mcd(d, m, n) by {
        existe_un_mcd(m, n);
    }
    ghost var d: int :| es_el_mcd(d, m, n);
    var m': int, n': int;
    m', n' := inicializacion(d, m, n);
    while (m' % n' > 0)
        decreases m' % n'
        invariant invariante(d, m', n')
    {
         m', n' := cuerpo(d, m', n');
    }
    return n';
}