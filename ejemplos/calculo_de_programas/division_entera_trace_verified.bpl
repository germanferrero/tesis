New lambda: (lambda $o: ref, $f: Field :: 
  $o != null && $Unbox_982(read($Heap, $o, alloc)) ==> false)
Desugaring of lambda expressions produced 1 functions and 1 axioms:
// auto-generated lambda function
function lambda#0(l#0: ref, l#1: [ref][Field]Box, l#2: Field, l#3: bool) : [ref,Field]bool
uses {
axiom (forall l#0: ref, l#1: [ref][Field]Box, l#2: Field, l#3: bool, $o: ref, $f: Field :: { lambda#0(l#0, l#1, l#2, l#3)[$o, $f] } lambda#0(l#0, l#1, l#2, l#3)[$o, $f] == ($o != l#0 && $Unbox_982(read(l#1, $o, l#2)) ==> l#3));
}
axiom (forall l#0: ref, l#1: [ref][Field]Box, l#2: Field, l#3: bool, $o: ref, $f: Field :: { lambda#0(l#0, l#1, l#2, l#3)[$o, $f] } lambda#0(l#0, l#1, l#2, l#3)[$o, $f] == ($o != l#0 && $Unbox_982(read(l#1, $o, l#2)) ==> l#3));

original implementation
implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "division_entera (correctness)"} Impl$$_module.__default.division__entera(x#0: int, y#0: int) returns (defass#q#0: bool, q#0: int, defass#r#0: bool, r#0: int, $_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var $PreLoopHeap$loop#0: [ref][Field]Box;
  var preLoop$loop#0$defass#r#0: bool;
  var preLoop$loop#0$defass#q#0: bool;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;


  anon0:
    $_ModifiesFrame := lambda#0(null, $Heap, alloc, false);
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(4,0): initial state"} true;
    $_reverifyPost := false;
    assume true;
    assume true;
    q#0 := LitInt(0);
    defass#q#0 := true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(5,10)"} true;
    assume true;
    assume true;
    r#0 := x#0;
    defass#r#0 := true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(6,10)"} true;
    $PreLoopHeap$loop#0 := $Heap;
    preLoop$loop#0$defass#r#0 := defass#r#0;
    preLoop$loop#0$defass#q#0 := defass#q#0;
    $decr_init$loop#00 := r#0 - y#0;
    havoc $w$loop#0;
    goto anon9_LoopHead;

  anon9_LoopHead:
    assume true;
    assert {:id "id20"} $w$loop#0 ==> x#0 == Mul(q#0, y#0) + r#0;
    assert {:id "id21"} $w$loop#0 ==> r#0 >= LitInt(0);
    assume (forall $o: ref :: { $Heap[$o] } $o != null && $Unbox_982(read(old($Heap), $o, alloc)) ==> $Heap[$o] == $PreLoopHeap$loop#0[$o]);
    assume $HeapSucc($PreLoopHeap$loop#0, $Heap);
    assume (forall $o: ref, $f: Field :: { read($Heap, $o, $f) } $o != null && $Unbox_982(read($PreLoopHeap$loop#0, $o, alloc)) ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_ModifiesFrame[$o, $f]);
    assume preLoop$loop#0$defass#r#0 ==> defass#r#0;
    assume preLoop$loop#0$defass#q#0 ==> defass#q#0;
    assume r#0 - y#0 <= $decr_init$loop#00;
    goto anon9_LoopDone, anon9_LoopBody;

  anon9_LoopBody:
    assume {:partition} true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(7,4): after some loop iterations"} true;
    goto anon10_Then, anon10_Else;

  anon10_Else:
    assume {:partition} $w$loop#0;
    assert {:id "id23"} defass#r#0;
    assume true;
    goto anon12_Then, anon12_Else;

  anon12_Else:
    assume {:partition} r#0 >= y#0;
    $decr$loop#00 := r#0 - y#0;
    assume true;
    assert {:id "id24"} defass#q#0;
    assume true;
    q#0 := q#0 + 1;
    defass#q#0 := true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(11,18)"} true;
    assume true;
    assert {:id "id26"} defass#r#0;
    assume true;
    r#0 := r#0 - y#0;
    defass#r#0 := true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(12,18)"} true;
    assert {:id "id28"} 0 <= $decr$loop#00 || r#0 - y#0 == $decr$loop#00;
    assert {:id "id29"} r#0 - y#0 < $decr$loop#00;
    assume true;
    goto anon9_LoopHead;

  anon12_Then:
    assume {:partition} y#0 > r#0;
    goto anon8;

  anon8:
    assert {:id "id30"} defass#q#0;
    assert {:id "id31"} defass#r#0;
    return;

  anon10_Then:
    assume {:partition} !$w$loop#0;
    assert {:id "id16"} defass#q#0;
    assert {:id "id17"} defass#r#0;
    goto anon11_Then, anon11_Else;

  anon11_Else:
    assume {:partition} x#0 != Mul(q#0, y#0) + r#0;
    goto anon4;

  anon4:
    assume true;
    assume {:id "id19"} x#0 == Mul(q#0, y#0) + r#0 && r#0 >= LitInt(0);
    assert {:id "id22"} defass#r#0;
    assume true;
    assume false;
    return;

  anon11_Then:
    assume {:partition} x#0 == Mul(q#0, y#0) + r#0;
    assert {:id "id18"} defass#r#0;
    goto anon4;

  anon9_LoopDone:
    assume {:partition} !true;
    goto anon8;
}


after desugaring sugared commands like procedure calls
implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "division_entera (correctness)"} Impl$$_module.__default.division__entera(x#0: int, y#0: int) returns (defass#q#0: bool, q#0: int, defass#r#0: bool, r#0: int, $_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var $PreLoopHeap$loop#0: [ref][Field]Box;
  var preLoop$loop#0$defass#r#0: bool;
  var preLoop$loop#0$defass#q#0: bool;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;


  anon0:
    $_ModifiesFrame := lambda#0(null, $Heap, alloc, false);
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(4,0): initial state"} true;
    $_reverifyPost := false;
    assume true;
    assume true;
    q#0 := LitInt(0);
    defass#q#0 := true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(5,10)"} true;
    assume true;
    assume true;
    r#0 := x#0;
    defass#r#0 := true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(6,10)"} true;
    $PreLoopHeap$loop#0 := $Heap;
    preLoop$loop#0$defass#r#0 := defass#r#0;
    preLoop$loop#0$defass#q#0 := defass#q#0;
    $decr_init$loop#00 := r#0 - y#0;
    havoc $w$loop#0;
    goto anon9_LoopHead;

  anon9_LoopHead:
    assume true;
    assert {:id "id20"} $w$loop#0 ==> x#0 == Mul(q#0, y#0) + r#0;
    assert {:id "id21"} $w$loop#0 ==> r#0 >= LitInt(0);
    assume (forall $o: ref :: { $Heap[$o] } $o != null && $Unbox_982(read(old($Heap), $o, alloc)) ==> $Heap[$o] == $PreLoopHeap$loop#0[$o]);
    assume $HeapSucc($PreLoopHeap$loop#0, $Heap);
    assume (forall $o: ref, $f: Field :: { read($Heap, $o, $f) } $o != null && $Unbox_982(read($PreLoopHeap$loop#0, $o, alloc)) ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_ModifiesFrame[$o, $f]);
    assume preLoop$loop#0$defass#r#0 ==> defass#r#0;
    assume preLoop$loop#0$defass#q#0 ==> defass#q#0;
    assume r#0 - y#0 <= $decr_init$loop#00;
    goto anon9_LoopDone, anon9_LoopBody;

  anon9_LoopBody:
    assume {:partition} true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(7,4): after some loop iterations"} true;
    goto anon10_Then, anon10_Else;

  anon10_Else:
    assume {:partition} $w$loop#0;
    assert {:id "id23"} defass#r#0;
    assume true;
    goto anon12_Then, anon12_Else;

  anon12_Else:
    assume {:partition} r#0 >= y#0;
    $decr$loop#00 := r#0 - y#0;
    assume true;
    assert {:id "id24"} defass#q#0;
    assume true;
    q#0 := q#0 + 1;
    defass#q#0 := true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(11,18)"} true;
    assume true;
    assert {:id "id26"} defass#r#0;
    assume true;
    r#0 := r#0 - y#0;
    defass#r#0 := true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(12,18)"} true;
    assert {:id "id28"} 0 <= $decr$loop#00 || r#0 - y#0 == $decr$loop#00;
    assert {:id "id29"} r#0 - y#0 < $decr$loop#00;
    assume true;
    goto anon9_LoopHead;

  anon12_Then:
    assume {:partition} y#0 > r#0;
    goto anon8;

  anon8:
    assert {:id "id30"} defass#q#0;
    assert {:id "id31"} defass#r#0;
    return;

  anon10_Then:
    assume {:partition} !$w$loop#0;
    assert {:id "id16"} defass#q#0;
    assert {:id "id17"} defass#r#0;
    goto anon11_Then, anon11_Else;

  anon11_Else:
    assume {:partition} x#0 != Mul(q#0, y#0) + r#0;
    goto anon4;

  anon4:
    assume true;
    assume {:id "id19"} x#0 == Mul(q#0, y#0) + r#0 && r#0 >= LitInt(0);
    assert {:id "id22"} defass#r#0;
    assume true;
    assume false;
    return;

  anon11_Then:
    assume {:partition} x#0 == Mul(q#0, y#0) + r#0;
    assert {:id "id18"} defass#r#0;
    goto anon4;

  anon9_LoopDone:
    assume {:partition} !true;
    goto anon8;
}


after conversion into a DAG
implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "division_entera (correctness)"} Impl$$_module.__default.division__entera(x#0: int, y#0: int) returns (defass#q#0: bool, q#0: int, defass#r#0: bool, r#0: int, $_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var $PreLoopHeap$loop#0: [ref][Field]Box;
  var preLoop$loop#0$defass#r#0: bool;
  var preLoop$loop#0$defass#q#0: bool;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;


  0:
    goto anon0;

  anon0:
    $_ModifiesFrame := lambda#0(null, $Heap, alloc, false);
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(4,0): initial state"} true;
    $_reverifyPost := false;
    assume true;
    assume true;
    q#0 := LitInt(0);
    defass#q#0 := true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(5,10)"} true;
    assume true;
    assume true;
    r#0 := x#0;
    defass#r#0 := true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(6,10)"} true;
    $PreLoopHeap$loop#0 := $Heap;
    preLoop$loop#0$defass#r#0 := defass#r#0;
    preLoop$loop#0$defass#q#0 := defass#q#0;
    $decr_init$loop#00 := r#0 - y#0;
    havoc $w$loop#0;
    assert {:id "id20$established"} {:id "id20"} $w$loop#0 ==> x#0 == Mul(q#0, y#0) + r#0;
    assert {:id "id21$established"} {:id "id21"} $w$loop#0 ==> r#0 >= LitInt(0);
    goto anon9_LoopHead;

  anon9_LoopHead:
    havoc $decr$loop#00, q#0, defass#q#0, r#0, defass#r#0;
    assume true;
    assume {:id "id20$assume_in_body"} $w$loop#0 ==> x#0 == Mul(q#0, y#0) + r#0;
    assume {:id "id21$assume_in_body"} $w$loop#0 ==> r#0 >= LitInt(0);
    assume (forall $o: ref :: { $Heap[$o] } $o != null && $Unbox_982(read(old($Heap), $o, alloc)) ==> $Heap[$o] == $PreLoopHeap$loop#0[$o]);
    assume $HeapSucc($PreLoopHeap$loop#0, $Heap);
    assume (forall $o: ref, $f: Field :: { read($Heap, $o, $f) } $o != null && $Unbox_982(read($PreLoopHeap$loop#0, $o, alloc)) ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_ModifiesFrame[$o, $f]);
    assume preLoop$loop#0$defass#r#0 ==> defass#r#0;
    assume preLoop$loop#0$defass#q#0 ==> defass#q#0;
    assume r#0 - y#0 <= $decr_init$loop#00;
    goto anon9_LoopDone, anon9_LoopBody;

  anon9_LoopBody:
    assume {:partition} true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(7,4): after some loop iterations"} true;
    goto anon10_Then, anon10_Else;

  anon10_Else:
    assume {:partition} $w$loop#0;
    assert {:id "id23"} defass#r#0;
    assume true;
    goto anon12_Then, anon12_Else;

  anon12_Else:
    assume {:partition} r#0 >= y#0;
    $decr$loop#00 := r#0 - y#0;
    assume true;
    assert {:id "id24"} defass#q#0;
    assume true;
    q#0 := q#0 + 1;
    defass#q#0 := true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(11,18)"} true;
    assume true;
    assert {:id "id26"} defass#r#0;
    assume true;
    r#0 := r#0 - y#0;
    defass#r#0 := true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(12,18)"} true;
    assert {:id "id28"} 0 <= $decr$loop#00 || r#0 - y#0 == $decr$loop#00;
    assert {:id "id29"} r#0 - y#0 < $decr$loop#00;
    assume true;
    assert {:id "id20$maintained"} {:id "id20"} $w$loop#0 ==> x#0 == Mul(q#0, y#0) + r#0;
    assert {:id "id21$maintained"} {:id "id21"} $w$loop#0 ==> r#0 >= LitInt(0);
    assume false;
    return;

  anon12_Then:
    assume {:partition} y#0 > r#0;
    goto anon8;

  anon8:
    assert {:id "id30"} defass#q#0;
    assert {:id "id31"} defass#r#0;
    return;

  anon10_Then:
    assume {:partition} !$w$loop#0;
    assert {:id "id16"} defass#q#0;
    assert {:id "id17"} defass#r#0;
    goto anon11_Then, anon11_Else;

  anon11_Else:
    assume {:partition} x#0 != Mul(q#0, y#0) + r#0;
    goto anon4;

  anon4:
    assume true;
    assume {:id "id19"} x#0 == Mul(q#0, y#0) + r#0 && r#0 >= LitInt(0);
    assert {:id "id22"} defass#r#0;
    assume true;
    assume false;
    return;

  anon11_Then:
    assume {:partition} x#0 == Mul(q#0, y#0) + r#0;
    assert {:id "id18"} defass#r#0;
    goto anon4;

  anon9_LoopDone:
    assume {:partition} !true;
    goto anon8;
}


after creating a unified exit block
implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "division_entera (correctness)"} Impl$$_module.__default.division__entera(x#0: int, y#0: int) returns (defass#q#0: bool, q#0: int, defass#r#0: bool, r#0: int, $_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var $PreLoopHeap$loop#0: [ref][Field]Box;
  var preLoop$loop#0$defass#r#0: bool;
  var preLoop$loop#0$defass#q#0: bool;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;


  0:
    goto anon0;

  anon0:
    $_ModifiesFrame := lambda#0(null, $Heap, alloc, false);
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(4,0): initial state"} true;
    $_reverifyPost := false;
    assume true;
    assume true;
    q#0 := LitInt(0);
    defass#q#0 := true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(5,10)"} true;
    assume true;
    assume true;
    r#0 := x#0;
    defass#r#0 := true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(6,10)"} true;
    $PreLoopHeap$loop#0 := $Heap;
    preLoop$loop#0$defass#r#0 := defass#r#0;
    preLoop$loop#0$defass#q#0 := defass#q#0;
    $decr_init$loop#00 := r#0 - y#0;
    havoc $w$loop#0;
    assert {:id "id20$established"} {:id "id20"} $w$loop#0 ==> x#0 == Mul(q#0, y#0) + r#0;
    assert {:id "id21$established"} {:id "id21"} $w$loop#0 ==> r#0 >= LitInt(0);
    goto anon9_LoopHead;

  anon9_LoopHead:
    havoc $decr$loop#00, q#0, defass#q#0, r#0, defass#r#0;
    assume true;
    assume {:id "id20$assume_in_body"} $w$loop#0 ==> x#0 == Mul(q#0, y#0) + r#0;
    assume {:id "id21$assume_in_body"} $w$loop#0 ==> r#0 >= LitInt(0);
    assume (forall $o: ref :: { $Heap[$o] } $o != null && $Unbox_982(read(old($Heap), $o, alloc)) ==> $Heap[$o] == $PreLoopHeap$loop#0[$o]);
    assume $HeapSucc($PreLoopHeap$loop#0, $Heap);
    assume (forall $o: ref, $f: Field :: { read($Heap, $o, $f) } $o != null && $Unbox_982(read($PreLoopHeap$loop#0, $o, alloc)) ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_ModifiesFrame[$o, $f]);
    assume preLoop$loop#0$defass#r#0 ==> defass#r#0;
    assume preLoop$loop#0$defass#q#0 ==> defass#q#0;
    assume r#0 - y#0 <= $decr_init$loop#00;
    goto anon9_LoopDone, anon9_LoopBody;

  anon9_LoopBody:
    assume {:partition} true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(7,4): after some loop iterations"} true;
    goto anon10_Then, anon10_Else;

  anon10_Else:
    assume {:partition} $w$loop#0;
    assert {:id "id23"} defass#r#0;
    assume true;
    goto anon12_Then, anon12_Else;

  anon12_Else:
    assume {:partition} r#0 >= y#0;
    $decr$loop#00 := r#0 - y#0;
    assume true;
    assert {:id "id24"} defass#q#0;
    assume true;
    q#0 := q#0 + 1;
    defass#q#0 := true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(11,18)"} true;
    assume true;
    assert {:id "id26"} defass#r#0;
    assume true;
    r#0 := r#0 - y#0;
    defass#r#0 := true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(12,18)"} true;
    assert {:id "id28"} 0 <= $decr$loop#00 || r#0 - y#0 == $decr$loop#00;
    assert {:id "id29"} r#0 - y#0 < $decr$loop#00;
    assume true;
    assert {:id "id20$maintained"} {:id "id20"} $w$loop#0 ==> x#0 == Mul(q#0, y#0) + r#0;
    assert {:id "id21$maintained"} {:id "id21"} $w$loop#0 ==> r#0 >= LitInt(0);
    assume false;
    goto GeneratedUnifiedExit;

  anon12_Then:
    assume {:partition} y#0 > r#0;
    goto anon8;

  anon8:
    assert {:id "id30"} defass#q#0;
    assert {:id "id31"} defass#r#0;
    goto GeneratedUnifiedExit;

  anon10_Then:
    assume {:partition} !$w$loop#0;
    assert {:id "id16"} defass#q#0;
    assert {:id "id17"} defass#r#0;
    goto anon11_Then, anon11_Else;

  anon11_Else:
    assume {:partition} x#0 != Mul(q#0, y#0) + r#0;
    goto anon4;

  anon4:
    assume true;
    assume {:id "id19"} x#0 == Mul(q#0, y#0) + r#0 && r#0 >= LitInt(0);
    assert {:id "id22"} defass#r#0;
    assume true;
    assume false;
    goto GeneratedUnifiedExit;

  anon11_Then:
    assume {:partition} x#0 == Mul(q#0, y#0) + r#0;
    assert {:id "id18"} defass#r#0;
    goto anon4;

  anon9_LoopDone:
    assume {:partition} !true;
    goto anon8;

  GeneratedUnifiedExit:
    return;
}


after inserting pre- and post-conditions
implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "division_entera (correctness)"} Impl$$_module.__default.division__entera(x#0: int, y#0: int) returns (defass#q#0: bool, q#0: int, defass#r#0: bool, r#0: int, $_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var $PreLoopHeap$loop#0: [ref][Field]Box;
  var preLoop$loop#0$defass#r#0: bool;
  var preLoop$loop#0$defass#q#0: bool;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;


  PreconditionGeneratedEntry:
    assume $IsGoodHeap($Heap) && $IsHeapAnchor($Heap);
    assume 0 == $FunctionContextHeight;
    assume {:id "id9"} x#0 > 0;
    assume {:id "id10"} y#0 > 0;
    goto 0;

  anon0:
    $_ModifiesFrame := lambda#0(null, $Heap, alloc, false);
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(4,0): initial state"} true;
    $_reverifyPost := false;
    assume true;
    assume true;
    q#0 := LitInt(0);
    defass#q#0 := true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(5,10)"} true;
    assume true;
    assume true;
    r#0 := x#0;
    defass#r#0 := true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(6,10)"} true;
    $PreLoopHeap$loop#0 := $Heap;
    preLoop$loop#0$defass#r#0 := defass#r#0;
    preLoop$loop#0$defass#q#0 := defass#q#0;
    $decr_init$loop#00 := r#0 - y#0;
    havoc $w$loop#0;
    assert {:id "id20$established"} {:id "id20"} $w$loop#0 ==> x#0 == Mul(q#0, y#0) + r#0;
    assert {:id "id21$established"} {:id "id21"} $w$loop#0 ==> r#0 >= LitInt(0);
    goto anon9_LoopHead;

  anon9_LoopHead:
    havoc $decr$loop#00, q#0, defass#q#0, r#0, defass#r#0;
    assume true;
    assume {:id "id20$assume_in_body"} $w$loop#0 ==> x#0 == Mul(q#0, y#0) + r#0;
    assume {:id "id21$assume_in_body"} $w$loop#0 ==> r#0 >= LitInt(0);
    assume (forall $o: ref :: { $Heap[$o] } $o != null && $Unbox_982(read(old($Heap), $o, alloc)) ==> $Heap[$o] == $PreLoopHeap$loop#0[$o]);
    assume $HeapSucc($PreLoopHeap$loop#0, $Heap);
    assume (forall $o: ref, $f: Field :: { read($Heap, $o, $f) } $o != null && $Unbox_982(read($PreLoopHeap$loop#0, $o, alloc)) ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_ModifiesFrame[$o, $f]);
    assume preLoop$loop#0$defass#r#0 ==> defass#r#0;
    assume preLoop$loop#0$defass#q#0 ==> defass#q#0;
    assume r#0 - y#0 <= $decr_init$loop#00;
    goto anon9_LoopDone, anon9_LoopBody;

  anon9_LoopBody:
    assume {:partition} true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(7,4): after some loop iterations"} true;
    goto anon10_Then, anon10_Else;

  anon10_Else:
    assume {:partition} $w$loop#0;
    assert {:id "id23"} defass#r#0;
    assume true;
    goto anon12_Then, anon12_Else;

  anon12_Else:
    assume {:partition} r#0 >= y#0;
    $decr$loop#00 := r#0 - y#0;
    assume true;
    assert {:id "id24"} defass#q#0;
    assume true;
    q#0 := q#0 + 1;
    defass#q#0 := true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(11,18)"} true;
    assume true;
    assert {:id "id26"} defass#r#0;
    assume true;
    r#0 := r#0 - y#0;
    defass#r#0 := true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(12,18)"} true;
    assert {:id "id28"} 0 <= $decr$loop#00 || r#0 - y#0 == $decr$loop#00;
    assert {:id "id29"} r#0 - y#0 < $decr$loop#00;
    assume true;
    assert {:id "id20$maintained"} {:id "id20"} $w$loop#0 ==> x#0 == Mul(q#0, y#0) + r#0;
    assert {:id "id21$maintained"} {:id "id21"} $w$loop#0 ==> r#0 >= LitInt(0);
    assume false;
    goto GeneratedUnifiedExit;

  anon12_Then:
    assume {:partition} y#0 > r#0;
    goto anon8;

  anon8:
    assert {:id "id30"} defass#q#0;
    assert {:id "id31"} defass#r#0;
    goto GeneratedUnifiedExit;

  anon10_Then:
    assume {:partition} !$w$loop#0;
    assert {:id "id16"} defass#q#0;
    assert {:id "id17"} defass#r#0;
    goto anon11_Then, anon11_Else;

  anon11_Else:
    assume {:partition} x#0 != Mul(q#0, y#0) + r#0;
    goto anon4;

  anon4:
    assume true;
    assume {:id "id19"} x#0 == Mul(q#0, y#0) + r#0 && r#0 >= LitInt(0);
    assert {:id "id22"} defass#r#0;
    assume true;
    assume false;
    goto GeneratedUnifiedExit;

  anon11_Then:
    assume {:partition} x#0 == Mul(q#0, y#0) + r#0;
    assert {:id "id18"} defass#r#0;
    goto anon4;

  anon9_LoopDone:
    assume {:partition} !true;
    goto anon8;

  GeneratedUnifiedExit:
    assert {:id "id11"} x#0 == Mul(q#0, y#0) + r#0;
    assert {:id "id12"} LitInt(0) <= r#0;
    assert {:id "id13"} r#0 < y#0;
    return;

  0:
    goto anon0;
}


after adding empty blocks as needed to catch join assumptions
implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "division_entera (correctness)"} Impl$$_module.__default.division__entera(x#0: int, y#0: int) returns (defass#q#0: bool, q#0: int, defass#r#0: bool, r#0: int, $_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var $PreLoopHeap$loop#0: [ref][Field]Box;
  var preLoop$loop#0$defass#r#0: bool;
  var preLoop$loop#0$defass#q#0: bool;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;


  PreconditionGeneratedEntry:
    assume $IsGoodHeap($Heap) && $IsHeapAnchor($Heap);
    assume 0 == $FunctionContextHeight;
    assume {:id "id9"} x#0 > 0;
    assume {:id "id10"} y#0 > 0;
    goto 0;

  anon0:
    $_ModifiesFrame := lambda#0(null, $Heap, alloc, false);
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(4,0): initial state"} true;
    $_reverifyPost := false;
    assume true;
    assume true;
    q#0 := LitInt(0);
    defass#q#0 := true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(5,10)"} true;
    assume true;
    assume true;
    r#0 := x#0;
    defass#r#0 := true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(6,10)"} true;
    $PreLoopHeap$loop#0 := $Heap;
    preLoop$loop#0$defass#r#0 := defass#r#0;
    preLoop$loop#0$defass#q#0 := defass#q#0;
    $decr_init$loop#00 := r#0 - y#0;
    havoc $w$loop#0;
    assert {:id "id20$established"} {:id "id20"} $w$loop#0 ==> x#0 == Mul(q#0, y#0) + r#0;
    assert {:id "id21$established"} {:id "id21"} $w$loop#0 ==> r#0 >= LitInt(0);
    goto anon9_LoopHead;

  anon9_LoopHead:
    havoc $decr$loop#00, q#0, defass#q#0, r#0, defass#r#0;
    assume true;
    assume {:id "id20$assume_in_body"} $w$loop#0 ==> x#0 == Mul(q#0, y#0) + r#0;
    assume {:id "id21$assume_in_body"} $w$loop#0 ==> r#0 >= LitInt(0);
    assume (forall $o: ref :: { $Heap[$o] } $o != null && $Unbox_982(read(old($Heap), $o, alloc)) ==> $Heap[$o] == $PreLoopHeap$loop#0[$o]);
    assume $HeapSucc($PreLoopHeap$loop#0, $Heap);
    assume (forall $o: ref, $f: Field :: { read($Heap, $o, $f) } $o != null && $Unbox_982(read($PreLoopHeap$loop#0, $o, alloc)) ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_ModifiesFrame[$o, $f]);
    assume preLoop$loop#0$defass#r#0 ==> defass#r#0;
    assume preLoop$loop#0$defass#q#0 ==> defass#q#0;
    assume r#0 - y#0 <= $decr_init$loop#00;
    goto anon9_LoopDone, anon9_LoopBody;

  anon9_LoopBody:
    assume {:partition} true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(7,4): after some loop iterations"} true;
    goto anon10_Then, anon10_Else;

  anon10_Else:
    assume {:partition} $w$loop#0;
    assert {:id "id23"} defass#r#0;
    assume true;
    goto anon12_Then, anon12_Else;

  anon12_Else:
    assume {:partition} r#0 >= y#0;
    $decr$loop#00 := r#0 - y#0;
    assume true;
    assert {:id "id24"} defass#q#0;
    assume true;
    q#0 := q#0 + 1;
    defass#q#0 := true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(11,18)"} true;
    assume true;
    assert {:id "id26"} defass#r#0;
    assume true;
    r#0 := r#0 - y#0;
    defass#r#0 := true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(12,18)"} true;
    assert {:id "id28"} 0 <= $decr$loop#00 || r#0 - y#0 == $decr$loop#00;
    assert {:id "id29"} r#0 - y#0 < $decr$loop#00;
    assume true;
    assert {:id "id20$maintained"} {:id "id20"} $w$loop#0 ==> x#0 == Mul(q#0, y#0) + r#0;
    assert {:id "id21$maintained"} {:id "id21"} $w$loop#0 ==> r#0 >= LitInt(0);
    assume false;
    goto GeneratedUnifiedExit;

  anon12_Then:
    assume {:partition} y#0 > r#0;
    goto anon8;

  anon8:
    assert {:id "id30"} defass#q#0;
    assert {:id "id31"} defass#r#0;
    goto GeneratedUnifiedExit;

  anon10_Then:
    assume {:partition} !$w$loop#0;
    assert {:id "id16"} defass#q#0;
    assert {:id "id17"} defass#r#0;
    goto anon11_Then, anon11_Else;

  anon11_Else:
    assume {:partition} x#0 != Mul(q#0, y#0) + r#0;
    goto anon4;

  anon4:
    assume true;
    assume {:id "id19"} x#0 == Mul(q#0, y#0) + r#0 && r#0 >= LitInt(0);
    assert {:id "id22"} defass#r#0;
    assume true;
    assume false;
    goto GeneratedUnifiedExit;

  anon11_Then:
    assume {:partition} x#0 == Mul(q#0, y#0) + r#0;
    assert {:id "id18"} defass#r#0;
    goto anon4;

  anon9_LoopDone:
    assume {:partition} !true;
    goto anon8;

  GeneratedUnifiedExit:
    assert {:id "id11"} x#0 == Mul(q#0, y#0) + r#0;
    assert {:id "id12"} LitInt(0) <= r#0;
    assert {:id "id13"} r#0 < y#0;
    return;

  0:
    goto anon0;
}


after conversion to passive commands
implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "division_entera (correctness)"} Impl$$_module.__default.division__entera(x#0: int, y#0: int) returns (defass#q#0: bool, q#0: int, defass#r#0: bool, r#0: int, $_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var $PreLoopHeap$loop#0: [ref][Field]Box;
  var preLoop$loop#0$defass#r#0: bool;
  var preLoop$loop#0$defass#q#0: bool;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;
  var $_ModifiesFrame#AT#0: [ref,Field]bool;
  var q#0#AT#0: int;
  var $decr_init$loop#00#AT#0: int;
  var $w$loop#0#AT#0: bool;
  var $decr$loop#00#AT#0: int;
  var q#0#AT#1: int;
  var defass#q#0#AT#0: bool;
  var r#0#AT#0: int;
  var defass#r#0#AT#0: bool;
  var $decr$loop#00#AT#1: int;
  var q#0#AT#2: int;
  var r#0#AT#1: int;
  var q#0#AT#3: int;
  var r#0#AT#2: int;


  PreconditionGeneratedEntry:
    assume $IsGoodHeap($Heap) && $IsHeapAnchor($Heap);
    assume 0 == $FunctionContextHeight;
    assume {:id "id9"} x#0 > 0;
    assume {:id "id10"} y#0 > 0;
    goto 0;

  anon0:
    assume $_ModifiesFrame#AT#0 == lambda#0(null, $Heap, alloc, false);
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(4,0): initial state"} true;
    assume true;
    assume true;
    assume q#0#AT#0 == LitInt(0);
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(5,10)"} true;
    assume true;
    assume true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(6,10)"} true;
    assume $decr_init$loop#00#AT#0 == x#0 - y#0;
    assert {:id "id20$established"} {:id "id20"} $w$loop#0#AT#0 ==> x#0 == Mul(q#0#AT#0, y#0) + x#0;
    assert {:id "id21$established"} {:id "id21"} $w$loop#0#AT#0 ==> x#0 >= LitInt(0);
    goto anon9_LoopHead;

  anon9_LoopHead:
    assume true;
    assume {:id "id20$assume_in_body"} $w$loop#0#AT#0 ==> x#0 == Mul(q#0#AT#1, y#0) + r#0#AT#0;
    assume {:id "id21$assume_in_body"} $w$loop#0#AT#0 ==> r#0#AT#0 >= LitInt(0);
    assume (forall $o: ref :: { $Heap[$o] } $o != null && $Unbox_982(read($Heap, $o, alloc)) ==> $Heap[$o] == $Heap[$o]);
    assume $HeapSucc($Heap, $Heap);
    assume (forall $o: ref, $f: Field :: { read($Heap, $o, $f) } $o != null && $Unbox_982(read($Heap, $o, alloc)) ==> read($Heap, $o, $f) == read($Heap, $o, $f) || $_ModifiesFrame#AT#0[$o, $f]);
    assume true ==> defass#r#0#AT#0;
    assume true ==> defass#q#0#AT#0;
    assume r#0#AT#0 - y#0 <= $decr_init$loop#00#AT#0;
    goto anon9_LoopDone, anon9_LoopBody;

  anon9_LoopBody:
    assume {:partition} true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(7,4): after some loop iterations"} true;
    goto anon10_Then, anon10_Else;

  anon10_Else:
    assume {:partition} $w$loop#0#AT#0;
    assert {:id "id23"} defass#r#0#AT#0;
    assume true;
    goto anon12_Then, anon12_Else;

  anon12_Else:
    assume {:partition} r#0#AT#0 >= y#0;
    assume $decr$loop#00#AT#1 == r#0#AT#0 - y#0;
    assume true;
    assert {:id "id24"} defass#q#0#AT#0;
    assume true;
    assume q#0#AT#2 == q#0#AT#1 + 1;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(11,18)"} true;
    assume true;
    assert {:id "id26"} defass#r#0#AT#0;
    assume true;
    assume r#0#AT#1 == r#0#AT#0 - y#0;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(12,18)"} true;
    assert {:id "id28"} 0 <= $decr$loop#00#AT#1 || r#0#AT#1 - y#0 == $decr$loop#00#AT#1;
    assert {:id "id29"} r#0#AT#1 - y#0 < $decr$loop#00#AT#1;
    assume true;
    assert {:id "id20$maintained"} {:id "id20"} $w$loop#0#AT#0 ==> x#0 == Mul(q#0#AT#2, y#0) + r#0#AT#1;
    assert {:id "id21$maintained"} {:id "id21"} $w$loop#0#AT#0 ==> r#0#AT#1 >= LitInt(0);
    assume false;
    assume q#0#AT#3 == q#0#AT#2;
    assume r#0#AT#2 == r#0#AT#1;
    goto GeneratedUnifiedExit;

  anon12_Then:
    assume {:partition} y#0 > r#0#AT#0;
    goto anon8;

  anon8:
    assert {:id "id30"} defass#q#0#AT#0;
    assert {:id "id31"} defass#r#0#AT#0;
    assume q#0#AT#3 == q#0#AT#1;
    assume r#0#AT#2 == r#0#AT#0;
    goto GeneratedUnifiedExit;

  anon10_Then:
    assume {:partition} !$w$loop#0#AT#0;
    assert {:id "id16"} defass#q#0#AT#0;
    assert {:id "id17"} defass#r#0#AT#0;
    goto anon11_Then, anon11_Else;

  anon11_Else:
    assume {:partition} x#0 != Mul(q#0#AT#1, y#0) + r#0#AT#0;
    goto anon4;

  anon4:
    assume true;
    assume {:id "id19"} x#0 == Mul(q#0#AT#1, y#0) + r#0#AT#0 && r#0#AT#0 >= LitInt(0);
    assert {:id "id22"} defass#r#0#AT#0;
    assume true;
    assume false;
    assume q#0#AT#3 == q#0#AT#1;
    assume r#0#AT#2 == r#0#AT#0;
    goto GeneratedUnifiedExit;

  anon11_Then:
    assume {:partition} x#0 == Mul(q#0#AT#1, y#0) + r#0#AT#0;
    assert {:id "id18"} defass#r#0#AT#0;
    goto anon4;

  anon9_LoopDone:
    assume {:partition} !true;
    goto anon8;

  GeneratedUnifiedExit:
    assert {:id "id11"} x#0 == Mul(q#0#AT#3, y#0) + r#0#AT#2;
    assert {:id "id12"} LitInt(0) <= r#0#AT#2;
    assert {:id "id13"} r#0#AT#2 < y#0;
    return;

  0:
    goto anon0;
}


after peep-hole optimizations
implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "division_entera (correctness)"} Impl$$_module.__default.division__entera(x#0: int, y#0: int) returns (defass#q#0: bool, q#0: int, defass#r#0: bool, r#0: int, $_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var $PreLoopHeap$loop#0: [ref][Field]Box;
  var preLoop$loop#0$defass#r#0: bool;
  var preLoop$loop#0$defass#q#0: bool;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;
  var $_ModifiesFrame#AT#0: [ref,Field]bool;
  var q#0#AT#0: int;
  var $decr_init$loop#00#AT#0: int;
  var $w$loop#0#AT#0: bool;
  var $decr$loop#00#AT#0: int;
  var q#0#AT#1: int;
  var defass#q#0#AT#0: bool;
  var r#0#AT#0: int;
  var defass#r#0#AT#0: bool;
  var $decr$loop#00#AT#1: int;
  var q#0#AT#2: int;
  var r#0#AT#1: int;
  var q#0#AT#3: int;
  var r#0#AT#2: int;


  PreconditionGeneratedEntry:
    assume $IsGoodHeap($Heap) && $IsHeapAnchor($Heap);
    assume 0 == $FunctionContextHeight;
    assume {:id "id9"} x#0 > 0;
    assume {:id "id10"} y#0 > 0;
    goto anon0;

  anon0:
    assume $_ModifiesFrame#AT#0 == lambda#0(null, $Heap, alloc, false);
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(4,0): initial state"} true;
    assume true;
    assume true;
    assume q#0#AT#0 == LitInt(0);
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(5,10)"} true;
    assume true;
    assume true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(6,10)"} true;
    assume $decr_init$loop#00#AT#0 == x#0 - y#0;
    assert {:id "id20$established"} {:id "id20"} $w$loop#0#AT#0 ==> x#0 == Mul(q#0#AT#0, y#0) + x#0;
    assert {:id "id21$established"} {:id "id21"} $w$loop#0#AT#0 ==> x#0 >= LitInt(0);
    goto anon9_LoopHead;

  anon9_LoopHead:
    assume true;
    assume {:id "id20$assume_in_body"} $w$loop#0#AT#0 ==> x#0 == Mul(q#0#AT#1, y#0) + r#0#AT#0;
    assume {:id "id21$assume_in_body"} $w$loop#0#AT#0 ==> r#0#AT#0 >= LitInt(0);
    assume (forall $o: ref :: { $Heap[$o] } $o != null && $Unbox_982(read($Heap, $o, alloc)) ==> $Heap[$o] == $Heap[$o]);
    assume $HeapSucc($Heap, $Heap);
    assume (forall $o: ref, $f: Field :: { read($Heap, $o, $f) } $o != null && $Unbox_982(read($Heap, $o, alloc)) ==> read($Heap, $o, $f) == read($Heap, $o, $f) || $_ModifiesFrame#AT#0[$o, $f]);
    assume true ==> defass#r#0#AT#0;
    assume true ==> defass#q#0#AT#0;
    assume r#0#AT#0 - y#0 <= $decr_init$loop#00#AT#0;
    goto anon9_LoopDone, anon9_LoopBody;

  anon9_LoopBody:
    assume {:partition} true;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(7,4): after some loop iterations"} true;
    goto anon10_Then, anon10_Else;

  anon10_Else:
    assume {:partition} $w$loop#0#AT#0;
    assert {:id "id23"} defass#r#0#AT#0;
    assume true;
    goto anon12_Then, anon12_Else;

  anon12_Else:
    assume {:partition} r#0#AT#0 >= y#0;
    assume $decr$loop#00#AT#1 == r#0#AT#0 - y#0;
    assume true;
    assert {:id "id24"} defass#q#0#AT#0;
    assume true;
    assume q#0#AT#2 == q#0#AT#1 + 1;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(11,18)"} true;
    assume true;
    assert {:id "id26"} defass#r#0#AT#0;
    assume true;
    assume r#0#AT#1 == r#0#AT#0 - y#0;
    assume {:captureState "ejemplo_19_1_division_entera_verificada.dfy(12,18)"} true;
    assert {:id "id28"} 0 <= $decr$loop#00#AT#1 || r#0#AT#1 - y#0 == $decr$loop#00#AT#1;
    assert {:id "id29"} r#0#AT#1 - y#0 < $decr$loop#00#AT#1;
    assume true;
    assert {:id "id20$maintained"} {:id "id20"} $w$loop#0#AT#0 ==> x#0 == Mul(q#0#AT#2, y#0) + r#0#AT#1;
    assert {:id "id21$maintained"} {:id "id21"} $w$loop#0#AT#0 ==> r#0#AT#1 >= LitInt(0);
    assume false;
    assume q#0#AT#3 == q#0#AT#2;
    assume r#0#AT#2 == r#0#AT#1;
    return;

  anon12_Then:
    assume {:partition} y#0 > r#0#AT#0;
    goto anon8;

  anon8:
    assert {:id "id30"} defass#q#0#AT#0;
    assert {:id "id31"} defass#r#0#AT#0;
    assume q#0#AT#3 == q#0#AT#1;
    assume r#0#AT#2 == r#0#AT#0;
    goto GeneratedUnifiedExit;

  GeneratedUnifiedExit:
    assert {:id "id11"} x#0 == Mul(q#0#AT#3, y#0) + r#0#AT#2;
    assert {:id "id12"} LitInt(0) <= r#0#AT#2;
    assert {:id "id13"} r#0#AT#2 < y#0;
    return;

  anon10_Then:
    assume {:partition} !$w$loop#0#AT#0;
    assert {:id "id16"} defass#q#0#AT#0;
    assert {:id "id17"} defass#r#0#AT#0;
    goto anon11_Then, anon11_Else;

  anon11_Else:
    assume {:partition} x#0 != Mul(q#0#AT#1, y#0) + r#0#AT#0;
    goto anon4;

  anon4:
    assume true;
    assume {:id "id19"} x#0 == Mul(q#0#AT#1, y#0) + r#0#AT#0 && r#0#AT#0 >= LitInt(0);
    assert {:id "id22"} defass#r#0#AT#0;
    assume true;
    assume false;
    assume q#0#AT#3 == q#0#AT#1;
    assume r#0#AT#2 == r#0#AT#0;
    return;

  anon11_Then:
    assume {:partition} x#0 == Mul(q#0#AT#1, y#0) + r#0#AT#0;
    assert {:id "id18"} defass#r#0#AT#0;
    goto anon4;

  anon9_LoopDone:
    assume {:partition} !true;
    goto anon8;
}



Boogie program verifier finished with 1 verified, 0 errors
