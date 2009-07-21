// Spec# program verifier version 0.90, Copyright (c) 2003-2008, Microsoft.
// Command Line Options: /print:UseMscorlibContracts.bpl Program.exe

type real;

type elements;

type struct;

type exposeVersionType;

var $Heap: [ref,<x>name]x where IsHeap($Heap);

type ActivityType;

var $ActivityIndicator: ActivityType;

function IsHeap(h: [ref,<x>name]x) returns (bool);

const unique $allocated: <bool>name;

const unique $elements: <elements>name;

axiom DeclType($elements) == System.Object;

const unique $inv: <name>name;

const unique $localinv: <name>name;

const unique $exposeVersion: <exposeVersionType>name;

axiom DeclType($exposeVersion) == System.Object;

const unique $sharingMode: name;

const unique $SharingMode_Unshared: name;

const unique $SharingMode_LockProtected: name;

const unique $ownerRef: <ref>name;

const unique $ownerFrame: <name>name;

const unique $PeerGroupPlaceholder: name;

function ClassRepr(class: name) returns (ref);

function ClassReprInv(ref) returns (name);

axiom (forall c: name :: { ClassRepr(c) } ClassReprInv(ClassRepr(c)) == c);

axiom (forall T: name :: !($typeof(ClassRepr(T)) <: System.Object));

axiom (forall T: name :: ClassRepr(T) != null);

axiom (forall T: name, h: [ref,<x>name]x :: { h[ClassRepr(T), $ownerFrame] } IsHeap(h) ==> h[ClassRepr(T), $ownerFrame] == $PeerGroupPlaceholder);

function IncludeInMainFrameCondition(f: name) returns (bool);

axiom IncludeInMainFrameCondition($allocated);

axiom IncludeInMainFrameCondition($elements);

axiom !IncludeInMainFrameCondition($inv);

axiom !IncludeInMainFrameCondition($localinv);

axiom IncludeInMainFrameCondition($ownerRef);

axiom IncludeInMainFrameCondition($ownerFrame);

axiom IncludeInMainFrameCondition($exposeVersion);

axiom !IncludeInMainFrameCondition($FirstConsistentOwner);

function IsStaticField(f: name) returns (bool);

axiom !IsStaticField($allocated);

axiom !IsStaticField($elements);

axiom !IsStaticField($inv);

axiom !IsStaticField($localinv);

axiom !IsStaticField($exposeVersion);

function $IncludedInModifiesStar(f: name) returns (bool);

axiom !$IncludedInModifiesStar($ownerRef);

axiom !$IncludedInModifiesStar($ownerFrame);

axiom $IncludedInModifiesStar($exposeVersion);

axiom $IncludedInModifiesStar($elements);

function ValueArrayGet(elements, int) returns (any);

function ValueArraySet(elements, int, any) returns (elements);

function IntArrayGet(elements, int) returns (int);

function IntArraySet(elements, int, int) returns (elements);

function RefArrayGet(elements, int) returns (ref);

function RefArraySet(elements, int, ref) returns (elements);

axiom (forall A: elements, i: int, x: any :: ValueArrayGet(ValueArraySet(A, i, x), i) == x);

axiom (forall A: elements, i: int, j: int, x: any :: i != j ==> ValueArrayGet(ValueArraySet(A, i, x), j) == ValueArrayGet(A, j));

axiom (forall A: elements, i: int, x: int :: IntArrayGet(IntArraySet(A, i, x), i) == x);

axiom (forall A: elements, i: int, j: int, x: int :: i != j ==> IntArrayGet(IntArraySet(A, i, x), j) == IntArrayGet(A, j));

axiom (forall A: elements, i: int, x: ref :: RefArrayGet(RefArraySet(A, i, x), i) == x);

axiom (forall A: elements, i: int, j: int, x: ref :: i != j ==> RefArrayGet(RefArraySet(A, i, x), j) == RefArrayGet(A, j));

function ArrayIndex(arr: ref, dim: int, indexAtDim: int, remainingIndexContribution: int) returns (int);

function ArrayIndexInvX(arrayIndex: int) returns (indexAtDim: int);

function ArrayIndexInvY(arrayIndex: int) returns (remainingIndexContribution: int);

axiom (forall a: ref, d: int, x: int, y: int :: { ArrayIndex(a, d, x, y) } ArrayIndexInvX(ArrayIndex(a, d, x, y)) == x);

axiom (forall a: ref, d: int, x: int, y: int :: { ArrayIndex(a, d, x, y) } ArrayIndexInvY(ArrayIndex(a, d, x, y)) == y);

axiom (forall a: ref, i: int, heap: [ref,<x>name]x :: { IntArrayGet(heap[a, $elements], i) } IsHeap(heap) ==> InRange(IntArrayGet(heap[a, $elements], i), $ElementType($typeof(a))));

axiom (forall a: ref, i: int, heap: [ref,<x>name]x :: { $typeof(RefArrayGet(heap[a, $elements], i)) } IsHeap(heap) && RefArrayGet(heap[a, $elements], i) != null ==> $typeof(RefArrayGet(heap[a, $elements], i)) <: $ElementType($typeof(a)));

axiom (forall a: ref, T: name, i: int, r: int, heap: [ref,<x>name]x :: { $typeof(a) <: NonNullRefArray(T, r), RefArrayGet(heap[a, $elements], i) } IsHeap(heap) && $typeof(a) <: NonNullRefArray(T, r) ==> RefArrayGet(heap[a, $elements], i) != null);

function $Rank(ref) returns (int);

axiom (forall a: ref :: 1 <= $Rank(a));

axiom (forall a: ref, T: name, r: int :: { $typeof(a) <: RefArray(T, r) } a != null && $typeof(a) <: RefArray(T, r) ==> $Rank(a) == r);

axiom (forall a: ref, T: name, r: int :: { $typeof(a) <: NonNullRefArray(T, r) } a != null && $typeof(a) <: NonNullRefArray(T, r) ==> $Rank(a) == r);

axiom (forall a: ref, T: name, r: int :: { $typeof(a) <: ValueArray(T, r) } a != null && $typeof(a) <: ValueArray(T, r) ==> $Rank(a) == r);

axiom (forall a: ref, T: name, r: int :: { $typeof(a) <: IntArray(T, r) } a != null && $typeof(a) <: IntArray(T, r) ==> $Rank(a) == r);

function $Length(ref) returns (int);

axiom (forall a: ref :: { $Length(a) } 0 <= $Length(a) && $Length(a) <= int#2147483647);

function $DimLength(ref, int) returns (int);

axiom (forall a: ref, i: int :: 0 <= $DimLength(a, i));

axiom (forall a: ref :: { $DimLength(a, 0) } $Rank(a) == 1 ==> $DimLength(a, 0) == $Length(a));

function $LBound(ref, int) returns (int);

function $UBound(ref, int) returns (int);

axiom (forall a: ref, i: int :: { $LBound(a, i) } $LBound(a, i) == 0);

axiom (forall a: ref, i: int :: { $UBound(a, i) } $UBound(a, i) == $DimLength(a, i) - 1);

const unique $ArrayCategoryValue: name;

const unique $ArrayCategoryInt: name;

const unique $ArrayCategoryRef: name;

const unique $ArrayCategoryNonNullRef: name;

function $ArrayCategory(arrayType: name) returns (arrayCategory: name);

axiom (forall T: name, ET: name, r: int :: { T <: ValueArray(ET, r) } T <: ValueArray(ET, r) ==> $ArrayCategory(T) == $ArrayCategoryValue);

axiom (forall T: name, ET: name, r: int :: { T <: IntArray(ET, r) } T <: IntArray(ET, r) ==> $ArrayCategory(T) == $ArrayCategoryInt);

axiom (forall T: name, ET: name, r: int :: { T <: RefArray(ET, r) } T <: RefArray(ET, r) ==> $ArrayCategory(T) == $ArrayCategoryRef);

axiom (forall T: name, ET: name, r: int :: { T <: NonNullRefArray(ET, r) } T <: NonNullRefArray(ET, r) ==> $ArrayCategory(T) == $ArrayCategoryNonNullRef);

const unique System.Array: name;

axiom System.Array <: System.Object;

function $ElementType(name) returns (name);

function ValueArray(elementType: name, rank: int) returns (name);

axiom (forall T: name, r: int :: { ValueArray(T, r) } ValueArray(T, r) <: ValueArray(T, r) && ValueArray(T, r) <: System.Array);

function IntArray(elementType: name, rank: int) returns (name);

axiom (forall T: name, r: int :: { IntArray(T, r) } IntArray(T, r) <: IntArray(T, r) && IntArray(T, r) <: System.Array);

function RefArray(elementType: name, rank: int) returns (name);

axiom (forall T: name, r: int :: { RefArray(T, r) } RefArray(T, r) <: RefArray(T, r) && RefArray(T, r) <: System.Array);

function NonNullRefArray(elementType: name, rank: int) returns (name);

axiom (forall T: name, r: int :: { NonNullRefArray(T, r) } NonNullRefArray(T, r) <: NonNullRefArray(T, r) && NonNullRefArray(T, r) <: System.Array);

function NonNullRefArrayRaw(array: ref, elementType: name, rank: int) returns (bool);

axiom (forall array: ref, elementType: name, rank: int :: { NonNullRefArrayRaw(array, elementType, rank) } NonNullRefArrayRaw(array, elementType, rank) ==> $typeof(array) <: System.Array && $Rank(array) == rank && elementType <: $ElementType($typeof(array)));

axiom (forall T: name, U: name, r: int :: U <: T ==> RefArray(U, r) <: RefArray(T, r));

axiom (forall T: name, U: name, r: int :: U <: T ==> NonNullRefArray(U, r) <: NonNullRefArray(T, r));

axiom (forall A: name, r: int :: $ElementType(ValueArray(A, r)) == A);

axiom (forall A: name, r: int :: $ElementType(IntArray(A, r)) == A);

axiom (forall A: name, r: int :: $ElementType(RefArray(A, r)) == A);

axiom (forall A: name, r: int :: $ElementType(NonNullRefArray(A, r)) == A);

axiom (forall A: name, r: int, T: name :: { T <: RefArray(A, r) } T <: RefArray(A, r) ==> T != A && T == RefArray($ElementType(T), r) && $ElementType(T) <: A);

axiom (forall A: name, r: int, T: name :: { T <: NonNullRefArray(A, r) } T <: NonNullRefArray(A, r) ==> T != A && T == NonNullRefArray($ElementType(T), r) && $ElementType(T) <: A);

axiom (forall A: name, r: int, T: name :: { T <: ValueArray(A, r) } T <: ValueArray(A, r) ==> T == ValueArray(A, r));

axiom (forall A: name, r: int, T: name :: { T <: IntArray(A, r) } T <: IntArray(A, r) ==> T == IntArray(A, r));

axiom (forall A: name, r: int, T: name :: { RefArray(A, r) <: T } RefArray(A, r) <: T ==> System.Array <: T || (T == RefArray($ElementType(T), r) && A <: $ElementType(T)));

axiom (forall A: name, r: int, T: name :: { NonNullRefArray(A, r) <: T } NonNullRefArray(A, r) <: T ==> System.Array <: T || (T == NonNullRefArray($ElementType(T), r) && A <: $ElementType(T)));

axiom (forall A: name, r: int, T: name :: { ValueArray(A, r) <: T } ValueArray(A, r) <: T ==> System.Array <: T || T == ValueArray(A, r));

axiom (forall A: name, r: int, T: name :: { IntArray(A, r) <: T } IntArray(A, r) <: T ==> System.Array <: T || T == IntArray(A, r));

function $ArrayPtr(elementType: name) returns (name);

function $ElementProxy(ref, int) returns (ref);

function $ElementProxyStruct(struct, int) returns (ref);

axiom (forall a: ref, i: int, heap: [ref,<x>name]x :: { heap[RefArrayGet(heap[a, $elements], i), $ownerRef] } { heap[RefArrayGet(heap[a, $elements], i), $ownerFrame] } IsHeap(heap) && $typeof(a) <: System.Array ==> RefArrayGet(heap[a, $elements], i) == null || $IsImmutable($typeof(RefArrayGet(heap[a, $elements], i))) || (heap[RefArrayGet(heap[a, $elements], i), $ownerRef] == heap[$ElementProxy(a, 0 - 1), $ownerRef] && heap[RefArrayGet(heap[a, $elements], i), $ownerFrame] == heap[$ElementProxy(a, 0 - 1), $ownerFrame]));

axiom (forall a: ref, heap: [ref,<x>name]x :: { IsAllocated(heap, a) } IsHeap(heap) && IsAllocated(heap, a) && $typeof(a) <: System.Array ==> IsAllocated(heap, $ElementProxy(a, 0 - 1)));

axiom (forall o: ref, pos: int :: { $typeof($ElementProxy(o, pos)) } $typeof($ElementProxy(o, pos)) == System.Object);

axiom (forall o: struct, pos: int :: { $typeof($ElementProxyStruct(o, pos)) } $typeof($ElementProxyStruct(o, pos)) == System.Object);

function $StructGet(struct, name) returns (any);

function $StructSet(struct, name, any) returns (struct);

axiom (forall s: struct, f: name, x: any :: $StructGet($StructSet(s, f, x), f) == x);

axiom (forall s: struct, f: name, f': name, x: any :: f != f' ==> $StructGet($StructSet(s, f, x), f') == $StructGet(s, f'));

function ZeroInit(s: struct, typ: name) returns (bool);

function $typeof(ref) returns (name);

function $BaseClass(sub: name) returns (base: name);

axiom (forall T: name :: { $BaseClass(T) } T <: $BaseClass(T) && (T != System.Object ==> T != $BaseClass(T)));

function AsDirectSubClass(sub: name, base: name) returns (sub': name);

function OneClassDown(sub: name, base: name) returns (directSub: name);

axiom (forall A: name, B: name, C: name :: { C <: AsDirectSubClass(B, A) } C <: AsDirectSubClass(B, A) ==> OneClassDown(C, A) == B);

function $IsValueType(name) returns (bool);

axiom (forall T: name :: $IsValueType(T) ==> (forall U: name :: T <: U ==> T == U) && (forall U: name :: U <: T ==> T == U));

const unique System.Boolean: name;

axiom $IsValueType(System.Boolean);

const unique System.Object: name;

function $IsTokenForType(struct, name) returns (bool);

function TypeObject(name) returns (ref);

const unique System.Type: name;

axiom System.Type <: System.Object;

axiom (forall T: name :: { TypeObject(T) } $IsNotNull(TypeObject(T), System.Type));

function TypeName(ref) returns (name);

axiom (forall T: name :: { TypeObject(T) } TypeName(TypeObject(T)) == T);

function $Is(ref, name) returns (bool);

axiom (forall o: ref, T: name :: { $Is(o, T) } $Is(o, T) <==> o == null || $typeof(o) <: T);

function $IsNotNull(ref, name) returns (bool);

axiom (forall o: ref, T: name :: { $IsNotNull(o, T) } $IsNotNull(o, T) <==> o != null && $Is(o, T));

function $As(ref, name) returns (ref);

axiom (forall o: ref, T: name :: $Is(o, T) ==> $As(o, T) == o);

axiom (forall o: ref, T: name :: !$Is(o, T) ==> $As(o, T) == null);

axiom (forall h: [ref,<x>name]x, o: ref :: { $typeof(o) <: System.Array, h[o, $inv] } IsHeap(h) && o != null && $typeof(o) <: System.Array ==> h[o, $inv] == $typeof(o) && h[o, $localinv] == $typeof(o));

function IsAllocated(h: [ref,<x>name]x, o: any) returns (bool);

axiom (forall h: [ref,<x>name]x, o: ref, f: name :: { IsAllocated(h, h[o, f]) } IsHeap(h) && h[o, $allocated] ==> IsAllocated(h, h[o, f]));

axiom (forall h: [ref,<x>name]x, o: ref, f: <ref>name :: { h[h[o, f], $allocated] } IsHeap(h) && h[o, $allocated] ==> h[h[o, f], $allocated]);

axiom (forall h: [ref,<x>name]x, s: struct, f: name :: { IsAllocated(h, $StructGet(s, f)) } IsAllocated(h, s) ==> IsAllocated(h, $StructGet(s, f)));

axiom (forall h: [ref,<x>name]x, e: elements, i: int :: { IsAllocated(h, RefArrayGet(e, i)) } IsAllocated(h, e) ==> IsAllocated(h, RefArrayGet(e, i)));

axiom (forall h: [ref,<x>name]x, e: elements, i: int :: { IsAllocated(h, ValueArrayGet(e, i)) } IsAllocated(h, e) ==> IsAllocated(h, ValueArrayGet(e, i)));

axiom (forall h: [ref,<x>name]x, o: ref :: { h[o, $allocated] } IsAllocated(h, o) ==> h[o, $allocated]);

axiom (forall h: [ref,<x>name]x, c: name :: { h[ClassRepr(c), $allocated] } IsHeap(h) ==> h[ClassRepr(c), $allocated]);

const $BeingConstructed: ref;

const unique $NonNullFieldsAreInitialized: <bool>name;

const $PurityAxiomsCanBeAssumed: bool;

axiom DeclType($NonNullFieldsAreInitialized) == System.Object;

function DeclType(field: name) returns (class: name);

function AsNonNullRefField(field: <ref>name, T: name) returns (f: <ref>name);

function AsRefField(field: <ref>name, T: name) returns (f: <ref>name);

function AsRangeField(field: <int>name, T: name) returns (f: <int>name);

axiom (forall f: <ref>name, T: name :: { AsNonNullRefField(f, T) } AsNonNullRefField(f, T) == f ==> AsRefField(f, T) == f);

axiom (forall h: [ref,<x>name]x, o: ref, f: <ref>name, T: name :: { h[o, AsRefField(f, T)] } IsHeap(h) ==> $Is(h[o, AsRefField(f, T)], T));

axiom (forall h: [ref,<x>name]x, o: ref, f: <ref>name, T: name :: { h[o, AsNonNullRefField(f, T)] } IsHeap(h) && o != null && (o != $BeingConstructed || h[$BeingConstructed, $NonNullFieldsAreInitialized] == true) ==> h[o, AsNonNullRefField(f, T)] != null);

axiom (forall h: [ref,<x>name]x, o: ref, f: <int>name, T: name :: { h[o, AsRangeField(f, T)] } IsHeap(h) ==> InRange(h[o, AsRangeField(f, T)], T));

function $IsMemberlessType(name) returns (bool);

axiom (forall o: ref :: { $IsMemberlessType($typeof(o)) } !$IsMemberlessType($typeof(o)));

function $AsInterface(name) returns (name);

axiom (forall $J: name, s: any, b: ref :: { UnboxedType(Box(s, b)) <: $AsInterface($J) } $AsInterface($J) == $J && Box(s, b) == b && UnboxedType(Box(s, b)) <: $AsInterface($J) ==> $typeof(b) <: $J);

function $HeapSucc(oldHeap: [ref,<x>name]x, newHeap: [ref,<x>name]x) returns (bool);

function $IsImmutable(T: name) returns (bool);

axiom !$IsImmutable(System.Object);

function $AsImmutable(T: name) returns (theType: name);

function $AsMutable(T: name) returns (theType: name);

axiom (forall T: name, U: name :: { U <: $AsImmutable(T) } U <: $AsImmutable(T) ==> $IsImmutable(U) && $AsImmutable(U) == U);

axiom (forall T: name, U: name :: { U <: $AsMutable(T) } U <: $AsMutable(T) ==> !$IsImmutable(U) && $AsMutable(U) == U);

function AsOwner(string: ref, owner: ref) returns (theString: ref);

axiom (forall o: ref, T: name :: { $typeof(o) <: $AsImmutable(T) } o != null && o != $BeingConstructed && $typeof(o) <: $AsImmutable(T) ==> (forall h: [ref,<x>name]x :: { IsHeap(h) } IsHeap(h) ==> h[o, $inv] == $typeof(o) && h[o, $localinv] == $typeof(o) && h[o, $ownerFrame] == $PeerGroupPlaceholder && AsOwner(o, h[o, $ownerRef]) == o && (forall t: ref :: { AsOwner(o, h[t, $ownerRef]) } AsOwner(o, h[t, $ownerRef]) == o ==> t == o || h[t, $ownerFrame] != $PeerGroupPlaceholder)));

const unique System.String: name;

function $StringLength(ref) returns (int);

axiom (forall s: ref :: { $StringLength(s) } 0 <= $StringLength(s));

function AsRepField(f: <ref>name, declaringType: name) returns (theField: <ref>name);

axiom (forall h: [ref,<x>name]x, o: ref, f: <ref>name, T: name :: { h[o, AsRepField(f, T)] } IsHeap(h) && h[o, AsRepField(f, T)] != null ==> h[h[o, AsRepField(f, T)], $ownerRef] == o && h[h[o, AsRepField(f, T)], $ownerFrame] == T);

function AsPeerField(f: <ref>name) returns (theField: <ref>name);

axiom (forall h: [ref,<x>name]x, o: ref, f: <ref>name :: { h[o, AsPeerField(f)] } IsHeap(h) && h[o, AsPeerField(f)] != null ==> h[h[o, AsPeerField(f)], $ownerRef] == h[o, $ownerRef] && h[h[o, AsPeerField(f)], $ownerFrame] == h[o, $ownerFrame]);

function AsElementsRepField(f: <ref>name, declaringType: name, position: int) returns (theField: <ref>name);

axiom (forall h: [ref,<x>name]x, o: ref, f: <ref>name, T: name, i: int :: { h[o, AsElementsRepField(f, T, i)] } IsHeap(h) && h[o, AsElementsRepField(f, T, i)] != null ==> h[$ElementProxy(h[o, AsElementsRepField(f, T, i)], i), $ownerRef] == o && h[$ElementProxy(h[o, AsElementsRepField(f, T, i)], i), $ownerFrame] == T);

function AsElementsPeerField(f: <ref>name, position: int) returns (theField: <ref>name);

axiom (forall h: [ref,<x>name]x, o: ref, f: <ref>name, i: int :: { h[o, AsElementsPeerField(f, i)] } IsHeap(h) && h[o, AsElementsPeerField(f, i)] != null ==> h[$ElementProxy(h[o, AsElementsPeerField(f, i)], i), $ownerRef] == h[o, $ownerRef] && h[$ElementProxy(h[o, AsElementsPeerField(f, i)], i), $ownerFrame] == h[o, $ownerFrame]);

axiom (forall h: [ref,<x>name]x, o: ref :: { h[h[o, $ownerRef], $inv] <: h[o, $ownerFrame] } IsHeap(h) && h[o, $ownerFrame] != $PeerGroupPlaceholder && h[h[o, $ownerRef], $inv] <: h[o, $ownerFrame] && h[h[o, $ownerRef], $localinv] != $BaseClass(h[o, $ownerFrame]) ==> h[o, $inv] == $typeof(o) && h[o, $localinv] == $typeof(o));

procedure $SetOwner(o: ref, ow: ref, fr: name);
  modifies $Heap;
  ensures (forall p: ref, F: name :: { $Heap[p, F] } (F != $ownerRef && F != $ownerFrame) || old($Heap[p, $ownerRef] != $Heap[o, $ownerRef]) || old($Heap[p, $ownerFrame] != $Heap[o, $ownerFrame]) ==> old($Heap[p, F]) == $Heap[p, F]);
  ensures (forall p: ref :: { $Heap[p, $ownerRef] } { $Heap[p, $ownerFrame] } old($Heap[p, $ownerRef] == $Heap[o, $ownerRef]) && old($Heap[p, $ownerFrame] == $Heap[o, $ownerFrame]) ==> $Heap[p, $ownerRef] == ow && $Heap[p, $ownerFrame] == fr);
  free ensures $HeapSucc(old($Heap), $Heap);



procedure $UpdateOwnersForRep(o: ref, T: name, e: ref);
  modifies $Heap;
  ensures (forall p: ref, F: name :: { $Heap[p, F] } (F != $ownerRef && F != $ownerFrame) || old($Heap[p, $ownerRef] != $Heap[e, $ownerRef]) || old($Heap[p, $ownerFrame] != $Heap[e, $ownerFrame]) ==> old($Heap[p, F]) == $Heap[p, F]);
  ensures e == null ==> $Heap == old($Heap);
  ensures e != null ==> (forall p: ref :: { $Heap[p, $ownerRef] } { $Heap[p, $ownerFrame] } old($Heap[p, $ownerRef] == $Heap[e, $ownerRef]) && old($Heap[p, $ownerFrame] == $Heap[e, $ownerFrame]) ==> $Heap[p, $ownerRef] == o && $Heap[p, $ownerFrame] == T);
  free ensures $HeapSucc(old($Heap), $Heap);



procedure $UpdateOwnersForPeer(c: ref, d: ref);
  modifies $Heap;
  ensures (forall p: ref, F: name :: { $Heap[p, F] } (F != $ownerRef && F != $ownerFrame) || old($Heap[p, $ownerRef] != $Heap[d, $ownerRef] || $Heap[p, $ownerFrame] != $Heap[d, $ownerFrame]) ==> old($Heap[p, F]) == $Heap[p, F]);
  ensures d == null ==> $Heap == old($Heap);
  ensures d != null ==> (forall p: ref :: { $Heap[p, $ownerRef] } { $Heap[p, $ownerFrame] } old($Heap[p, $ownerRef] == $Heap[d, $ownerRef] && $Heap[p, $ownerFrame] == $Heap[d, $ownerFrame]) ==> $Heap[p, $ownerRef] == old($Heap)[c, $ownerRef] && $Heap[p, $ownerFrame] == old($Heap)[c, $ownerFrame]);
  free ensures $HeapSucc(old($Heap), $Heap);



const unique $FirstConsistentOwner: <ref>name;

function $AsPureObject(ref) returns (ref);

function ##FieldDependsOnFCO(o: ref, f: name, ev: exposeVersionType) returns (value: any);

axiom (forall o: ref, f: name, h: [ref,<x>name]x :: { h[$AsPureObject(o), f] } IsHeap(h) && o != null && h[o, $allocated] == true && $AsPureObject(o) == o && h[o, $ownerFrame] != $PeerGroupPlaceholder && h[h[o, $ownerRef], $inv] <: h[o, $ownerFrame] && h[h[o, $ownerRef], $localinv] != $BaseClass(h[o, $ownerFrame]) ==> h[o, f] == ##FieldDependsOnFCO(o, f, h[h[o, $FirstConsistentOwner], $exposeVersion]));

axiom (forall o: ref, h: [ref,<x>name]x :: { h[o, $FirstConsistentOwner] } IsHeap(h) && o != null && h[o, $allocated] == true && h[o, $ownerFrame] != $PeerGroupPlaceholder && h[h[o, $ownerRef], $inv] <: h[o, $ownerFrame] && h[h[o, $ownerRef], $localinv] != $BaseClass(h[o, $ownerFrame]) ==> h[o, $FirstConsistentOwner] != null && h[h[o, $FirstConsistentOwner], $allocated] == true && (h[h[o, $FirstConsistentOwner], $ownerFrame] == $PeerGroupPlaceholder || !(h[h[h[o, $FirstConsistentOwner], $ownerRef], $inv] <: h[h[o, $FirstConsistentOwner], $ownerFrame]) || h[h[h[o, $FirstConsistentOwner], $ownerRef], $localinv] == $BaseClass(h[h[o, $FirstConsistentOwner], $ownerFrame])));

function Box(any, ref) returns (ref);

function Unbox(ref) returns (any);

type NondetType;

function MeldNondets(NondetType, any) returns (NondetType);

function BoxFunc(value: any, typ: name, occurrence: NondetType, activity: ActivityType) returns (boxedValue: ref);

axiom (forall value: any, typ: name, occurrence: NondetType, activity: ActivityType :: { BoxFunc(value, typ, occurrence, activity) } Box(value, BoxFunc(value, typ, occurrence, activity)) == BoxFunc(value, typ, occurrence, activity) && UnboxedType(BoxFunc(value, typ, occurrence, activity)) == typ);

axiom (forall x: ref, typ: name, occurrence: NondetType, activity: ActivityType :: !$IsValueType(UnboxedType(x)) ==> BoxFunc(x, typ, occurrence, activity) == x);

axiom (forall x: any, p: ref :: { Unbox(Box(x, p)) } Unbox(Box(x, p)) == x);

function UnboxedType(ref) returns (name);

axiom (forall p: ref :: { $IsValueType(UnboxedType(p)) } $IsValueType(UnboxedType(p)) ==> (forall heap: [ref,<x>name]x, x: any :: { heap[Box(x, p), $inv] } IsHeap(heap) ==> heap[Box(x, p), $inv] == $typeof(Box(x, p)) && heap[Box(x, p), $localinv] == $typeof(Box(x, p))));

axiom (forall x: any, p: ref :: { UnboxedType(Box(x, p)) <: System.Object } UnboxedType(Box(x, p)) <: System.Object && Box(x, p) == p ==> x == p);

function BoxTester(p: ref, typ: name) returns (ref);

axiom (forall p: ref, typ: name :: { BoxTester(p, typ) } UnboxedType(p) == typ <==> BoxTester(p, typ) != null);

axiom (forall p: ref, typ: name :: { BoxTester(p, typ) } BoxTester(p, typ) != null ==> Box(Unbox(p), p) == p);

const unique System.SByte: name;

axiom $IsValueType(System.SByte);

const unique System.Byte: name;

axiom $IsValueType(System.Byte);

const unique System.Int16: name;

axiom $IsValueType(System.Int16);

const unique System.UInt16: name;

axiom $IsValueType(System.UInt16);

const unique System.Int32: name;

axiom $IsValueType(System.Int32);

const unique System.UInt32: name;

axiom $IsValueType(System.UInt32);

const unique System.Int64: name;

axiom $IsValueType(System.Int64);

const unique System.UInt64: name;

axiom $IsValueType(System.UInt64);

const unique System.Char: name;

axiom $IsValueType(System.Char);

const unique System.UIntPtr: name;

axiom $IsValueType(System.UIntPtr);

const unique System.IntPtr: name;

axiom $IsValueType(System.IntPtr);

const int#m2147483648: int;

const int#2147483647: int;

const int#4294967295: int;

const int#m9223372036854775808: int;

const int#9223372036854775807: int;

const int#18446744073709551615: int;

axiom int#m9223372036854775808 < int#m2147483648;

axiom int#m2147483648 < 0 - 100000;

axiom 100000 < int#2147483647;

axiom int#2147483647 < int#4294967295;

axiom int#4294967295 < int#9223372036854775807;

axiom int#9223372036854775807 < int#18446744073709551615;

axiom int#m9223372036854775808 + 1 == 0 - int#9223372036854775807;

axiom int#m2147483648 + 1 == 0 - int#2147483647;

function InRange(i: int, T: name) returns (bool);

axiom (forall i: int :: InRange(i, System.SByte) <==> 0 - 128 <= i && i < 128);

axiom (forall i: int :: InRange(i, System.Byte) <==> 0 <= i && i < 256);

axiom (forall i: int :: InRange(i, System.Int16) <==> 0 - 32768 <= i && i < 32768);

axiom (forall i: int :: InRange(i, System.UInt16) <==> 0 <= i && i < 65536);

axiom (forall i: int :: InRange(i, System.Int32) <==> int#m2147483648 <= i && i <= int#2147483647);

axiom (forall i: int :: InRange(i, System.UInt32) <==> 0 <= i && i <= int#4294967295);

axiom (forall i: int :: InRange(i, System.Int64) <==> int#m9223372036854775808 <= i && i <= int#9223372036854775807);

axiom (forall i: int :: InRange(i, System.UInt64) <==> 0 <= i && i <= int#18446744073709551615);

axiom (forall i: int :: InRange(i, System.Char) <==> 0 <= i && i < 65536);

function $IntToInt(val: int, fromType: name, toType: name) returns (int);

function $IntToReal(int, fromType: name, toType: name) returns (real);

function $RealToInt(real, fromType: name, toType: name) returns (int);

function $RealToReal(val: real, fromType: name, toType: name) returns (real);

axiom (forall z: int, B: name, C: name :: InRange(z, C) ==> $IntToInt(z, B, C) == z);

function $SizeIs(name, int) returns (bool);

function $IfThenElse(bool, any, any) returns (any);

axiom (forall b: bool, x: any, y: any :: { $IfThenElse(b, x, y) } b ==> $IfThenElse(b, x, y) == x);

axiom (forall b: bool, x: any, y: any :: { $IfThenElse(b, x, y) } !b ==> $IfThenElse(b, x, y) == y);

function #neg(int) returns (int);

function #and(int, int) returns (int);

function #or(int, int) returns (int);

function #xor(int, int) returns (int);

function #shl(int, int) returns (int);

function #shr(int, int) returns (int);

function #rneg(real) returns (real);

function #radd(real, real) returns (real);

function #rsub(real, real) returns (real);

function #rmul(real, real) returns (real);

function #rdiv(real, real) returns (real);

function #rmod(real, real) returns (real);

function #rLess(real, real) returns (bool);

function #rAtmost(real, real) returns (bool);

function #rEq(real, real) returns (bool);

function #rNeq(real, real) returns (bool);

function #rAtleast(real, real) returns (bool);

function #rGreater(real, real) returns (bool);

axiom (forall x: int, y: int :: { x % y } { x / y } x % y == x - x / y * y);

axiom (forall x: int, y: int :: { x % y } 0 <= x && 0 < y ==> 0 <= x % y && x % y < y);

axiom (forall x: int, y: int :: { x % y } 0 <= x && y < 0 ==> 0 <= x % y && x % y < 0 - y);

axiom (forall x: int, y: int :: { x % y } x <= 0 && 0 < y ==> 0 - y < x % y && x % y <= 0);

axiom (forall x: int, y: int :: { x % y } x <= 0 && y < 0 ==> y < x % y && x % y <= 0);

axiom (forall x: int, y: int :: { (x + y) % y } 0 <= x && 0 <= y ==> (x + y) % y == x % y);

axiom (forall x: int, y: int :: { (y + x) % y } 0 <= x && 0 <= y ==> (y + x) % y == x % y);

axiom (forall x: int, y: int :: { (x - y) % y } 0 <= x - y && 0 <= y ==> (x - y) % y == x % y);

axiom (forall a: int, b: int, d: int :: { a % d, b % d } 2 <= d && a % d == b % d && a < b ==> a + d <= b);

axiom (forall x: int, y: int :: { #and(x, y) } 0 <= x || 0 <= y ==> 0 <= #and(x, y));

axiom (forall x: int, y: int :: { #or(x, y) } 0 <= x && 0 <= y ==> 0 <= #or(x, y) && #or(x, y) <= x + y);

axiom (forall i: int :: { #shl(i, 0) } #shl(i, 0) == i);

axiom (forall i: int, j: int :: { #shl(i, j) } 1 <= j ==> #shl(i, j) == #shl(i, j - 1) * 2);

axiom (forall i: int, j: int :: { #shl(i, j) } 0 <= i && i < 32768 && 0 <= j && j <= 16 ==> 0 <= #shl(i, j) && #shl(i, j) <= int#2147483647);

axiom (forall i: int :: { #shr(i, 0) } #shr(i, 0) == i);

axiom (forall i: int, j: int :: { #shr(i, j) } 1 <= j ==> #shr(i, j) == #shr(i, j - 1) / 2);

function #min(int, int) returns (int);

function #max(int, int) returns (int);

axiom (forall x: int, y: int :: { #min(x, y) } (#min(x, y) == x || #min(x, y) == y) && #min(x, y) <= x && #min(x, y) <= y);

axiom (forall x: int, y: int :: { #max(x, y) } (#max(x, y) == x || #max(x, y) == y) && x <= #max(x, y) && y <= #max(x, y));

function #System.String.IsInterned$System.String$notnull([ref,<x>name]x, ref) returns (ref);

function #System.String.Equals$System.String([ref,<x>name]x, ref, ref) returns (bool);

function #System.String.Equals$System.String$System.String([ref,<x>name]x, ref, ref) returns (bool);

function ##StringEquals(ref, ref) returns (bool);

axiom (forall h: [ref,<x>name]x, a: ref, b: ref :: { #System.String.Equals$System.String(h, a, b) } #System.String.Equals$System.String(h, a, b) == #System.String.Equals$System.String$System.String(h, a, b));

axiom (forall h: [ref,<x>name]x, a: ref, b: ref :: { #System.String.Equals$System.String$System.String(h, a, b) } #System.String.Equals$System.String$System.String(h, a, b) == ##StringEquals(a, b) && #System.String.Equals$System.String$System.String(h, a, b) == ##StringEquals(b, a) && (a == b ==> ##StringEquals(a, b)));

axiom (forall a: ref, b: ref, c: ref :: ##StringEquals(a, b) && ##StringEquals(b, c) ==> ##StringEquals(a, c));

axiom (forall h: [ref,<x>name]x, a: ref, b: ref :: { #System.String.Equals$System.String$System.String(h, a, b) } a != null && b != null && #System.String.Equals$System.String$System.String(h, a, b) ==> #System.String.IsInterned$System.String$notnull(h, a) == #System.String.IsInterned$System.String$notnull(h, b));

const $UnknownRef: ref;

const unique System.MarshalByRefObject: name;

const unique System.IComparable`1...System.String: name;

const unique System.IConvertible: name;

const unique System.Collections.Generic.IEnumerable`1...System.Char: name;

const unique System.ICloneable: name;

const unique System.Collections.IEnumerable: name;

const unique System.IO.TextWriter: name;

const unique System.IComparable: name;

const unique System.Collections.IList: name;

const unique Play.Program: name;

const unique System.IO.StreamWriter: name;

const unique System.IDisposable: name;

const unique System.Collections.ICollection: name;

const unique System.IEquatable`1...System.String: name;

const unique System.IO.TextReader: name;

function #System.String.Replace$System.String$notnull$System.String([ref,<x>name]x, ref, ref, ref) returns (ref);

function ##System.String.Replace$System.String$notnull$System.String(exposeVersionType, ref, ref) returns (ref);

function #System.Console.get_In([ref,<x>name]x) returns (ref);

function ##System.Console.get_In() returns (ref);

function #System.String.PadLeft$System.Int32([ref,<x>name]x, ref, int) returns (ref);

function ##System.String.PadLeft$System.Int32(exposeVersionType, int) returns (ref);

axiom Play.Program <: Play.Program;

axiom $BaseClass(Play.Program) == System.Object && AsDirectSubClass(Play.Program, $BaseClass(Play.Program)) == Play.Program;

axiom !$IsImmutable(Play.Program) && $AsMutable(Play.Program) == Play.Program;

// Play.Program object invariant
axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: Play.Program } IsHeap($h) && $h[$oi, $inv] <: Play.Program && $h[$oi, $localinv] != $BaseClass(Play.Program) ==> true);

axiom System.Array <: System.Array;

axiom $BaseClass(System.Array) == System.Object && AsDirectSubClass(System.Array, $BaseClass(System.Array)) == System.Array;

axiom !$IsImmutable(System.Array) && $AsMutable(System.Array) == System.Array;

axiom System.ICloneable <: System.ICloneable;

axiom System.ICloneable <: System.Object;

axiom $IsMemberlessType(System.ICloneable);

axiom $AsInterface(System.ICloneable) == System.ICloneable;

axiom System.Array <: System.ICloneable;

axiom System.Collections.IList <: System.Collections.IList;

axiom System.Collections.IList <: System.Object;

axiom System.Collections.ICollection <: System.Collections.ICollection;

axiom System.Collections.ICollection <: System.Object;

axiom System.Collections.IEnumerable <: System.Collections.IEnumerable;

axiom System.Collections.IEnumerable <: System.Object;

axiom $IsMemberlessType(System.Collections.IEnumerable);

axiom $AsInterface(System.Collections.IEnumerable) == System.Collections.IEnumerable;

axiom System.Collections.ICollection <: System.Collections.IEnumerable;

axiom $IsMemberlessType(System.Collections.ICollection);

axiom $AsInterface(System.Collections.ICollection) == System.Collections.ICollection;

axiom System.Collections.IList <: System.Collections.ICollection;

axiom System.Collections.IList <: System.Collections.IEnumerable;

axiom $IsMemberlessType(System.Collections.IList);

axiom $AsInterface(System.Collections.IList) == System.Collections.IList;

axiom System.Array <: System.Collections.IList;

axiom System.Array <: System.Collections.ICollection;

axiom System.Array <: System.Collections.IEnumerable;

axiom $IsMemberlessType(System.Array);

// System.Array object invariant
axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: System.Array } IsHeap($h) && $h[$oi, $inv] <: System.Array && $h[$oi, $localinv] != $BaseClass(System.Array) ==> true);

axiom System.String <: System.String;

axiom $BaseClass(System.String) == System.Object && AsDirectSubClass(System.String, $BaseClass(System.String)) == System.String;

axiom $IsImmutable(System.String) && $AsImmutable(System.String) == System.String;

axiom System.IComparable <: System.IComparable;

axiom System.IComparable <: System.Object;

axiom $IsMemberlessType(System.IComparable);

axiom $AsInterface(System.IComparable) == System.IComparable;

axiom System.String <: System.IComparable;

axiom System.String <: System.ICloneable;

axiom System.IConvertible <: System.IConvertible;

axiom System.IConvertible <: System.Object;

axiom $IsMemberlessType(System.IConvertible);

axiom $AsInterface(System.IConvertible) == System.IConvertible;

axiom System.String <: System.IConvertible;

axiom System.IComparable`1...System.String <: System.IComparable`1...System.String;

axiom System.IComparable`1...System.String <: System.Object;

axiom $IsMemberlessType(System.IComparable`1...System.String);

axiom $AsInterface(System.IComparable`1...System.String) == System.IComparable`1...System.String;

axiom System.String <: System.IComparable`1...System.String;

axiom System.Collections.Generic.IEnumerable`1...System.Char <: System.Collections.Generic.IEnumerable`1...System.Char;

axiom System.Collections.Generic.IEnumerable`1...System.Char <: System.Object;

axiom System.Collections.Generic.IEnumerable`1...System.Char <: System.Collections.IEnumerable;

axiom $IsMemberlessType(System.Collections.Generic.IEnumerable`1...System.Char);

axiom $AsInterface(System.Collections.Generic.IEnumerable`1...System.Char) == System.Collections.Generic.IEnumerable`1...System.Char;

axiom System.String <: System.Collections.Generic.IEnumerable`1...System.Char;

axiom System.String <: System.Collections.IEnumerable;

axiom System.IEquatable`1...System.String <: System.IEquatable`1...System.String;

axiom System.IEquatable`1...System.String <: System.Object;

axiom $IsMemberlessType(System.IEquatable`1...System.String);

axiom $AsInterface(System.IEquatable`1...System.String) == System.IEquatable`1...System.String;

axiom System.String <: System.IEquatable`1...System.String;

axiom (forall $U: name :: { $U <: System.String } $U <: System.String ==> $U == System.String);

// System.String object invariant
axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: System.String } IsHeap($h) && $h[$oi, $inv] <: System.String && $h[$oi, $localinv] != $BaseClass(System.String) ==> true);

procedure Play.Program.Main$System.String.array$notnull(commandLineArgs$in: ref where $IsNotNull(commandLineArgs$in, RefArray(System.String, 1)) && $Heap[commandLineArgs$in, $allocated]);
  // commandLineArgs is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[commandLineArgs$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[commandLineArgs$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // commandLineArgs is peer consistent (owner must not be valid)
  requires $Heap[commandLineArgs$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[commandLineArgs$in, $ownerRef], $inv] <: $Heap[commandLineArgs$in, $ownerFrame]) || $Heap[$Heap[commandLineArgs$in, $ownerRef], $localinv] == $BaseClass($Heap[commandLineArgs$in, $ownerFrame]);
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Play.Program.Main$System.String.array$notnull(commandLineArgs$in: ref)
{
  var commandLineArgs: ref where $IsNotNull(commandLineArgs, RefArray(System.String, 1)) && $Heap[commandLineArgs, $allocated], stack0o: ref, stack0i: int, stack1i: int, stack0b: bool, home: ref where $Is(home, System.String) && $Heap[home, $allocated], path: ref where $Is(path, System.String) && $Heap[path, $allocated], temp: ref where $Is(temp, System.String) && $Heap[temp, $allocated], local3: ref where $Is(local3, System.String) && $Heap[local3, $allocated], stack1o: ref, stack2o: ref, stack50000o: ref, writer: ref where $Is(writer, System.IO.StreamWriter) && $Heap[writer, $allocated], local6: ref where $Is(local6, System.String) && $Heap[local6, $allocated], line: ref where $Is(line, System.String) && $Heap[line, $allocated], temp0: ref, stack3i: int, stack4i: int, parts: ref where $Is(parts, RefArray(System.String, 1)) && $Heap[parts, $allocated], local10: ref where $Is(local10, System.IO.StreamWriter) && $Heap[local10, $allocated], local9: ref where $Is(local9, System.String) && $Heap[local9, $allocated], padAmount: int where InRange(padAmount, System.Int32), $Heap$block2703$LoopPreheader: [ref,<x>name]x;

  entry:
    commandLineArgs := commandLineArgs$in;
    goto block2550;

  block2550:
    goto block2618;

  block2618:
    // ----- copy  ----- Program.ssc(27,13)
    stack0o := commandLineArgs;
    // ----- unary operator  ----- Program.ssc(27,13)
    assert stack0o != null;
    stack0i := $Length(stack0o);
    // ----- unary operator  ----- Program.ssc(27,13)
    stack0i := $IntToInt(stack0i, System.UIntPtr, System.Int32);
    // ----- load constant 1  ----- Program.ssc(27,13)
    stack1i := 1;
    // ----- binary operator  ----- Program.ssc(27,13)
    // ----- branch  ----- Program.ssc(27,13)
    goto true2618to2652, false2618to2635;

  true2618to2652:
    assume stack0i == stack1i;
    goto block2652;

  false2618to2635:
    assume stack0i != stack1i;
    goto block2635;

  block2652:
    // ----- load constant "HOME"  ----- Program.ssc(29,20)
    stack0o := $stringLiteral0;
    // ----- call  ----- Program.ssc(29,20)
    call home := System.Environment.GetEnvironmentVariable$System.String$notnull(stack0o);
    // ----- copy  ----- Program.ssc(32,20)
    stack0o := commandLineArgs;
    // ----- load constant 0  ----- Program.ssc(32,20)
    stack1i := 0;
    // ----- load element  ----- Program.ssc(32,20)
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    path := RefArrayGet($Heap[stack0o, $elements], stack1i);
    stack0o := null;
    // ----- binary operator  ----- Program.ssc(40,13)
    // ----- branch  ----- Program.ssc(40,13)
    goto true2652to2686, false2652to2669;

  block2635:
    // ----- branch  ----- Program.ssc(27,46)
    goto block2788;

  true2652to2686:
    assume path != stack0o;
    goto block2686;

  false2652to2669:
    assume path == stack0o;
    goto block2669;

  block2686:
    // ----- call  ----- Program.ssc(43,20)
    call temp := System.IO.Path.GetTempPath();
    // ----- copy
    stack0o := path;
    // ----- copy  ----- Program.ssc(46,13)
    local3 := home;
    // ----- copy  ----- Program.ssc(46,13)
    stack1o := local3;
    // ----- copy  ----- Program.ssc(46,13)
    stack2o := temp;
    // ----- call  ----- Program.ssc(46,13)
    assert stack0o != null;
    call path := System.String.Replace$System.String$notnull$System.String(stack0o, stack1o, stack2o);
    // ----- copy  ----- Program.ssc(49,42)
    stack0o := path;
    // ----- new object  ----- Program.ssc(49,42)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == System.IO.StreamWriter;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    // ----- call  ----- Program.ssc(49,42)
    assert stack50000o != null;
    call System.IO.StreamWriter..ctor$System.String$notnull(stack50000o, stack0o);
    // ----- copy  ----- Program.ssc(49,42)
    stack0o := stack50000o;
    // ----- copy  ----- Program.ssc(49,42)
    writer := stack0o;
    goto block2703$LoopPreheader;

  block2669:
    // ----- branch  ----- Program.ssc(40,31)
    goto block2788;

  block2788:
    // ----- return  ----- Program.ssc(62,9)
    return;

  block2703:
    // ----- default loop invariant: allocation and ownership are stable  ----- Program.ssc(52,17)
    assume (forall $o: ref :: { $Heap[$o, $allocated] } $Heap$block2703$LoopPreheader[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } $Heap$block2703$LoopPreheader[$ot, $allocated] && $Heap$block2703$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block2703$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block2703$LoopPreheader[$ot, $ownerFrame]) && $Heap$block2703$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: exposure  ----- Program.ssc(52,17)
    assume (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $Heap$block2703$LoopPreheader[$o, $allocated] ==> $Heap$block2703$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block2703$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]);
    assume (forall $o: ref :: !$Heap$block2703$LoopPreheader[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: modifies  ----- Program.ssc(52,17)
    assert (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old(true) ==> $Heap$block2703$LoopPreheader[$o, $f] == $Heap[$o, $f]);
    assume $HeapSucc($Heap$block2703$LoopPreheader, $Heap);
    // ----- default loop invariant: owner fields  ----- Program.ssc(52,17)
    assert (forall $o: ref :: { $Heap[$o, $ownerFrame] } { $Heap[$o, $ownerRef] } $o != null && $Heap$block2703$LoopPreheader[$o, $allocated] ==> $Heap[$o, $ownerRef] == $Heap$block2703$LoopPreheader[$o, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap$block2703$LoopPreheader[$o, $ownerFrame]);
    // ----- advance activity
    havoc $ActivityIndicator;
    // ----- call  ----- Program.ssc(52,17)
    call stack0o := System.Console.get_In();
    // ----- call  ----- Program.ssc(52,17)
    assert stack0o != null;
    call local6 := System.IO.TextReader.ReadLine$.Virtual.$(stack0o);
    // ----- copy  ----- Program.ssc(52,25)
    line := local6;
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true2703to2771, false2703to2720;

  true2703to2771:
    assume local6 == stack0o;
    goto block2771;

  false2703to2720:
    assume local6 != stack0o;
    goto block2720;

  block2771:
    // ----- branch
    goto block2839;

  block2720:
    // ----- copy
    stack0o := line;
    // ----- load constant 1
    stack1i := 1;
    // ----- new array
    assert 0 <= stack1i;
    havoc temp0;
    assume $Heap[temp0, $allocated] == false && $Length(temp0) == stack1i;
    assume $Heap[$ElementProxy(temp0, -1), $allocated] == false && $ElementProxy(temp0, -1) != temp0 && $ElementProxy(temp0, -1) != null;
    assume temp0 != null;
    assume $typeof(temp0) == IntArray(System.Char, 1);
    assume $Heap[temp0, $ownerRef] == temp0 && $Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder;
    assume $Heap[$ElementProxy(temp0, -1), $ownerRef] == $ElementProxy(temp0, -1) && $Heap[$ElementProxy(temp0, -1), $ownerFrame] == $PeerGroupPlaceholder;
    assume $Heap[temp0, $inv] == $typeof(temp0) && $Heap[temp0, $localinv] == $typeof(temp0);
    assume (forall $i: int :: IntArrayGet($Heap[temp0, $elements], $i) == 0);
    $Heap[temp0, $allocated] := true;
    call System.Object..ctor($ElementProxy(temp0, -1));
    stack1o := temp0;
    assume IsHeap($Heap);
    // ----- copy  ----- Program.ssc(54,30)
    stack2o := stack1o;
    // ----- load constant 0
    stack3i := 0;
    // ----- load constant 32
    stack4i := 32;
    // ----- store element
    assert stack2o != null;
    assert 0 <= stack3i;
    assert stack3i < $Length(stack2o);
    assert $Heap[stack2o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack2o, $ownerRef], $inv] <: $Heap[stack2o, $ownerFrame]) || $Heap[$Heap[stack2o, $ownerRef], $localinv] == $BaseClass($Heap[stack2o, $ownerFrame]);
    $Heap[stack2o, $elements] := IntArraySet($Heap[stack2o, $elements], stack3i, stack4i);
    assume IsHeap($Heap);
    // ----- call
    assert stack0o != null;
    call parts := System.String.Split$System.Char.array(stack0o, stack1o);
    // ----- copy  ----- Program.ssc(55,21)
    stack0o := parts;
    // ----- unary operator  ----- Program.ssc(55,21)
    assert stack0o != null;
    stack0i := $Length(stack0o);
    // ----- unary operator  ----- Program.ssc(55,21)
    stack0i := $IntToInt(stack0i, System.UIntPtr, System.Int32);
    // ----- load constant 2  ----- Program.ssc(55,21)
    stack1i := 2;
    // ----- binary operator  ----- Program.ssc(55,21)
    // ----- branch  ----- Program.ssc(55,21)
    goto true2720to2754, false2720to2737;

  true2720to2754:
    assume stack0i >= stack1i;
    goto block2754;

  false2720to2737:
    assume stack0i < stack1i;
    goto block2737;

  block2754:
    // ----- copy  ----- Program.ssc(58,25)
    stack0o := parts;
    // ----- load constant 0  ----- Program.ssc(58,25)
    stack1i := 0;
    // ----- load element  ----- Program.ssc(58,25)
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    local9 := RefArrayGet($Heap[stack0o, $elements], stack1i);
    // ----- copy  ----- Program.ssc(58,25)
    stack0o := local9;
    // ----- call  ----- Program.ssc(58,25)
    call padAmount := System.Int32.Parse$System.String$notnull(stack0o);
    // ----- copy  ----- Program.ssc(59,21)
    stack0o := parts;
    // ----- load constant 1  ----- Program.ssc(59,21)
    stack1i := 1;
    // ----- load element  ----- Program.ssc(59,21)
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    stack0o := RefArrayGet($Heap[stack0o, $elements], stack1i);
    // ----- copy  ----- Program.ssc(59,21)
    stack1i := padAmount;
    // ----- call  ----- Program.ssc(59,21)
    assert stack0o != null;
    call stack0o := System.String.PadLeft$System.Int32(stack0o, stack1i);
    // ----- call  ----- Program.ssc(59,21)
    assert writer != null;
    call System.IO.TextWriter.WriteLine$System.String$.Virtual.$(writer, stack0o);
    // ----- branch  ----- Program.ssc(60,18)
    goto block2703;

  block2737:
    // ----- branch  ----- Program.ssc(55,43)
    goto block2822;

  block2839:
    // ----- copy
    local10 := writer;
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true2839to2856, false2839to2873;

  true2839to2856:
    assume local10 == stack0o;
    goto block2856;

  false2839to2873:
    assume local10 != stack0o;
    goto block2873;

  block2856:
    // ----- nop
    // ----- branch
    goto block2788;

  block2873:
    // ----- call
    assert local10 != null;
    call System.IDisposable.Dispose$.Virtual.$(local10);
    goto block2856;

  block2822:
    // ----- copy
    local10 := writer;
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true2822to2924, false2822to2907;

  true2822to2924:
    assume local10 == stack0o;
    goto block2924;

  false2822to2907:
    assume local10 != stack0o;
    goto block2907;

  block2924:
    // ----- nop
    // ----- branch
    goto block2788;

  block2907:
    // ----- call
    assert local10 != null;
    call System.IDisposable.Dispose$.Virtual.$(local10);
    goto block2924;

  block2703$LoopPreheader:
    $Heap$block2703$LoopPreheader := $Heap;
    goto block2703;
}



procedure System.Environment.GetEnvironmentVariable$System.String$notnull(variable$in: ref where $IsNotNull(variable$in, System.String) && $Heap[variable$in, $allocated]) returns ($result: ref where $Is($result, System.String) && $Heap[$result, $allocated]);
  // user-declared preconditions
  requires variable$in != null;
  // variable is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[variable$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[variable$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // variable is peer consistent (owner must not be valid)
  requires $Heap[variable$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[variable$in, $ownerRef], $inv] <: $Heap[variable$in, $ownerFrame]) || $Heap[$Heap[variable$in, $ownerRef], $localinv] == $BaseClass($Heap[variable$in, $ownerFrame]);
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // return value is peer consistent
  ensures $result == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // return value is peer consistent (owner must not be valid)
  ensures $result == null || $Heap[$result, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[$result, $ownerRef], $inv] <: $Heap[$result, $ownerFrame]) || $Heap[$Heap[$result, $ownerRef], $localinv] == $BaseClass($Heap[$result, $ownerFrame]);
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



procedure System.IO.Path.GetTempPath() returns ($result: ref where $IsNotNull($result, System.String) && $Heap[$result, $allocated]);
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // return value is peer consistent
  ensures (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // return value is peer consistent (owner must not be valid)
  ensures $Heap[$result, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[$result, $ownerRef], $inv] <: $Heap[$result, $ownerFrame]) || $Heap[$Heap[$result, $ownerRef], $localinv] == $BaseClass($Heap[$result, $ownerFrame]);
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



// purity axiom (confined)
axiom $PurityAxiomsCanBeAssumed ==> (forall $Heap: [ref,<x>name]x, this: ref, oldValue$in: ref, newValue$in: ref :: { #System.String.Replace$System.String$notnull$System.String($Heap, this, oldValue$in, newValue$in) } IsHeap($Heap) && $IsNotNull(this, System.String) && $Heap[this, $allocated] && $IsNotNull(oldValue$in, System.String) && $Heap[oldValue$in, $allocated] && $Is(newValue$in, System.String) && $Heap[newValue$in, $allocated] && oldValue$in != null && $StringLength(oldValue$in) > 0 && (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)) && (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[oldValue$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[oldValue$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)) && (newValue$in == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[newValue$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[newValue$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc))) ==> $IsNotNull(#System.String.Replace$System.String$notnull$System.String($Heap, this, oldValue$in, newValue$in), System.String) && $Heap[#System.String.Replace$System.String$notnull$System.String($Heap, this, oldValue$in, newValue$in), $allocated] && ($Heap[this, $ownerFrame] != $PeerGroupPlaceholder ==> ($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame] && $Heap[$Heap[this, $ownerRef], $localinv] != $BaseClass($Heap[this, $ownerFrame]) ==> $Heap[this, $FirstConsistentOwner] == $Heap[this, $ownerRef]) && (!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame] && $Heap[$Heap[this, $ownerRef], $localinv] != $BaseClass($Heap[this, $ownerFrame])) ==> $Heap[this, $FirstConsistentOwner] == $Heap[$Heap[this, $ownerRef], $FirstConsistentOwner])) && $AsPureObject(this) == this && $AsPureObject(oldValue$in) == oldValue$in && $AsPureObject(newValue$in) == newValue$in && (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[#System.String.Replace$System.String$notnull$System.String($Heap, this, oldValue$in, newValue$in), $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[#System.String.Replace$System.String$notnull$System.String($Heap, this, oldValue$in, newValue$in), $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)));

// expose version axiom for confined methods
axiom (forall $Heap: [ref,<x>name]x, this: ref, oldValue$in: ref, newValue$in: ref :: { #System.String.Replace$System.String$notnull$System.String($Heap, this, oldValue$in, newValue$in) } this != null && $typeof(this) <: System.String && $Heap[this, $inv] == $typeof(this) && $Heap[this, $localinv] == $typeof(this) && IsHeap($Heap) && $Heap[this, $allocated] ==> #System.String.Replace$System.String$notnull$System.String($Heap, this, oldValue$in, newValue$in) == ##System.String.Replace$System.String$notnull$System.String($Heap[this, $exposeVersion], oldValue$in, newValue$in));

procedure System.String.Replace$System.String$notnull$System.String(this: ref where $IsNotNull(this, System.String) && $Heap[this, $allocated], oldValue$in: ref where $IsNotNull(oldValue$in, System.String) && $Heap[oldValue$in, $allocated], newValue$in: ref where $Is(newValue$in, System.String) && $Heap[newValue$in, $allocated]) returns ($result: ref where $IsNotNull($result, System.String) && $Heap[$result, $allocated]);
  // user-declared preconditions
  requires oldValue$in != null;
  requires $StringLength(oldValue$in) > 0;
  // target object is peer valid (pure method)
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // parameter of a pure method
  free requires $AsPureObject(this) == this;
  // oldValue is peer valid (pure method)
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[oldValue$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[oldValue$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // parameter of a pure method
  free requires $AsPureObject(oldValue$in) == oldValue$in;
  // newValue is peer valid (pure method)
  requires newValue$in == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[newValue$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[newValue$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // parameter of a pure method
  free requires $AsPureObject(newValue$in) == newValue$in;
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // FCO info about pure receiver
  free ensures $Heap[this, $ownerFrame] != $PeerGroupPlaceholder ==> ($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame] && $Heap[$Heap[this, $ownerRef], $localinv] != $BaseClass($Heap[this, $ownerFrame]) ==> $Heap[this, $FirstConsistentOwner] == $Heap[this, $ownerRef]) && (!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame] && $Heap[$Heap[this, $ownerRef], $localinv] != $BaseClass($Heap[this, $ownerFrame])) ==> $Heap[this, $FirstConsistentOwner] == $Heap[$Heap[this, $ownerRef], $FirstConsistentOwner]);
  // parameter of a pure method
  free ensures $AsPureObject(this) == this;
  // parameter of a pure method
  free ensures $AsPureObject(oldValue$in) == oldValue$in;
  // parameter of a pure method
  free ensures $AsPureObject(newValue$in) == newValue$in;
  // return value is peer valid (pure method)
  ensures (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  free ensures $result == #System.String.Replace$System.String$notnull$System.String($Heap, this, oldValue$in, newValue$in);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



axiom System.IO.StreamWriter <: System.IO.StreamWriter;

axiom System.IO.TextWriter <: System.IO.TextWriter;

axiom System.MarshalByRefObject <: System.MarshalByRefObject;

axiom $BaseClass(System.MarshalByRefObject) == System.Object && AsDirectSubClass(System.MarshalByRefObject, $BaseClass(System.MarshalByRefObject)) == System.MarshalByRefObject;

axiom !$IsImmutable(System.MarshalByRefObject) && $AsMutable(System.MarshalByRefObject) == System.MarshalByRefObject;

axiom $IsMemberlessType(System.MarshalByRefObject);

// System.MarshalByRefObject object invariant
axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: System.MarshalByRefObject } IsHeap($h) && $h[$oi, $inv] <: System.MarshalByRefObject && $h[$oi, $localinv] != $BaseClass(System.MarshalByRefObject) ==> true);

axiom $BaseClass(System.IO.TextWriter) == System.MarshalByRefObject && AsDirectSubClass(System.IO.TextWriter, $BaseClass(System.IO.TextWriter)) == System.IO.TextWriter;

axiom !$IsImmutable(System.IO.TextWriter) && $AsMutable(System.IO.TextWriter) == System.IO.TextWriter;

axiom System.IDisposable <: System.IDisposable;

axiom System.IDisposable <: System.Object;

axiom $IsMemberlessType(System.IDisposable);

axiom $AsInterface(System.IDisposable) == System.IDisposable;

axiom System.IO.TextWriter <: System.IDisposable;

axiom $IsMemberlessType(System.IO.TextWriter);

// System.IO.TextWriter object invariant
axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: System.IO.TextWriter } IsHeap($h) && $h[$oi, $inv] <: System.IO.TextWriter && $h[$oi, $localinv] != $BaseClass(System.IO.TextWriter) ==> true);

axiom $BaseClass(System.IO.StreamWriter) == System.IO.TextWriter && AsDirectSubClass(System.IO.StreamWriter, $BaseClass(System.IO.StreamWriter)) == System.IO.StreamWriter;

axiom !$IsImmutable(System.IO.StreamWriter) && $AsMutable(System.IO.StreamWriter) == System.IO.StreamWriter;

// System.IO.StreamWriter object invariant
axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: System.IO.StreamWriter } IsHeap($h) && $h[$oi, $inv] <: System.IO.StreamWriter && $h[$oi, $localinv] != $BaseClass(System.IO.StreamWriter) ==> true);

procedure System.IO.StreamWriter..ctor$System.String$notnull(this: ref where $IsNotNull(this, System.IO.StreamWriter) && $Heap[this, $allocated], path$in: ref where $IsNotNull(path$in, System.String) && $Heap[path$in, $allocated]);
  // object is fully unpacked:  this.inv == Object
  free requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
  // user-declared preconditions
  requires path$in != null;
  // path is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[path$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[path$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // path is peer consistent (owner must not be valid)
  requires $Heap[path$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[path$in, $ownerRef], $inv] <: $Heap[path$in, $ownerFrame]) || $Heap[$Heap[path$in, $ownerRef], $localinv] == $BaseClass($Heap[path$in, $ownerFrame]);
  // nothing is owned by [this,*] and 'this' is alone in its own peer group
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this) && $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires $BeingConstructed == this;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // target object is allocated upon return
  free ensures $Heap[this, $allocated];
  // target object is additively exposable for System.IO.StreamWriter
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.IO.StreamWriter && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(System.IO.StreamWriter <: DeclType($f))) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] && $o != this ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



axiom System.IO.TextReader <: System.IO.TextReader;

axiom $BaseClass(System.IO.TextReader) == System.MarshalByRefObject && AsDirectSubClass(System.IO.TextReader, $BaseClass(System.IO.TextReader)) == System.IO.TextReader;

axiom !$IsImmutable(System.IO.TextReader) && $AsMutable(System.IO.TextReader) == System.IO.TextReader;

axiom System.IO.TextReader <: System.IDisposable;

axiom $IsMemberlessType(System.IO.TextReader);

// System.IO.TextReader object invariant
axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: System.IO.TextReader } IsHeap($h) && $h[$oi, $inv] <: System.IO.TextReader && $h[$oi, $localinv] != $BaseClass(System.IO.TextReader) ==> true);

// purity axiom (state independent)
axiom $PurityAxiomsCanBeAssumed ==> (forall $Heap: [ref,<x>name]x :: { #System.Console.get_In($Heap) } IsHeap($Heap) ==> $IsNotNull(#System.Console.get_In($Heap), System.IO.TextReader) && $Heap[#System.Console.get_In($Heap), $allocated] && ($Heap[#System.Console.get_In($Heap), $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[#System.Console.get_In($Heap), $ownerRef], $inv] <: $Heap[#System.Console.get_In($Heap), $ownerFrame]) || $Heap[$Heap[#System.Console.get_In($Heap), $ownerRef], $localinv] == $BaseClass($Heap[#System.Console.get_In($Heap), $ownerFrame])) && (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[#System.Console.get_In($Heap), $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[#System.Console.get_In($Heap), $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)) && (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[#System.Console.get_In($Heap), $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[#System.Console.get_In($Heap), $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)));

// state-independent methods do not depend on the heap
axiom (forall $Heap: [ref,<x>name]x :: { #System.Console.get_In($Heap) } #System.Console.get_In($Heap) == ##System.Console.get_In());

procedure System.Console.get_In() returns ($result: ref where $IsNotNull($result, System.IO.TextReader) && $Heap[$result, $allocated]);
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // user-declared postconditions
  ensures ($Heap[$result, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[$result, $ownerRef], $inv] <: $Heap[$result, $ownerFrame]) || $Heap[$Heap[$result, $ownerRef], $localinv] == $BaseClass($Heap[$result, $ownerFrame])) && (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // return value is peer valid (pure method)
  ensures (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  free ensures $result == #System.Console.get_In($Heap);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



procedure System.IO.TextReader.ReadLine$.Virtual.$(this: ref where $IsNotNull(this, System.IO.TextReader) && $Heap[this, $allocated]) returns ($result: ref where $Is($result, System.String) && $Heap[$result, $allocated]);
  // target object is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // target object is peer consistent (owner must not be valid)
  requires $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // return value is peer consistent
  ensures $result == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // return value is peer consistent (owner must not be valid)
  ensures $result == null || $Heap[$result, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[$result, $ownerRef], $inv] <: $Heap[$result, $ownerFrame]) || $Heap[$Heap[$result, $ownerRef], $localinv] == $BaseClass($Heap[$result, $ownerFrame]);
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || !($typeof(this) <: DeclType($f)) || !$IncludedInModifiesStar($f)) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



procedure System.Object..ctor(this: ref where $IsNotNull(this, System.Object) && $Heap[this, $allocated]);
  // object is fully unpacked:  this.inv == Object
  free requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
  // nothing is owned by [this,*] and 'this' is alone in its own peer group
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this) && $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires $BeingConstructed == this;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // target object is allocated upon return
  free ensures $Heap[this, $allocated];
  // target object is additively exposable for System.Object
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(System.Object <: DeclType($f))) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] && $o != this ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



procedure System.String.Split$System.Char.array(this: ref where $IsNotNull(this, System.String) && $Heap[this, $allocated], param0$in: ref where $Is(param0$in, IntArray(System.Char, 1)) && $Heap[param0$in, $allocated]) returns ($result: ref where $Is($result, RefArray(System.String, 1)) && $Heap[$result, $allocated]);
  // target object is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // target object is peer consistent (owner must not be valid)
  requires $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
  //  is peer consistent
  requires param0$in == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[param0$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[param0$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  //  is peer consistent (owner must not be valid)
  requires param0$in == null || $Heap[param0$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[param0$in, $ownerRef], $inv] <: $Heap[param0$in, $ownerFrame]) || $Heap[$Heap[param0$in, $ownerRef], $localinv] == $BaseClass($Heap[param0$in, $ownerFrame]);
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // return value is peer consistent
  ensures $result == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // return value is peer consistent (owner must not be valid)
  ensures $result == null || $Heap[$result, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[$result, $ownerRef], $inv] <: $Heap[$result, $ownerFrame]) || $Heap[$Heap[$result, $ownerRef], $localinv] == $BaseClass($Heap[$result, $ownerFrame]);
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



procedure System.Int32.Parse$System.String$notnull(s$in: ref where $IsNotNull(s$in, System.String) && $Heap[s$in, $allocated]) returns ($result: int where InRange($result, System.Int32));
  // user-declared preconditions
  requires s$in != null;
  // s is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[s$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[s$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // s is peer consistent (owner must not be valid)
  requires $Heap[s$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[s$in, $ownerRef], $inv] <: $Heap[s$in, $ownerFrame]) || $Heap[$Heap[s$in, $ownerRef], $localinv] == $BaseClass($Heap[s$in, $ownerFrame]);
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



// purity axiom (confined)
axiom $PurityAxiomsCanBeAssumed ==> (forall $Heap: [ref,<x>name]x, this: ref, totalWidth$in: int :: { #System.String.PadLeft$System.Int32($Heap, this, totalWidth$in) } IsHeap($Heap) && $IsNotNull(this, System.String) && $Heap[this, $allocated] && totalWidth$in >= 0 && (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)) ==> $IsNotNull(#System.String.PadLeft$System.Int32($Heap, this, totalWidth$in), System.String) && $Heap[#System.String.PadLeft$System.Int32($Heap, this, totalWidth$in), $allocated] && $StringLength(#System.String.PadLeft$System.Int32($Heap, this, totalWidth$in)) == totalWidth$in && ($Heap[this, $ownerFrame] != $PeerGroupPlaceholder ==> ($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame] && $Heap[$Heap[this, $ownerRef], $localinv] != $BaseClass($Heap[this, $ownerFrame]) ==> $Heap[this, $FirstConsistentOwner] == $Heap[this, $ownerRef]) && (!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame] && $Heap[$Heap[this, $ownerRef], $localinv] != $BaseClass($Heap[this, $ownerFrame])) ==> $Heap[this, $FirstConsistentOwner] == $Heap[$Heap[this, $ownerRef], $FirstConsistentOwner])) && $AsPureObject(this) == this && (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[#System.String.PadLeft$System.Int32($Heap, this, totalWidth$in), $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[#System.String.PadLeft$System.Int32($Heap, this, totalWidth$in), $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)));

// expose version axiom for confined methods
axiom (forall $Heap: [ref,<x>name]x, this: ref, totalWidth$in: int :: { #System.String.PadLeft$System.Int32($Heap, this, totalWidth$in) } this != null && $typeof(this) <: System.String && $Heap[this, $inv] == $typeof(this) && $Heap[this, $localinv] == $typeof(this) && IsHeap($Heap) && $Heap[this, $allocated] ==> #System.String.PadLeft$System.Int32($Heap, this, totalWidth$in) == ##System.String.PadLeft$System.Int32($Heap[this, $exposeVersion], totalWidth$in));

procedure System.String.PadLeft$System.Int32(this: ref where $IsNotNull(this, System.String) && $Heap[this, $allocated], totalWidth$in: int where InRange(totalWidth$in, System.Int32)) returns ($result: ref where $IsNotNull($result, System.String) && $Heap[$result, $allocated]);
  // user-declared preconditions
  requires totalWidth$in >= 0;
  // target object is peer valid (pure method)
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // parameter of a pure method
  free requires $AsPureObject(this) == this;
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // user-declared postconditions
  ensures $StringLength($result) == totalWidth$in;
  // FCO info about pure receiver
  free ensures $Heap[this, $ownerFrame] != $PeerGroupPlaceholder ==> ($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame] && $Heap[$Heap[this, $ownerRef], $localinv] != $BaseClass($Heap[this, $ownerFrame]) ==> $Heap[this, $FirstConsistentOwner] == $Heap[this, $ownerRef]) && (!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame] && $Heap[$Heap[this, $ownerRef], $localinv] != $BaseClass($Heap[this, $ownerFrame])) ==> $Heap[this, $FirstConsistentOwner] == $Heap[$Heap[this, $ownerRef], $FirstConsistentOwner]);
  // parameter of a pure method
  free ensures $AsPureObject(this) == this;
  // return value is peer valid (pure method)
  ensures (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  free ensures $result == #System.String.PadLeft$System.Int32($Heap, this, totalWidth$in);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



procedure System.IO.TextWriter.WriteLine$System.String$.Virtual.$(this: ref where $IsNotNull(this, System.IO.TextWriter) && $Heap[this, $allocated], value$in: ref where $Is(value$in, System.String) && $Heap[value$in, $allocated]);
  // target object is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // target object is peer consistent (owner must not be valid)
  requires $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
  // value is peer consistent
  requires value$in == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[value$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[value$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // value is peer consistent (owner must not be valid)
  requires value$in == null || $Heap[value$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[value$in, $ownerRef], $inv] <: $Heap[value$in, $ownerFrame]) || $Heap[$Heap[value$in, $ownerRef], $localinv] == $BaseClass($Heap[value$in, $ownerFrame]);
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || !($typeof(this) <: DeclType($f)) || !$IncludedInModifiesStar($f)) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



procedure System.IDisposable.Dispose$.Virtual.$(this: ref where $IsNotNull(this, System.IDisposable) && $Heap[this, $allocated]);
  // target object is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // target object is peer consistent (owner must not be valid)
  requires $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || !($typeof(this) <: DeclType($f)) || !$IncludedInModifiesStar($f)) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



procedure Play.Program..ctor(this: ref where $IsNotNull(this, Play.Program) && $Heap[this, $allocated]);
  // object is fully unpacked:  this.inv == Object
  free requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
  // nothing is owned by [this,*] and 'this' is alone in its own peer group
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this) && $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires $BeingConstructed == this;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // target object is allocated upon return
  free ensures $Heap[this, $allocated];
  // target object is additively exposable for Play.Program
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == Play.Program && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(Play.Program <: DeclType($f))) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] && $o != this ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Play.Program..ctor(this: ref)
{

  entry:
    goto block5525;

  block5525:
    goto block5542;

  block5542:
    // ----- call  ----- Program.ssc(23,18)
    assert this != null;
    call System.Object..ctor(this);
    // ----- return
    // ----- translation-inserted post-constructor pack
    assert this != null;
    assert $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == Play.Program ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[this, $inv] := Play.Program;
    assume IsHeap($Heap);
    return;
}



const unique $stringLiteral0: ref;

// $stringLiteral0 is allocated, interned, and has the appropriate type and length
axiom $IsNotNull($stringLiteral0, System.String) && $StringLength($stringLiteral0) == 4 && (forall heap: [ref,<x>name]x :: { heap[$stringLiteral0, $allocated] } IsHeap(heap) ==> heap[$stringLiteral0, $allocated]) && (forall heap: [ref,<x>name]x :: { #System.String.IsInterned$System.String$notnull(heap, $stringLiteral0) } IsHeap(heap) ==> #System.String.IsInterned$System.String$notnull(heap, $stringLiteral0) == $stringLiteral0);
