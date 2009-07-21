// Spec# program verifier version 0.90, Copyright (c) 2003-2008, Microsoft.
// Command Line Options: /print:00.bpl ArrayList.exe

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

const unique Collections.ArrayList._size: <int>name;

const unique Collections.ArrayList._items: <ref>name;

const unique System.Collections.Comparer.Default: <ref>name;

const unique System.Runtime.Serialization.ISerializable: name;

const unique System.IComparable`1...System.String: name;

const unique Collections.TestArrayList: name;

const unique System.Runtime.InteropServices._Exception: name;

const unique System.Collections.Comparer: name;

const unique System.Collections.Generic.IEnumerable`1...System.Char: name;

const unique System.Collections.IList: name;

const unique System.Reflection.ICustomAttributeProvider: name;

const unique System.Collections.IEnumerable: name;

const unique System.IComparable: name;

const unique System.Collections.IComparer: name;

const unique System.IEquatable`1...System.String: name;

const unique System.Collections.ICollection: name;

const unique System.IConvertible: name;

const unique Microsoft.Contracts.ICheckedException: name;

const unique Microsoft.Contracts.ObjectInvariantException: name;

const unique System.Reflection.MemberInfo: name;

const unique System.Exception: name;

const unique System.Runtime.InteropServices._MemberInfo: name;

const unique Collections.ArrayList: name;

const unique System.Runtime.InteropServices._Type: name;

const unique Microsoft.Contracts.GuardException: name;

const unique System.Reflection.IReflect: name;

const unique System.ICloneable: name;

axiom !IsStaticField(Collections.ArrayList._items);

axiom IncludeInMainFrameCondition(Collections.ArrayList._items);

axiom $IncludedInModifiesStar(Collections.ArrayList._items);

axiom AsRepField(Collections.ArrayList._items, Collections.ArrayList) == Collections.ArrayList._items;

axiom DeclType(Collections.ArrayList._items) == Collections.ArrayList;

axiom AsNonNullRefField(Collections.ArrayList._items, RefArray(System.Object, 1)) == Collections.ArrayList._items;

axiom !IsStaticField(Collections.ArrayList._size);

axiom IncludeInMainFrameCondition(Collections.ArrayList._size);

axiom $IncludedInModifiesStar(Collections.ArrayList._size);

axiom DeclType(Collections.ArrayList._size) == Collections.ArrayList;

axiom AsRangeField(Collections.ArrayList._size, System.Int32) == Collections.ArrayList._size;

function #System.Collections.ICollection.get_Count([ref,<x>name]x, ref) returns (int);

function ##System.Collections.ICollection.get_Count(exposeVersionType) returns (int);

function #Collections.ArrayList.get_Capacity([ref,<x>name]x, ref) returns (int);

function ##Collections.ArrayList.get_Capacity(exposeVersionType) returns (int);

function #Collections.ArrayList.get_Count([ref,<x>name]x, ref) returns (int);

function ##Collections.ArrayList.get_Count(exposeVersionType) returns (int);

function #Collections.ArrayList.get_Item$System.Int32([ref,<x>name]x, ref, int) returns (ref);

function ##Collections.ArrayList.get_Item$System.Int32(exposeVersionType, int) returns (ref);

axiom IsStaticField(System.Collections.Comparer.Default);

axiom !IncludeInMainFrameCondition(System.Collections.Comparer.Default);

axiom $IncludedInModifiesStar(System.Collections.Comparer.Default);

axiom DeclType(System.Collections.Comparer.Default) == System.Collections.Comparer;

axiom AsNonNullRefField(System.Collections.Comparer.Default, System.Collections.Comparer) == System.Collections.Comparer.Default;

axiom Collections.ArrayList <: Collections.ArrayList;

axiom $BaseClass(Collections.ArrayList) == System.Object && AsDirectSubClass(Collections.ArrayList, $BaseClass(Collections.ArrayList)) == Collections.ArrayList;

axiom !$IsImmutable(Collections.ArrayList) && $AsMutable(Collections.ArrayList) == Collections.ArrayList;

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

axiom System.Type <: System.Type;

axiom System.Reflection.MemberInfo <: System.Reflection.MemberInfo;

axiom $BaseClass(System.Reflection.MemberInfo) == System.Object && AsDirectSubClass(System.Reflection.MemberInfo, $BaseClass(System.Reflection.MemberInfo)) == System.Reflection.MemberInfo;

axiom $IsImmutable(System.Reflection.MemberInfo) && $AsImmutable(System.Reflection.MemberInfo) == System.Reflection.MemberInfo;

axiom System.Reflection.ICustomAttributeProvider <: System.Reflection.ICustomAttributeProvider;

axiom System.Reflection.ICustomAttributeProvider <: System.Object;

axiom $IsMemberlessType(System.Reflection.ICustomAttributeProvider);

axiom $AsInterface(System.Reflection.ICustomAttributeProvider) == System.Reflection.ICustomAttributeProvider;

axiom System.Reflection.MemberInfo <: System.Reflection.ICustomAttributeProvider;

axiom System.Runtime.InteropServices._MemberInfo <: System.Runtime.InteropServices._MemberInfo;

axiom System.Runtime.InteropServices._MemberInfo <: System.Object;

axiom $IsMemberlessType(System.Runtime.InteropServices._MemberInfo);

axiom $AsInterface(System.Runtime.InteropServices._MemberInfo) == System.Runtime.InteropServices._MemberInfo;

axiom System.Reflection.MemberInfo <: System.Runtime.InteropServices._MemberInfo;

axiom $IsMemberlessType(System.Reflection.MemberInfo);

// System.Reflection.MemberInfo object invariant
axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: System.Reflection.MemberInfo } IsHeap($h) && $h[$oi, $inv] <: System.Reflection.MemberInfo && $h[$oi, $localinv] != $BaseClass(System.Reflection.MemberInfo) ==> true);

axiom $BaseClass(System.Type) == System.Reflection.MemberInfo && AsDirectSubClass(System.Type, $BaseClass(System.Type)) == System.Type;

axiom $IsImmutable(System.Type) && $AsImmutable(System.Type) == System.Type;

axiom System.Runtime.InteropServices._Type <: System.Runtime.InteropServices._Type;

axiom System.Runtime.InteropServices._Type <: System.Object;

axiom $IsMemberlessType(System.Runtime.InteropServices._Type);

axiom $AsInterface(System.Runtime.InteropServices._Type) == System.Runtime.InteropServices._Type;

axiom System.Type <: System.Runtime.InteropServices._Type;

axiom System.Reflection.IReflect <: System.Reflection.IReflect;

axiom System.Reflection.IReflect <: System.Object;

axiom $IsMemberlessType(System.Reflection.IReflect);

axiom $AsInterface(System.Reflection.IReflect) == System.Reflection.IReflect;

axiom System.Type <: System.Reflection.IReflect;

axiom $IsMemberlessType(System.Type);

// System.Type object invariant
axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: System.Type } IsHeap($h) && $h[$oi, $inv] <: System.Type && $h[$oi, $localinv] != $BaseClass(System.Type) ==> true);

// Collections.ArrayList object invariant
axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: Collections.ArrayList } IsHeap($h) && $h[$oi, $inv] <: Collections.ArrayList && $h[$oi, $localinv] != $BaseClass(Collections.ArrayList) ==> TypeObject($typeof($h[$oi, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1)) && 0 <= $h[$oi, Collections.ArrayList._size] && $h[$oi, Collections.ArrayList._size] <= $Length($h[$oi, Collections.ArrayList._items]) && (forall ^i: int :: $h[$oi, Collections.ArrayList._size] <= ^i && ^i <= $Length($h[$oi, Collections.ArrayList._items]) - 1 ==> RefArrayGet($h[$h[$oi, Collections.ArrayList._items], $elements], ^i) == null));

procedure Collections.ArrayList.SpecSharp.CheckInvariant$System.Boolean(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], throwException$in: bool where true) returns ($result: bool where true);
  // user-declared preconditions
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this) && (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == Collections.ArrayList ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
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



implementation Collections.ArrayList.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool) returns ($result: bool)
{
  var throwException: bool where true, stack0o: ref, stack1s: struct, stack1o: ref, stack0b: bool, stack0i: int, stack1i: int, return.value: bool where true, stack50000o: ref, SS$Display.Return.Local: bool where true, local2: bool where true, i: int where InRange(i, System.Int32), $Heap$block3587$LoopPreheader: [ref,<x>name]x;

  entry:
    throwException := throwException$in;
    goto block3485;

  block3485:
    goto block4046;

  block4046:
    // ----- nop
    // ----- load field
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- System.Object.GetType
    stack0o := TypeObject($typeof(stack0o));
    // ----- load token
    havoc stack1s;
    assume $IsTokenForType(stack1s, RefArray(System.Object, 1));
    // ----- statically resolved GetTypeFromHandle call
    stack1o := TypeObject(RefArray(System.Object, 1));
    // ----- binary operator
    // ----- branch
    goto true4046to3655, false4046to3978;

  true4046to3655:
    assume stack0o == stack1o;
    goto block3655;

  false4046to3978:
    assume stack0o != stack1o;
    goto block3978;

  block3655:
    // ----- load constant 0
    stack0i := 0;
    // ----- load field
    assert this != null;
    stack1i := $Heap[this, Collections.ArrayList._size];
    // ----- binary operator
    // ----- branch
    goto true3655to3519, false3655to3689;

  block3978:
    // ----- copy
    stack0b := throwException;
    // ----- unary operator
    // ----- branch
    goto true3978to3876, false3978to3502;

  true3978to3876:
    assume !stack0b;
    goto block3876;

  false3978to3502:
    assume stack0b;
    goto block3502;

  block3876:
    // ----- load constant 0
    return.value := false;
    // ----- branch
    goto block3995;

  block3502:
    assume false;
    // ----- new object
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == Microsoft.Contracts.ObjectInvariantException;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    // ----- call
    assert stack50000o != null;
    call Microsoft.Contracts.ObjectInvariantException..ctor(stack50000o);
    // ----- copy
    stack0o := stack50000o;
    // ----- throw
    assert stack0o != null;
    assume false;
    return;

  true3655to3519:
    assume stack0i > stack1i;
    goto block3519;

  false3655to3689:
    assume stack0i <= stack1i;
    goto block3689;

  block3519:
    // ----- copy
    stack0b := throwException;
    // ----- unary operator
    // ----- branch
    goto true3519to3791, false3519to3757;

  block3689:
    // ----- load field
    assert this != null;
    stack0i := $Heap[this, Collections.ArrayList._size];
    // ----- load field
    assert this != null;
    stack1o := $Heap[this, Collections.ArrayList._items];
    // ----- unary operator
    assert stack1o != null;
    stack1i := $Length(stack1o);
    // ----- unary operator
    stack1i := $IntToInt(stack1i, System.UIntPtr, System.Int32);
    // ----- binary operator
    // ----- branch
    goto true3689to3519, false3689to3893;

  true3689to3519:
    assume stack0i > stack1i;
    goto block3519;

  false3689to3893:
    assume stack0i <= stack1i;
    goto block3893;

  block3893:
    // ----- branch
    goto block3672;

  true3519to3791:
    assume !stack0b;
    goto block3791;

  false3519to3757:
    assume stack0b;
    goto block3757;

  block3791:
    // ----- load constant 0
    return.value := false;
    // ----- branch
    goto block3995;

  block3757:
    assume false;
    // ----- new object  ----- ArrayList.ssc(21,5)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == Microsoft.Contracts.ObjectInvariantException;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    // ----- call  ----- ArrayList.ssc(21,5)
    assert stack50000o != null;
    call Microsoft.Contracts.ObjectInvariantException..ctor(stack50000o);
    // ----- copy  ----- ArrayList.ssc(21,5)
    stack0o := stack50000o;
    // ----- throw  ----- ArrayList.ssc(21,5)
    assert stack0o != null;
    assume false;
    return;

  block3995:
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0b := return.value;
    // ----- return
    $result := stack0b;
    return;

  block3672:
    // ----- load constant 1
    local2 := true;
    // ----- load field
    assert this != null;
    i := $Heap[this, Collections.ArrayList._size];
    goto block3587$LoopPreheader;

  block3587:
    // ----- serialized LoopInvariant
    assert $Heap[this, Collections.ArrayList._size] <= i;
    // ----- default loop invariant: allocation and ownership are stable
    assume (forall $o: ref :: { $Heap[$o, $allocated] } $Heap$block3587$LoopPreheader[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } $Heap$block3587$LoopPreheader[$ot, $allocated] && $Heap$block3587$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block3587$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block3587$LoopPreheader[$ot, $ownerFrame]) && $Heap$block3587$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: exposure
    assume (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $Heap$block3587$LoopPreheader[$o, $allocated] ==> $Heap$block3587$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block3587$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]);
    assume (forall $o: ref :: !$Heap$block3587$LoopPreheader[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: modifies
    assert (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || !($typeof(this) <: DeclType($f)) || !$IncludedInModifiesStar($f)) && old(true) ==> $Heap$block3587$LoopPreheader[$o, $f] == $Heap[$o, $f]);
    assume $HeapSucc($Heap$block3587$LoopPreheader, $Heap);
    // ----- default loop invariant: owner fields
    assert (forall $o: ref :: { $Heap[$o, $ownerFrame] } { $Heap[$o, $ownerRef] } $o != null && $Heap$block3587$LoopPreheader[$o, $allocated] ==> $Heap[$o, $ownerRef] == $Heap$block3587$LoopPreheader[$o, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap$block3587$LoopPreheader[$o, $ownerFrame]);
    // ----- advance activity
    havoc $ActivityIndicator;
    // ----- load field
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- unary operator
    assert stack0o != null;
    stack0i := $Length(stack0o);
    // ----- unary operator
    stack0i := $IntToInt(stack0i, System.UIntPtr, System.Int32);
    // ----- load constant 1
    stack1i := 1;
    // ----- binary operator
    stack0i := stack0i - stack1i;
    // ----- binary operator
    // ----- branch
    goto true3587to3944, false3587to3910;

  true3587to3944:
    assume i <= stack0i;
    goto block3944;

  false3587to3910:
    assume i > stack0i;
    goto block3910;

  block3944:
    // ----- load constant 1
    stack0b := true;
    goto block4029;

  block3910:
    // ----- load constant 0
    stack0b := false;
    // ----- branch
    goto block4029;

  block4029:
    // ----- unary operator
    // ----- branch
    goto true4029to3638, false4029to3825;

  true4029to3638:
    assume !stack0b;
    goto block3638;

  false4029to3825:
    assume stack0b;
    goto block3825;

  block3638:
    // ----- copy
    // ----- branch
    goto true3638to3808, false3638to3842;

  block3825:
    // ----- load field
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- copy
    stack1i := i;
    // ----- load element
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    stack0o := RefArrayGet($Heap[stack0o, $elements], stack1i);
    stack1o := null;
    // ----- binary operator
    // ----- branch
    goto true3825to4012, false3825to3774;

  true3638to3808:
    assume local2;
    goto block3808;

  false3638to3842:
    assume !local2;
    goto block3842;

  block3808:
    // ----- load constant 1
    return.value := true;
    // ----- branch
    goto block3995;

  block3842:
    // ----- copy
    stack0b := throwException;
    // ----- unary operator
    // ----- branch
    goto true3842to3723, false3842to3536;

  true3825to4012:
    assume stack0o == stack1o;
    goto block4012;

  false3825to3774:
    assume stack0o != stack1o;
    goto block3774;

  block4012:
    // ----- load constant 1
    stack0b := true;
    goto block3740;

  block3774:
    // ----- load constant 0
    stack0b := false;
    // ----- branch
    goto block3740;

  true3842to3723:
    assume !stack0b;
    goto block3723;

  false3842to3536:
    assume stack0b;
    goto block3536;

  block3723:
    // ----- load constant 0
    return.value := false;
    // ----- branch
    goto block3995;

  block3536:
    assume false;
    // ----- new object  ----- ArrayList.ssc(22,5)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == Microsoft.Contracts.ObjectInvariantException;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    // ----- call  ----- ArrayList.ssc(22,5)
    assert stack50000o != null;
    call Microsoft.Contracts.ObjectInvariantException..ctor(stack50000o);
    // ----- copy  ----- ArrayList.ssc(22,5)
    stack0o := stack50000o;
    // ----- throw  ----- ArrayList.ssc(22,5)
    assert stack0o != null;
    assume false;
    return;

  block3740:
    // ----- copy
    local2 := stack0b;
    // ----- copy
    // ----- branch
    goto true3740to3859, false3740to3927;

  true3740to3859:
    assume local2;
    goto block3859;

  false3740to3927:
    assume !local2;
    goto block3927;

  block3859:
    // ----- load constant 1
    stack0i := 1;
    // ----- binary operator
    stack0i := i + stack0i;
    // ----- copy
    i := stack0i;
    // ----- branch
    goto block3587;

  block3927:
    // ----- branch
    goto block3638;

  block3587$LoopPreheader:
    $Heap$block3587$LoopPreheader := $Heap;
    goto block3587;
}



axiom Microsoft.Contracts.ObjectInvariantException <: Microsoft.Contracts.ObjectInvariantException;

axiom Microsoft.Contracts.GuardException <: Microsoft.Contracts.GuardException;

axiom System.Exception <: System.Exception;

axiom $BaseClass(System.Exception) == System.Object && AsDirectSubClass(System.Exception, $BaseClass(System.Exception)) == System.Exception;

axiom !$IsImmutable(System.Exception) && $AsMutable(System.Exception) == System.Exception;

axiom System.Runtime.Serialization.ISerializable <: System.Runtime.Serialization.ISerializable;

axiom System.Runtime.Serialization.ISerializable <: System.Object;

axiom $IsMemberlessType(System.Runtime.Serialization.ISerializable);

axiom $AsInterface(System.Runtime.Serialization.ISerializable) == System.Runtime.Serialization.ISerializable;

axiom System.Exception <: System.Runtime.Serialization.ISerializable;

axiom System.Runtime.InteropServices._Exception <: System.Runtime.InteropServices._Exception;

axiom System.Runtime.InteropServices._Exception <: System.Object;

axiom $IsMemberlessType(System.Runtime.InteropServices._Exception);

axiom $AsInterface(System.Runtime.InteropServices._Exception) == System.Runtime.InteropServices._Exception;

axiom System.Exception <: System.Runtime.InteropServices._Exception;

// System.Exception object invariant
axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: System.Exception } IsHeap($h) && $h[$oi, $inv] <: System.Exception && $h[$oi, $localinv] != $BaseClass(System.Exception) ==> true);

axiom $BaseClass(Microsoft.Contracts.GuardException) == System.Exception && AsDirectSubClass(Microsoft.Contracts.GuardException, $BaseClass(Microsoft.Contracts.GuardException)) == Microsoft.Contracts.GuardException;

axiom !$IsImmutable(Microsoft.Contracts.GuardException) && $AsMutable(Microsoft.Contracts.GuardException) == Microsoft.Contracts.GuardException;

// Microsoft.Contracts.GuardException object invariant
axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: Microsoft.Contracts.GuardException } IsHeap($h) && $h[$oi, $inv] <: Microsoft.Contracts.GuardException && $h[$oi, $localinv] != $BaseClass(Microsoft.Contracts.GuardException) ==> true);

axiom $BaseClass(Microsoft.Contracts.ObjectInvariantException) == Microsoft.Contracts.GuardException && AsDirectSubClass(Microsoft.Contracts.ObjectInvariantException, $BaseClass(Microsoft.Contracts.ObjectInvariantException)) == Microsoft.Contracts.ObjectInvariantException;

axiom !$IsImmutable(Microsoft.Contracts.ObjectInvariantException) && $AsMutable(Microsoft.Contracts.ObjectInvariantException) == Microsoft.Contracts.ObjectInvariantException;

// Microsoft.Contracts.ObjectInvariantException object invariant
axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: Microsoft.Contracts.ObjectInvariantException } IsHeap($h) && $h[$oi, $inv] <: Microsoft.Contracts.ObjectInvariantException && $h[$oi, $localinv] != $BaseClass(Microsoft.Contracts.ObjectInvariantException) ==> true);

procedure Microsoft.Contracts.ObjectInvariantException..ctor(this: ref where $IsNotNull(this, Microsoft.Contracts.ObjectInvariantException) && $Heap[this, $allocated]);
  // object is fully unpacked:  this.inv == Object
  free requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
  // nothing is owned by [this,*] and 'this' is alone in its own peer group
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this) && $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires $BeingConstructed == this;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // target object is allocated upon return
  free ensures $Heap[this, $allocated];
  // target object is additively exposable for Microsoft.Contracts.ObjectInvariantException
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == Microsoft.Contracts.ObjectInvariantException && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(Microsoft.Contracts.ObjectInvariantException <: DeclType($f))) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] && $o != this ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



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

procedure Collections.ArrayList..ctor(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated]);
  // object is fully unpacked:  this.inv == Object
  free requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
  // nothing is owned by [this,*] and 'this' is alone in its own peer group
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this) && $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires $BeingConstructed == this;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // user-declared postconditions
  ensures $Heap[this, Collections.ArrayList._size] == 0;
  ensures $Length($Heap[this, Collections.ArrayList._items]) == 16;
  // target object is allocated upon return
  free ensures $Heap[this, $allocated];
  // target object is additively exposable for Collections.ArrayList
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == Collections.ArrayList && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(Collections.ArrayList <: DeclType($f))) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] && $o != this ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Collections.ArrayList..ctor(this: ref)
{
  var stack0i: int, stack0o: ref, temp0: ref, temp1: exposeVersionType, temp2: ref;

  entry:
    assume $Heap[this, Collections.ArrayList._size] == 0;
    goto block6698;

  block6698:
    goto block6732;

  block6732:
    // ----- load constant 16  ----- ArrayList.ssc(29,7)
    stack0i := 16;
    // ----- new array  ----- ArrayList.ssc(29,7)
    assert 0 <= stack0i;
    havoc temp0;
    assume $Heap[temp0, $allocated] == false && $Length(temp0) == stack0i;
    assume $Heap[$ElementProxy(temp0, -1), $allocated] == false && $ElementProxy(temp0, -1) != temp0 && $ElementProxy(temp0, -1) != null;
    assume temp0 != null;
    assume $typeof(temp0) == RefArray(System.Object, 1);
    assume $Heap[temp0, $ownerRef] == temp0 && $Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder;
    assume $Heap[$ElementProxy(temp0, -1), $ownerRef] == $ElementProxy(temp0, -1) && $Heap[$ElementProxy(temp0, -1), $ownerFrame] == $PeerGroupPlaceholder;
    assume $Heap[temp0, $inv] == $typeof(temp0) && $Heap[temp0, $localinv] == $typeof(temp0);
    assume (forall $i: int :: RefArrayGet($Heap[temp0, $elements], $i) == null);
    $Heap[temp0, $allocated] := true;
    call System.Object..ctor($ElementProxy(temp0, -1));
    stack0o := temp0;
    assume IsHeap($Heap);
    // ----- store field  ----- ArrayList.ssc(29,7)
    assert this != null;
    assert $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
    assert ($Heap[stack0o, $ownerRef] == this && $Heap[stack0o, $ownerFrame] == Collections.ArrayList) || $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder;
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder && $Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList) ==> (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[stack0o, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[stack0o, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder && $Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList) ==> $Heap[this, $ownerRef] != $Heap[stack0o, $ownerRef] || $Heap[this, $ownerFrame] != $Heap[stack0o, $ownerFrame];
    call $UpdateOwnersForRep(this, Collections.ArrayList, stack0o);
    havoc temp1;
    $Heap[this, $exposeVersion] := temp1;
    $Heap[this, Collections.ArrayList._items] := stack0o;
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || TypeObject($typeof($Heap[this, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || 0 <= $Heap[this, Collections.ArrayList._size];
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || $Heap[this, Collections.ArrayList._size] <= $Length($Heap[this, Collections.ArrayList._items]);
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || (forall ^i: int :: $Heap[this, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[this, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], ^i) == null);
    assume IsHeap($Heap);
    // ----- call  ----- ArrayList.ssc(30,7)
    assert this != null;
    call System.Object..ctor(this);
    $Heap[this, $NonNullFieldsAreInitialized] := true;
    assume IsHeap($Heap);
    goto block6851;

  block6851:
    // ----- FrameGuard processing  ----- ArrayList.ssc(31,5)
    temp2 := this;
    // ----- classic pack  ----- ArrayList.ssc(31,5)
    assert temp2 != null;
    assert $Heap[temp2, $inv] == System.Object && $Heap[temp2, $localinv] == $typeof(temp2);
    assert TypeObject($typeof($Heap[temp2, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert 0 <= $Heap[temp2, Collections.ArrayList._size];
    assert $Heap[temp2, Collections.ArrayList._size] <= $Length($Heap[temp2, Collections.ArrayList._items]);
    assert (forall ^i: int :: $Heap[temp2, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[temp2, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[temp2, Collections.ArrayList._items], $elements], ^i) == null);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == temp2 && $Heap[$p, $ownerFrame] == Collections.ArrayList ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp2, $inv] := Collections.ArrayList;
    assume IsHeap($Heap);
    goto block6800;

  block6800:
    // ----- nop
    // ----- return  ----- ArrayList.ssc(31,5)
    return;
}



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



procedure Collections.ArrayList..ctor$System.Int32(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], capacity$in: int where InRange(capacity$in, System.Int32));
  // object is fully unpacked:  this.inv == Object
  free requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
  // user-declared preconditions
  requires 0 <= capacity$in;
  // nothing is owned by [this,*] and 'this' is alone in its own peer group
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this) && $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires $BeingConstructed == this;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // user-declared postconditions
  ensures $Heap[this, Collections.ArrayList._size] == 0;
  ensures $Length($Heap[this, Collections.ArrayList._items]) == capacity$in;
  // target object is allocated upon return
  free ensures $Heap[this, $allocated];
  // target object is additively exposable for Collections.ArrayList
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == Collections.ArrayList && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(Collections.ArrayList <: DeclType($f))) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] && $o != this ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Collections.ArrayList..ctor$System.Int32(this: ref, capacity$in: int)
{
  var capacity: int where InRange(capacity, System.Int32), stack0i: int, stack0o: ref, temp0: ref, temp1: exposeVersionType, temp2: ref;

  entry:
    capacity := capacity$in;
    assume $Heap[this, Collections.ArrayList._size] == 0;
    goto block7565;

  block7565:
    goto block7599;

  block7599:
    // ----- nop
    // ----- copy  ----- ArrayList.ssc(40,7)
    stack0i := capacity;
    // ----- new array  ----- ArrayList.ssc(40,7)
    assert 0 <= stack0i;
    havoc temp0;
    assume $Heap[temp0, $allocated] == false && $Length(temp0) == stack0i;
    assume $Heap[$ElementProxy(temp0, -1), $allocated] == false && $ElementProxy(temp0, -1) != temp0 && $ElementProxy(temp0, -1) != null;
    assume temp0 != null;
    assume $typeof(temp0) == RefArray(System.Object, 1);
    assume $Heap[temp0, $ownerRef] == temp0 && $Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder;
    assume $Heap[$ElementProxy(temp0, -1), $ownerRef] == $ElementProxy(temp0, -1) && $Heap[$ElementProxy(temp0, -1), $ownerFrame] == $PeerGroupPlaceholder;
    assume $Heap[temp0, $inv] == $typeof(temp0) && $Heap[temp0, $localinv] == $typeof(temp0);
    assume (forall $i: int :: RefArrayGet($Heap[temp0, $elements], $i) == null);
    $Heap[temp0, $allocated] := true;
    call System.Object..ctor($ElementProxy(temp0, -1));
    stack0o := temp0;
    assume IsHeap($Heap);
    // ----- store field  ----- ArrayList.ssc(40,7)
    assert this != null;
    assert $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
    assert ($Heap[stack0o, $ownerRef] == this && $Heap[stack0o, $ownerFrame] == Collections.ArrayList) || $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder;
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder && $Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList) ==> (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[stack0o, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[stack0o, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder && $Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList) ==> $Heap[this, $ownerRef] != $Heap[stack0o, $ownerRef] || $Heap[this, $ownerFrame] != $Heap[stack0o, $ownerFrame];
    call $UpdateOwnersForRep(this, Collections.ArrayList, stack0o);
    havoc temp1;
    $Heap[this, $exposeVersion] := temp1;
    $Heap[this, Collections.ArrayList._items] := stack0o;
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || TypeObject($typeof($Heap[this, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || 0 <= $Heap[this, Collections.ArrayList._size];
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || $Heap[this, Collections.ArrayList._size] <= $Length($Heap[this, Collections.ArrayList._items]);
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || (forall ^i: int :: $Heap[this, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[this, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], ^i) == null);
    assume IsHeap($Heap);
    // ----- call  ----- ArrayList.ssc(41,7)
    assert this != null;
    call System.Object..ctor(this);
    $Heap[this, $NonNullFieldsAreInitialized] := true;
    assume IsHeap($Heap);
    goto block7888;

  block7888:
    // ----- FrameGuard processing  ----- ArrayList.ssc(42,5)
    temp2 := this;
    // ----- classic pack  ----- ArrayList.ssc(42,5)
    assert temp2 != null;
    assert $Heap[temp2, $inv] == System.Object && $Heap[temp2, $localinv] == $typeof(temp2);
    assert TypeObject($typeof($Heap[temp2, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert 0 <= $Heap[temp2, Collections.ArrayList._size];
    assert $Heap[temp2, Collections.ArrayList._size] <= $Length($Heap[temp2, Collections.ArrayList._items]);
    assert (forall ^i: int :: $Heap[temp2, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[temp2, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[temp2, Collections.ArrayList._items], $elements], ^i) == null);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == temp2 && $Heap[$p, $ownerFrame] == Collections.ArrayList ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp2, $inv] := Collections.ArrayList;
    assume IsHeap($Heap);
    goto block7735;

  block7735:
    // ----- nop
    // ----- return
    return;
}



// purity axiom (confined)
axiom $PurityAxiomsCanBeAssumed ==> (forall $Heap: [ref,<x>name]x, this: ref :: { #System.Collections.ICollection.get_Count($Heap, this) } IsHeap($Heap) && $IsNotNull(this, System.Collections.ICollection) && $Heap[this, $allocated] && (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)) ==> #System.Collections.ICollection.get_Count($Heap, this) >= 0 && ($Heap[this, $ownerFrame] != $PeerGroupPlaceholder ==> ($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame] && $Heap[$Heap[this, $ownerRef], $localinv] != $BaseClass($Heap[this, $ownerFrame]) ==> $Heap[this, $FirstConsistentOwner] == $Heap[this, $ownerRef]) && (!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame] && $Heap[$Heap[this, $ownerRef], $localinv] != $BaseClass($Heap[this, $ownerFrame])) ==> $Heap[this, $FirstConsistentOwner] == $Heap[$Heap[this, $ownerRef], $FirstConsistentOwner])) && $AsPureObject(this) == this);

// expose version axiom for confined methods
axiom (forall $Heap: [ref,<x>name]x, this: ref :: { #System.Collections.ICollection.get_Count($Heap, this) } this != null && $typeof(this) <: System.Collections.ICollection && $Heap[this, $inv] == $typeof(this) && $Heap[this, $localinv] == $typeof(this) && IsHeap($Heap) && $Heap[this, $allocated] ==> #System.Collections.ICollection.get_Count($Heap, this) == ##System.Collections.ICollection.get_Count($Heap[this, $exposeVersion]));

procedure Collections.ArrayList..ctor$System.Collections.ICollection$notnull(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], c$in: ref where $IsNotNull(c$in, System.Collections.ICollection) && $Heap[c$in, $allocated]);
  // object is fully unpacked:  this.inv == Object
  free requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
  // c is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[c$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[c$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // c is peer consistent (owner must not be valid)
  requires $Heap[c$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[c$in, $ownerRef], $inv] <: $Heap[c$in, $ownerFrame]) || $Heap[$Heap[c$in, $ownerRef], $localinv] == $BaseClass($Heap[c$in, $ownerFrame]);
  // nothing is owned by [this,*] and 'this' is alone in its own peer group
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this) && $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires $BeingConstructed == this;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // user-declared postconditions
  ensures $Heap[this, Collections.ArrayList._size] == #System.Collections.ICollection.get_Count($Heap, c$in);
  // target object is allocated upon return
  free ensures $Heap[this, $allocated];
  // target object is additively exposable for Collections.ArrayList
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == Collections.ArrayList && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(Collections.ArrayList <: DeclType($f))) && old($o != c$in || !($typeof(c$in) <: DeclType($f)) || !$IncludedInModifiesStar($f)) && old($o != c$in || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] && $o != this ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Collections.ArrayList..ctor$System.Collections.ICollection$notnull(this: ref, c$in: ref)
{
  var c: ref where $IsNotNull(c, System.Collections.ICollection) && $Heap[c, $allocated], stack0i: int, stack0o: ref, temp0: ref, temp1: exposeVersionType, stack1o: ref, temp2: ref;

  entry:
    c := c$in;
    assume $Heap[this, Collections.ArrayList._size] == 0;
    goto block8517;

  block8517:
    goto block8534;

  block8534:
    // ----- nop
    // ----- call  ----- ArrayList.ssc(50,7)
    assert c != null;
    call stack0i := System.Collections.ICollection.get_Count$.Virtual.$(c, false);
    // ----- new array  ----- ArrayList.ssc(50,7)
    assert 0 <= stack0i;
    havoc temp0;
    assume $Heap[temp0, $allocated] == false && $Length(temp0) == stack0i;
    assume $Heap[$ElementProxy(temp0, -1), $allocated] == false && $ElementProxy(temp0, -1) != temp0 && $ElementProxy(temp0, -1) != null;
    assume temp0 != null;
    assume $typeof(temp0) == RefArray(System.Object, 1);
    assume $Heap[temp0, $ownerRef] == temp0 && $Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder;
    assume $Heap[$ElementProxy(temp0, -1), $ownerRef] == $ElementProxy(temp0, -1) && $Heap[$ElementProxy(temp0, -1), $ownerFrame] == $PeerGroupPlaceholder;
    assume $Heap[temp0, $inv] == $typeof(temp0) && $Heap[temp0, $localinv] == $typeof(temp0);
    assume (forall $i: int :: RefArrayGet($Heap[temp0, $elements], $i) == null);
    $Heap[temp0, $allocated] := true;
    call System.Object..ctor($ElementProxy(temp0, -1));
    stack0o := temp0;
    assume IsHeap($Heap);
    // ----- store field  ----- ArrayList.ssc(50,7)
    assert this != null;
    assert $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
    assert ($Heap[stack0o, $ownerRef] == this && $Heap[stack0o, $ownerFrame] == Collections.ArrayList) || $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder;
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder && $Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList) ==> (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[stack0o, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[stack0o, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder && $Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList) ==> $Heap[this, $ownerRef] != $Heap[stack0o, $ownerRef] || $Heap[this, $ownerFrame] != $Heap[stack0o, $ownerFrame];
    call $UpdateOwnersForRep(this, Collections.ArrayList, stack0o);
    havoc temp1;
    $Heap[this, $exposeVersion] := temp1;
    $Heap[this, Collections.ArrayList._items] := stack0o;
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || TypeObject($typeof($Heap[this, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || 0 <= $Heap[this, Collections.ArrayList._size];
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || $Heap[this, Collections.ArrayList._size] <= $Length($Heap[this, Collections.ArrayList._items]);
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || (forall ^i: int :: $Heap[this, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[this, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], ^i) == null);
    assume IsHeap($Heap);
    // ----- call  ----- ArrayList.ssc(51,7)
    assert this != null;
    call System.Object..ctor(this);
    $Heap[this, $NonNullFieldsAreInitialized] := true;
    assume IsHeap($Heap);
    goto block8653;

  block8653:
    // ----- load constant 0  ----- ArrayList.ssc(52,7)
    stack0i := 0;
    // ----- copy  ----- ArrayList.ssc(52,7)
    stack1o := c;
    // ----- call  ----- ArrayList.ssc(52,7)
    assert this != null;
    call Collections.ArrayList.InsertRangeWorker$System.Int32$System.Collections.ICollection$notnull(this, stack0i, stack1o);
    // ----- FrameGuard processing  ----- ArrayList.ssc(53,5)
    temp2 := this;
    // ----- classic pack  ----- ArrayList.ssc(53,5)
    assert temp2 != null;
    assert $Heap[temp2, $inv] == System.Object && $Heap[temp2, $localinv] == $typeof(temp2);
    assert TypeObject($typeof($Heap[temp2, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert 0 <= $Heap[temp2, Collections.ArrayList._size];
    assert $Heap[temp2, Collections.ArrayList._size] <= $Length($Heap[temp2, Collections.ArrayList._items]);
    assert (forall ^i: int :: $Heap[temp2, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[temp2, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[temp2, Collections.ArrayList._items], $elements], ^i) == null);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == temp2 && $Heap[$p, $ownerFrame] == Collections.ArrayList ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp2, $inv] := Collections.ArrayList;
    assume IsHeap($Heap);
    goto block8687;

  block8687:
    // ----- nop
    // ----- return
    return;
}



procedure System.Collections.ICollection.get_Count$.Virtual.$(this: ref where $IsNotNull(this, System.Collections.ICollection) && $Heap[this, $allocated], $isBaseCall: bool) returns ($result: int where InRange($result, System.Int32));
  // target object is peer valid (pure method)
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // parameter of a pure method
  free requires $AsPureObject(this) == this;
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // user-declared postconditions
  ensures $result >= 0;
  // FCO info about pure receiver
  free ensures $Heap[this, $ownerFrame] != $PeerGroupPlaceholder ==> ($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame] && $Heap[$Heap[this, $ownerRef], $localinv] != $BaseClass($Heap[this, $ownerFrame]) ==> $Heap[this, $FirstConsistentOwner] == $Heap[this, $ownerRef]) && (!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame] && $Heap[$Heap[this, $ownerRef], $localinv] != $BaseClass($Heap[this, $ownerFrame])) ==> $Heap[this, $FirstConsistentOwner] == $Heap[$Heap[this, $ownerRef], $FirstConsistentOwner]);
  // parameter of a pure method
  free ensures $AsPureObject(this) == this;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  free ensures $Heap == old($Heap);
  free ensures $isBaseCall || $result == #System.Collections.ICollection.get_Count($Heap, this);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



procedure Collections.ArrayList.InsertRangeWorker$System.Int32$System.Collections.ICollection$notnull(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], index$in: int where InRange(index$in, System.Int32), c$in: ref where $IsNotNull(c$in, System.Collections.ICollection) && $Heap[c$in, $allocated]);
  // user-declared preconditions
  requires 0 <= index$in;
  requires index$in <= $Heap[this, Collections.ArrayList._size];
  requires $Heap[this, Collections.ArrayList._size] <= $Length($Heap[this, Collections.ArrayList._items]);
  requires ($Heap[$Heap[this, Collections.ArrayList._items], $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[$Heap[this, Collections.ArrayList._items], $ownerRef], $inv] <: $Heap[$Heap[this, Collections.ArrayList._items], $ownerFrame]) || $Heap[$Heap[$Heap[this, Collections.ArrayList._items], $ownerRef], $localinv] == $BaseClass($Heap[$Heap[this, Collections.ArrayList._items], $ownerFrame])) && (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[$Heap[this, Collections.ArrayList._items], $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[$Heap[this, Collections.ArrayList._items], $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires TypeObject($typeof($Heap[this, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
  requires (forall ^i: int :: $Heap[this, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[this, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], ^i) == null);
  // target object is exposed for Collections.ArrayList
  requires !($Heap[this, $inv] <: Collections.ArrayList) || $Heap[this, $localinv] == System.Object;
  // c is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[c$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[c$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // c is peer consistent (owner must not be valid)
  requires $Heap[c$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[c$in, $ownerRef], $inv] <: $Heap[c$in, $ownerFrame]) || $Heap[$Heap[c$in, $ownerRef], $localinv] == $BaseClass($Heap[c$in, $ownerFrame]);
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // user-declared postconditions
  ensures 0 <= $Heap[this, Collections.ArrayList._size];
  ensures $Heap[this, Collections.ArrayList._size] <= $Length($Heap[this, Collections.ArrayList._items]);
  ensures $Heap[this, Collections.ArrayList._size] == old($Heap[this, Collections.ArrayList._size] + #System.Collections.ICollection.get_Count($Heap, c$in));
  ensures TypeObject($typeof($Heap[this, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
  ensures (forall ^i: int :: $Heap[this, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[this, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], ^i) == null);
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(($o != $Heap[this, Collections.ArrayList._items] || !($typeof($Heap[this, Collections.ArrayList._items]) <: DeclType($f)) || !$IncludedInModifiesStar($f)) && ($o != c$in || !($typeof(c$in) <: DeclType($f)) || !$IncludedInModifiesStar($f)) && ($o != this || !($typeof(this) <: DeclType($f)) || !$IncludedInModifiesStar($f))) && old(($o != $Heap[this, Collections.ArrayList._items] || $f != $exposeVersion) && ($o != c$in || $f != $exposeVersion)) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



procedure Collections.ArrayList.Boogie.ContractConsistencyCheck.get_Capacity(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated]) returns ($result: int where InRange($result, System.Int32));
  // target object is peer valid (pure method)
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // parameter of a pure method
  free requires $AsPureObject(this) == this;
  free requires $BeingConstructed == null;
  modifies $Heap, $ActivityIndicator;
  // user-declared postconditions
  ensures 0 <= $result;
  // FCO info about pure receiver
  free ensures $Heap[this, $ownerFrame] != $PeerGroupPlaceholder ==> ($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame] && $Heap[$Heap[this, $ownerRef], $localinv] != $BaseClass($Heap[this, $ownerFrame]) ==> $Heap[this, $FirstConsistentOwner] == $Heap[this, $ownerRef]) && (!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame] && $Heap[$Heap[this, $ownerRef], $localinv] != $BaseClass($Heap[this, $ownerFrame])) ==> $Heap[this, $FirstConsistentOwner] == $Heap[$Heap[this, $ownerRef], $FirstConsistentOwner]);
  // parameter of a pure method
  free ensures $AsPureObject(this) == this;



implementation Collections.ArrayList.Boogie.ContractConsistencyCheck.get_Capacity(this: ref) returns ($result: int)
{

  entry:
    goto onGuardUpdateWitness1;

  onGuardUpdateWitness1:
    $result := 0;
    goto onPostReturn, onGuardUpdateWitness2;

  onGuardUpdateWitness2:
    assume 0 > $result;
    $result := 1;
    goto onPostReturn, onGuardUpdateWitness3;

  onGuardUpdateWitness3:
    assume 0 > $result;
    $result := 0;
    goto returnBlock;

  onPostReturn:
    assume 0 <= $result;
    return;

  returnBlock:
    return;
}



// purity axiom (confined)
axiom $PurityAxiomsCanBeAssumed ==> (forall $Heap: [ref,<x>name]x, this: ref :: { #Collections.ArrayList.get_Capacity($Heap, this) } IsHeap($Heap) && $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated] && (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)) ==> 0 <= #Collections.ArrayList.get_Capacity($Heap, this) && ($Heap[this, $ownerFrame] != $PeerGroupPlaceholder ==> ($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame] && $Heap[$Heap[this, $ownerRef], $localinv] != $BaseClass($Heap[this, $ownerFrame]) ==> $Heap[this, $FirstConsistentOwner] == $Heap[this, $ownerRef]) && (!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame] && $Heap[$Heap[this, $ownerRef], $localinv] != $BaseClass($Heap[this, $ownerFrame])) ==> $Heap[this, $FirstConsistentOwner] == $Heap[$Heap[this, $ownerRef], $FirstConsistentOwner])) && $AsPureObject(this) == this);

// expose version axiom for confined methods
axiom (forall $Heap: [ref,<x>name]x, this: ref :: { #Collections.ArrayList.get_Capacity($Heap, this) } this != null && $typeof(this) <: Collections.ArrayList && $Heap[this, $inv] == $typeof(this) && $Heap[this, $localinv] == $typeof(this) && IsHeap($Heap) && $Heap[this, $allocated] ==> #Collections.ArrayList.get_Capacity($Heap, this) == ##Collections.ArrayList.get_Capacity($Heap[this, $exposeVersion]));

procedure Collections.ArrayList.get_Capacity(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], $isBaseCall: bool) returns ($result: int where InRange($result, System.Int32));
  // target object is peer valid (pure method)
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // parameter of a pure method
  free requires $AsPureObject(this) == this;
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // user-declared postconditions
  ensures 0 <= $result;
  // FCO info about pure receiver
  free ensures $Heap[this, $ownerFrame] != $PeerGroupPlaceholder ==> ($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame] && $Heap[$Heap[this, $ownerRef], $localinv] != $BaseClass($Heap[this, $ownerFrame]) ==> $Heap[this, $FirstConsistentOwner] == $Heap[this, $ownerRef]) && (!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame] && $Heap[$Heap[this, $ownerRef], $localinv] != $BaseClass($Heap[this, $ownerFrame])) ==> $Heap[this, $FirstConsistentOwner] == $Heap[$Heap[this, $ownerRef], $FirstConsistentOwner]);
  // parameter of a pure method
  free ensures $AsPureObject(this) == this;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  free ensures $Heap == old($Heap);
  free ensures $isBaseCall || $result == #Collections.ArrayList.get_Capacity($Heap, this);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Collections.ArrayList.get_Capacity(this: ref, $isBaseCall: bool) returns ($result: int)
{
  var stack0o: ref, stack0i: int, return.value: int where InRange(return.value, System.Int32), SS$Display.Return.Local: int where InRange(SS$Display.Return.Local, System.Int32);

  entry:
    goto block9520;

  block9520:
    goto block9639;

  block9639:
    // ----- nop
    // ----- load field  ----- ArrayList.ssc(62,9)
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- unary operator  ----- ArrayList.ssc(62,9)
    assert stack0o != null;
    stack0i := $Length(stack0o);
    // ----- unary operator  ----- ArrayList.ssc(62,9)
    stack0i := $IntToInt(stack0i, System.UIntPtr, System.Int32);
    // ----- copy  ----- ArrayList.ssc(62,9)
    return.value := stack0i;
    // ----- branch
    goto block9741;

  block9741:
    // ----- nop
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0i := return.value;
    // ----- return
    $result := stack0i;
    return;
}



// purity axiom (confined)
axiom $PurityAxiomsCanBeAssumed ==> (forall $Heap: [ref,<x>name]x, this: ref :: { #Collections.ArrayList.get_Count($Heap, this) } IsHeap($Heap) && $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated] && (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)) ==> 0 <= #Collections.ArrayList.get_Count($Heap, this) && #Collections.ArrayList.get_Count($Heap, this) == $Heap[this, Collections.ArrayList._size] && ($Heap[this, $ownerFrame] != $PeerGroupPlaceholder ==> ($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame] && $Heap[$Heap[this, $ownerRef], $localinv] != $BaseClass($Heap[this, $ownerFrame]) ==> $Heap[this, $FirstConsistentOwner] == $Heap[this, $ownerRef]) && (!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame] && $Heap[$Heap[this, $ownerRef], $localinv] != $BaseClass($Heap[this, $ownerFrame])) ==> $Heap[this, $FirstConsistentOwner] == $Heap[$Heap[this, $ownerRef], $FirstConsistentOwner])) && $AsPureObject(this) == this);

// expose version axiom for confined methods
axiom (forall $Heap: [ref,<x>name]x, this: ref :: { #Collections.ArrayList.get_Count($Heap, this) } this != null && $typeof(this) <: Collections.ArrayList && $Heap[this, $inv] == $typeof(this) && $Heap[this, $localinv] == $typeof(this) && IsHeap($Heap) && $Heap[this, $allocated] ==> #Collections.ArrayList.get_Count($Heap, this) == ##Collections.ArrayList.get_Count($Heap[this, $exposeVersion]));

procedure Collections.ArrayList.set_Capacity$System.Int32(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], value$in: int where InRange(value$in, System.Int32));
  // user-declared preconditions
  requires #Collections.ArrayList.get_Count($Heap, this) <= value$in;
  // target object is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // target object is peer consistent (owner must not be valid)
  requires $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // user-declared postconditions
  ensures value$in <= $Length($Heap[this, Collections.ArrayList._items]);
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



implementation Collections.ArrayList.set_Capacity$System.Int32(this: ref, value$in: int)
{
  var value: int where InRange(value, System.Int32), temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception) && $Heap[local2, $allocated], stack0i: int, stack0o: ref, stack0b: bool, stack0s: struct;

  entry:
    value := value$in;
    goto block10642;

  block10642:
    goto block10846;

  block10846:
    // ----- nop
    // ----- FrameGuard processing  ----- ArrayList.ssc(69,17)
    temp0 := this;
    // ----- load token  ----- ArrayList.ssc(69,17)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(69,17)
    stack1o := TypeObject(Collections.ArrayList);
    // ----- local unpack  ----- ArrayList.ssc(69,17)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: Collections.ArrayList && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block10863;

  block10863:
    // ----- copy  ----- ArrayList.ssc(70,11)
    stack0i := value;
    // ----- call  ----- ArrayList.ssc(70,11)
    assert this != null;
    call Collections.ArrayList.EnsureCapacity$System.Int32(this, stack0i);
    // ----- branch
    goto block11033;

  block11033:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true11033to11152, false11033to11118;

  true11033to11152:
    assume local2 == stack0o;
    goto block11152;

  false11033to11118:
    assume local2 != stack0o;
    goto block11118;

  block11152:
    // ----- load token  ----- ArrayList.ssc(71,9)
    havoc stack0s;
    assume $IsTokenForType(stack0s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(71,9)
    stack0o := TypeObject(Collections.ArrayList);
    // ----- local pack  ----- ArrayList.ssc(71,9)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert TypeObject($typeof($Heap[temp0, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert 0 <= $Heap[temp0, Collections.ArrayList._size];
    assert $Heap[temp0, Collections.ArrayList._size] <= $Length($Heap[temp0, Collections.ArrayList._items]);
    assert (forall ^i: int :: $Heap[temp0, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[temp0, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[temp0, Collections.ArrayList._items], $elements], ^i) == null);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Collections.ArrayList ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block11135;

  block11118:
    // ----- is instance
    // ----- branch
    goto true11118to11152, false11118to11169;

  true11118to11152:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block11152;

  false11118to11169:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block11169;

  block11169:
    // ----- branch
    goto block11135;

  block11135:
    // ----- nop
    // ----- branch
    goto block10999;

  block10999:
    // ----- nop
    // ----- return
    return;
}



procedure Collections.ArrayList.EnsureCapacity$System.Int32(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], desiredCapacity$in: int where InRange(desiredCapacity$in, System.Int32));
  // user-declared preconditions
  requires $Heap[this, Collections.ArrayList._size] <= desiredCapacity$in;
  requires $Heap[this, Collections.ArrayList._size] <= $Length($Heap[this, Collections.ArrayList._items]);
  requires ($Heap[$Heap[this, Collections.ArrayList._items], $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[$Heap[this, Collections.ArrayList._items], $ownerRef], $inv] <: $Heap[$Heap[this, Collections.ArrayList._items], $ownerFrame]) || $Heap[$Heap[$Heap[this, Collections.ArrayList._items], $ownerRef], $localinv] == $BaseClass($Heap[$Heap[this, Collections.ArrayList._items], $ownerFrame])) && (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[$Heap[this, Collections.ArrayList._items], $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[$Heap[this, Collections.ArrayList._items], $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires TypeObject($typeof($Heap[this, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
  requires (forall ^i: int :: $Heap[this, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[this, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], ^i) == null);
  // target object is exposed for Collections.ArrayList
  requires !($Heap[this, $inv] <: Collections.ArrayList) || $Heap[this, $localinv] == System.Object;
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // user-declared postconditions
  ensures desiredCapacity$in <= $Length($Heap[this, Collections.ArrayList._items]);
  ensures $Heap[this, Collections.ArrayList._size] == old($Heap[this, Collections.ArrayList._size]);
  ensures TypeObject($typeof($Heap[this, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
  ensures (forall ^i: int :: $Heap[this, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[this, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], ^i) == null);
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



axiom Microsoft.Contracts.ICheckedException <: Microsoft.Contracts.ICheckedException;

axiom Microsoft.Contracts.ICheckedException <: System.Object;

axiom $IsMemberlessType(Microsoft.Contracts.ICheckedException);

axiom $AsInterface(Microsoft.Contracts.ICheckedException) == Microsoft.Contracts.ICheckedException;

procedure Collections.ArrayList.get_Count(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], $isBaseCall: bool) returns ($result: int where InRange($result, System.Int32));
  // target object is peer valid (pure method)
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // parameter of a pure method
  free requires $AsPureObject(this) == this;
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // user-declared postconditions
  ensures 0 <= $result;
  ensures $result == $Heap[this, Collections.ArrayList._size];
  // FCO info about pure receiver
  free ensures $Heap[this, $ownerFrame] != $PeerGroupPlaceholder ==> ($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame] && $Heap[$Heap[this, $ownerRef], $localinv] != $BaseClass($Heap[this, $ownerFrame]) ==> $Heap[this, $FirstConsistentOwner] == $Heap[this, $ownerRef]) && (!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame] && $Heap[$Heap[this, $ownerRef], $localinv] != $BaseClass($Heap[this, $ownerFrame])) ==> $Heap[this, $FirstConsistentOwner] == $Heap[$Heap[this, $ownerRef], $FirstConsistentOwner]);
  // parameter of a pure method
  free ensures $AsPureObject(this) == this;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  free ensures $Heap == old($Heap);
  free ensures $isBaseCall || $result == #Collections.ArrayList.get_Count($Heap, this);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Collections.ArrayList.get_Count(this: ref, $isBaseCall: bool) returns ($result: int)
{
  var return.value: int where InRange(return.value, System.Int32), SS$Display.Return.Local: int where InRange(SS$Display.Return.Local, System.Int32), stack0i: int;

  entry:
    goto block12189;

  block12189:
    goto block12444;

  block12444:
    // ----- nop
    // ----- load field  ----- ArrayList.ssc(81,9)
    assert this != null;
    return.value := $Heap[this, Collections.ArrayList._size];
    // ----- branch
    goto block12223;

  block12223:
    // ----- nop
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0i := return.value;
    // ----- return
    $result := stack0i;
    return;
}



procedure Collections.ArrayList.Boogie.ContractConsistencyCheck.get_Item$System.Int32(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], index$in: int where InRange(index$in, System.Int32)) returns ($result: ref where $Is($result, System.Object) && $Heap[$result, $allocated]);
  // user-declared preconditions
  requires 0 <= index$in;
  requires index$in < #Collections.ArrayList.get_Count($Heap, this);
  // target object is peer valid (pure method)
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // parameter of a pure method
  free requires $AsPureObject(this) == this;
  free requires $BeingConstructed == null;
  modifies $Heap, $ActivityIndicator;
  // user-declared postconditions
  ensures $result == RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], index$in);
  // FCO info about pure receiver
  free ensures $Heap[this, $ownerFrame] != $PeerGroupPlaceholder ==> ($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame] && $Heap[$Heap[this, $ownerRef], $localinv] != $BaseClass($Heap[this, $ownerFrame]) ==> $Heap[this, $FirstConsistentOwner] == $Heap[this, $ownerRef]) && (!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame] && $Heap[$Heap[this, $ownerRef], $localinv] != $BaseClass($Heap[this, $ownerFrame])) ==> $Heap[this, $FirstConsistentOwner] == $Heap[$Heap[this, $ownerRef], $FirstConsistentOwner]);
  // parameter of a pure method
  free ensures $AsPureObject(this) == this;
  // return value is peer valid (pure method)
  ensures $result == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));



implementation Collections.ArrayList.Boogie.ContractConsistencyCheck.get_Item$System.Int32(this: ref, index$in: int) returns ($result: ref)
{

  entry:
    goto onGuardUpdateWitness2;

  onGuardUpdateWitness2:
    assert $Is(RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], index$in), System.Object);
    $result := RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], index$in);
    goto onPostReturn, onGuardUpdateWitness3;

  onGuardUpdateWitness3:
    assume !($result == RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], index$in) && ($result == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc))));
    assert $Is(null, System.Object);
    $result := null;
    goto onPostReturn, onGuardUpdateWitness4;

  onGuardUpdateWitness4:
    assume !($result == RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], index$in) && ($result == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc))));
    assert $Is($stringLiteral2, System.Object);
    $result := $stringLiteral2;
    goto returnBlock;

  onPostReturn:
    assume $result == RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], index$in) && ($result == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)));
    return;

  returnBlock:
    return;
}



// purity axiom (confined)
axiom $PurityAxiomsCanBeAssumed ==> (forall $Heap: [ref,<x>name]x, this: ref, index$in: int :: { #Collections.ArrayList.get_Item$System.Int32($Heap, this, index$in) } IsHeap($Heap) && $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated] && 0 <= index$in && index$in < #Collections.ArrayList.get_Count($Heap, this) && (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)) ==> $Is(#Collections.ArrayList.get_Item$System.Int32($Heap, this, index$in), System.Object) && $Heap[#Collections.ArrayList.get_Item$System.Int32($Heap, this, index$in), $allocated] && #Collections.ArrayList.get_Item$System.Int32($Heap, this, index$in) == RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], index$in) && ($Heap[this, $ownerFrame] != $PeerGroupPlaceholder ==> ($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame] && $Heap[$Heap[this, $ownerRef], $localinv] != $BaseClass($Heap[this, $ownerFrame]) ==> $Heap[this, $FirstConsistentOwner] == $Heap[this, $ownerRef]) && (!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame] && $Heap[$Heap[this, $ownerRef], $localinv] != $BaseClass($Heap[this, $ownerFrame])) ==> $Heap[this, $FirstConsistentOwner] == $Heap[$Heap[this, $ownerRef], $FirstConsistentOwner])) && $AsPureObject(this) == this && (#Collections.ArrayList.get_Item$System.Int32($Heap, this, index$in) == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[#Collections.ArrayList.get_Item$System.Int32($Heap, this, index$in), $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[#Collections.ArrayList.get_Item$System.Int32($Heap, this, index$in), $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc))));

// expose version axiom for confined methods
axiom (forall $Heap: [ref,<x>name]x, this: ref, index$in: int :: { #Collections.ArrayList.get_Item$System.Int32($Heap, this, index$in) } this != null && $typeof(this) <: Collections.ArrayList && $Heap[this, $inv] == $typeof(this) && $Heap[this, $localinv] == $typeof(this) && IsHeap($Heap) && $Heap[this, $allocated] ==> #Collections.ArrayList.get_Item$System.Int32($Heap, this, index$in) == ##Collections.ArrayList.get_Item$System.Int32($Heap[this, $exposeVersion], index$in));

procedure Collections.ArrayList.get_Item$System.Int32(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], index$in: int where InRange(index$in, System.Int32), $isBaseCall: bool) returns ($result: ref where $Is($result, System.Object) && $Heap[$result, $allocated]);
  // user-declared preconditions
  requires 0 <= index$in;
  requires index$in < #Collections.ArrayList.get_Count($Heap, this);
  // target object is peer valid (pure method)
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // parameter of a pure method
  free requires $AsPureObject(this) == this;
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // user-declared postconditions
  ensures $result == RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], index$in);
  // FCO info about pure receiver
  free ensures $Heap[this, $ownerFrame] != $PeerGroupPlaceholder ==> ($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame] && $Heap[$Heap[this, $ownerRef], $localinv] != $BaseClass($Heap[this, $ownerFrame]) ==> $Heap[this, $FirstConsistentOwner] == $Heap[this, $ownerRef]) && (!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame] && $Heap[$Heap[this, $ownerRef], $localinv] != $BaseClass($Heap[this, $ownerFrame])) ==> $Heap[this, $FirstConsistentOwner] == $Heap[$Heap[this, $ownerRef], $FirstConsistentOwner]);
  // parameter of a pure method
  free ensures $AsPureObject(this) == this;
  // return value is peer valid (pure method)
  ensures $result == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  free ensures $isBaseCall || $result == #Collections.ArrayList.get_Item$System.Int32($Heap, this, index$in);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Collections.ArrayList.get_Item$System.Int32(this: ref, index$in: int, $isBaseCall: bool) returns ($result: ref)
{
  var index: int where InRange(index, System.Int32), stack0o: ref, stack1i: int, return.value: ref where $Is(return.value, System.Object) && $Heap[return.value, $allocated], SS$Display.Return.Local: ref where $Is(SS$Display.Return.Local, System.Object) && $Heap[SS$Display.Return.Local, $allocated];

  entry:
    index := index$in;
    goto block13107;

  block13107:
    goto block13311;

  block13311:
    // ----- nop
    // ----- serialized AssumeStatement  ----- ArrayList.ssc(92,9)
    assume RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], index) == null || (($Heap[RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], index), $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], index), $ownerRef], $inv] <: $Heap[RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], index), $ownerFrame]) || $Heap[$Heap[RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], index), $ownerRef], $localinv] == $BaseClass($Heap[RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], index), $ownerFrame])) && (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], index), $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], index), $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)));
    goto block13209;

  block13209:
    // ----- nop
    // ----- load field  ----- ArrayList.ssc(93,9)
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- copy  ----- ArrayList.ssc(93,9)
    stack1i := index;
    // ----- load element  ----- ArrayList.ssc(93,9)
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    return.value := RefArrayGet($Heap[stack0o, $elements], stack1i);
    // ----- branch
    goto block13294;

  block13294:
    // ----- nop
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0o := return.value;
    // ----- return
    $result := stack0o;
    return;
}



procedure Collections.ArrayList.set_Item$System.Int32$System.Object(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], index$in: int where InRange(index$in, System.Int32), value$in: ref where $Is(value$in, System.Object) && $Heap[value$in, $allocated]);
  // user-declared preconditions
  requires 0 <= index$in;
  requires index$in < #Collections.ArrayList.get_Count($Heap, this);
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



implementation Collections.ArrayList.set_Item$System.Int32$System.Object(this: ref, index$in: int, value$in: ref)
{
  var index: int where InRange(index, System.Int32), value: ref where $Is(value, System.Object) && $Heap[value, $allocated], temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception) && $Heap[local2, $allocated], stack0o: ref, stack1i: int, stack0b: bool, stack0s: struct;

  entry:
    index := index$in;
    value := value$in;
    goto block14501;

  block14501:
    goto block14722;

  block14722:
    // ----- nop
    // ----- FrameGuard processing  ----- ArrayList.ssc(98,17)
    temp0 := this;
    // ----- load token  ----- ArrayList.ssc(98,17)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(98,17)
    stack1o := TypeObject(Collections.ArrayList);
    // ----- local unpack  ----- ArrayList.ssc(98,17)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: Collections.ArrayList && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block14739;

  block14739:
    // ----- load field  ----- ArrayList.ssc(99,11)
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- copy  ----- ArrayList.ssc(99,11)
    stack1i := index;
    // ----- store element  ----- ArrayList.ssc(99,11)
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    assert value == null || $typeof(value) <: $ElementType($typeof(stack0o));
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]);
    $Heap[stack0o, $elements] := RefArraySet($Heap[stack0o, $elements], stack1i, value);
    assume IsHeap($Heap);
    // ----- branch
    goto block14892;

  block14892:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true14892to14824, false14892to14841;

  true14892to14824:
    assume local2 == stack0o;
    goto block14824;

  false14892to14841:
    assume local2 != stack0o;
    goto block14841;

  block14824:
    // ----- load token  ----- ArrayList.ssc(100,9)
    havoc stack0s;
    assume $IsTokenForType(stack0s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(100,9)
    stack0o := TypeObject(Collections.ArrayList);
    // ----- local pack  ----- ArrayList.ssc(100,9)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert TypeObject($typeof($Heap[temp0, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert 0 <= $Heap[temp0, Collections.ArrayList._size];
    assert $Heap[temp0, Collections.ArrayList._size] <= $Length($Heap[temp0, Collections.ArrayList._items]);
    assert (forall ^i: int :: $Heap[temp0, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[temp0, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[temp0, Collections.ArrayList._items], $elements], ^i) == null);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Collections.ArrayList ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block14926;

  block14841:
    // ----- is instance
    // ----- branch
    goto true14841to14824, false14841to14875;

  true14841to14824:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block14824;

  false14841to14875:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block14875;

  block14875:
    // ----- branch
    goto block14926;

  block14926:
    // ----- nop
    // ----- branch
    goto block14790;

  block14790:
    // ----- return
    return;
}



procedure Collections.ArrayList.Add$System.Object(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], value$in: ref where $Is(value$in, System.Object) && $Heap[value$in, $allocated]) returns ($result: int where InRange($result, System.Int32));
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
  // user-declared postconditions
  ensures #Collections.ArrayList.get_Count($Heap, this) == old(#Collections.ArrayList.get_Count($Heap, this)) + 1;
  ensures #Collections.ArrayList.get_Item$System.Int32($Heap, this, $result) == value$in;
  ensures $result == old(#Collections.ArrayList.get_Count($Heap, this));
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



implementation Collections.ArrayList.Add$System.Object(this: ref, value$in: ref) returns ($result: int)
{
  var value: ref where $Is(value, System.Object) && $Heap[value, $allocated], temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local4: ref where $Is(local4, System.Exception) && $Heap[local4, $allocated], stack0i: int, stack1i: int, stack0b: bool, stack0o: ref, local5: int where InRange(local5, System.Int32), temp2: exposeVersionType, return.value: int where InRange(return.value, System.Int32), stack0s: struct, SS$Display.Return.Local: int where InRange(SS$Display.Return.Local, System.Int32);

  entry:
    value := value$in;
    goto block16116;

  block16116:
    goto block16269;

  block16269:
    // ----- nop
    // ----- FrameGuard processing  ----- ArrayList.ssc(110,15)
    temp0 := this;
    // ----- load token  ----- ArrayList.ssc(110,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(110,15)
    stack1o := TypeObject(Collections.ArrayList);
    // ----- local unpack  ----- ArrayList.ssc(110,15)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: Collections.ArrayList && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local4 := null;
    goto block16286;

  block16286:
    // ----- load field  ----- ArrayList.ssc(111,9)
    assert this != null;
    stack0i := $Heap[this, Collections.ArrayList._size];
    // ----- load field  ----- ArrayList.ssc(111,9)
    assert this != null;
    stack1o := $Heap[this, Collections.ArrayList._items];
    // ----- unary operator  ----- ArrayList.ssc(111,9)
    assert stack1o != null;
    stack1i := $Length(stack1o);
    // ----- unary operator  ----- ArrayList.ssc(111,9)
    stack1i := $IntToInt(stack1i, System.UIntPtr, System.Int32);
    // ----- binary operator  ----- ArrayList.ssc(111,9)
    // ----- branch  ----- ArrayList.ssc(111,9)
    goto true16286to16320, false16286to16303;

  true16286to16320:
    assume stack0i != stack1i;
    goto block16320;

  false16286to16303:
    assume stack0i == stack1i;
    goto block16303;

  block16320:
    // ----- load field  ----- ArrayList.ssc(112,9)
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- load field  ----- ArrayList.ssc(112,9)
    assert this != null;
    stack1i := $Heap[this, Collections.ArrayList._size];
    // ----- store element  ----- ArrayList.ssc(112,9)
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    assert value == null || $typeof(value) <: $ElementType($typeof(stack0o));
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]);
    $Heap[stack0o, $elements] := RefArraySet($Heap[stack0o, $elements], stack1i, value);
    assume IsHeap($Heap);
    // ----- load field  ----- ArrayList.ssc(113,16)
    assert this != null;
    local5 := $Heap[this, Collections.ArrayList._size];
    // ----- load constant 1  ----- ArrayList.ssc(113,16)
    stack0i := 1;
    // ----- binary operator  ----- ArrayList.ssc(113,16)
    stack0i := local5 + stack0i;
    // ----- store field  ----- ArrayList.ssc(113,16)
    assert this != null;
    assert $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
    havoc temp2;
    $Heap[this, $exposeVersion] := temp2;
    $Heap[this, Collections.ArrayList._size] := stack0i;
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || TypeObject($typeof($Heap[this, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || 0 <= $Heap[this, Collections.ArrayList._size];
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || $Heap[this, Collections.ArrayList._size] <= $Length($Heap[this, Collections.ArrayList._items]);
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || (forall ^i: int :: $Heap[this, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[this, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], ^i) == null);
    assume IsHeap($Heap);
    // ----- copy
    return.value := local5;
    // ----- branch
    goto block16711;

  block16303:
    // ----- load field  ----- ArrayList.ssc(111,37)
    assert this != null;
    stack0i := $Heap[this, Collections.ArrayList._size];
    // ----- load constant 1  ----- ArrayList.ssc(111,37)
    stack1i := 1;
    // ----- binary operator  ----- ArrayList.ssc(111,37)
    stack0i := stack0i + stack1i;
    // ----- call  ----- ArrayList.ssc(111,37)
    assert this != null;
    call Collections.ArrayList.EnsureCapacity$System.Int32(this, stack0i);
    goto block16320;

  block16711:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true16711to16626, false16711to16694;

  true16711to16626:
    assume local4 == stack0o;
    goto block16626;

  false16711to16694:
    assume local4 != stack0o;
    goto block16694;

  block16626:
    // ----- load token  ----- ArrayList.ssc(114,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(114,7)
    stack0o := TypeObject(Collections.ArrayList);
    // ----- local pack  ----- ArrayList.ssc(114,7)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert TypeObject($typeof($Heap[temp0, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert 0 <= $Heap[temp0, Collections.ArrayList._size];
    assert $Heap[temp0, Collections.ArrayList._size] <= $Length($Heap[temp0, Collections.ArrayList._items]);
    assert (forall ^i: int :: $Heap[temp0, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[temp0, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[temp0, Collections.ArrayList._items], $elements], ^i) == null);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Collections.ArrayList ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block16643;

  block16694:
    // ----- is instance
    // ----- branch
    goto true16694to16626, false16694to16660;

  true16694to16626:
    assume $As(local4, Microsoft.Contracts.ICheckedException) != null;
    goto block16626;

  false16694to16660:
    assume $As(local4, Microsoft.Contracts.ICheckedException) == null;
    goto block16660;

  block16660:
    // ----- branch
    goto block16643;

  block16643:
    // ----- nop
    // ----- branch
    goto block16575;

  block16575:
    // ----- nop
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0i := return.value;
    // ----- return
    $result := stack0i;
    return;
}



implementation Collections.ArrayList.EnsureCapacity$System.Int32(this: ref, desiredCapacity$in: int)
{
  var desiredCapacity: int where InRange(desiredCapacity, System.Int32), stack0o: ref, stack0i: int, stack0b: bool, local4: int where InRange(local4, System.Int32), stack1i: int, stack1o: ref, newItems: ref where $Is(newItems, RefArray(System.Object, 1)) && $Heap[newItems, $allocated], temp0: ref, temp1: exposeVersionType, stack2o: ref, stack3i: int, stack4i: int;

  entry:
    desiredCapacity := desiredCapacity$in;
    goto block19006;

  block19006:
    goto block20145;

  block20145:
    // ----- nop
    // ----- load field  ----- ArrayList.ssc(129,7)
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- unary operator  ----- ArrayList.ssc(129,7)
    assert stack0o != null;
    stack0i := $Length(stack0o);
    // ----- unary operator  ----- ArrayList.ssc(129,7)
    stack0i := $IntToInt(stack0i, System.UIntPtr, System.Int32);
    // ----- binary operator  ----- ArrayList.ssc(129,7)
    // ----- branch  ----- ArrayList.ssc(129,7)
    goto true20145to19652, false20145to19703;

  true20145to19652:
    assume stack0i >= desiredCapacity;
    goto block19652;

  false20145to19703:
    assume stack0i < desiredCapacity;
    goto block19703;

  block19652:
    goto block19210;

  block19703:
    // ----- load constant -2147483648  ----- ArrayList.ssc(131,9)
    local4 := int#m2147483648;
    // ----- load constant 16
    stack0i := 16;
    // ----- binary operator
    // ----- branch
    goto true19703to20400, false19703to19567;

  true19703to20400:
    assume local4 >= stack0i;
    goto block20400;

  false19703to19567:
    assume local4 < stack0i;
    goto block19567;

  block20400:
    // ----- copy
    stack0i := local4;
    goto block19788;

  block19567:
    // ----- load constant 16
    stack0i := 16;
    // ----- branch
    goto block19788;

  block19210:
    // ----- nop
    // ----- return
    return;

  block19788:
    // ----- copy
    local4 := stack0i;
    // ----- load field
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- unary operator
    assert stack0o != null;
    stack0i := $Length(stack0o);
    // ----- unary operator
    stack0i := $IntToInt(stack0i, System.UIntPtr, System.Int32);
    // ----- load constant 2
    stack1i := 2;
    // ----- binary operator
    stack0i := stack0i * stack1i;
    // ----- binary operator
    // ----- branch
    goto true19788to20162, false19788to20111;

  true19788to20162:
    assume local4 >= stack0i;
    goto block20162;

  false19788to20111:
    assume local4 < stack0i;
    goto block20111;

  block20162:
    // ----- copy
    stack0i := local4;
    goto block20179;

  block20111:
    // ----- load field
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- unary operator
    assert stack0o != null;
    stack0i := $Length(stack0o);
    // ----- unary operator
    stack0i := $IntToInt(stack0i, System.UIntPtr, System.Int32);
    // ----- load constant 2
    stack1i := 2;
    // ----- binary operator
    stack0i := stack0i * stack1i;
    // ----- branch
    goto block20179;

  block20179:
    // ----- copy
    local4 := stack0i;
    // ----- binary operator
    // ----- branch
    goto true20179to19958, false20179to19380;

  true20179to19958:
    assume local4 >= desiredCapacity;
    goto block19958;

  false20179to19380:
    assume local4 < desiredCapacity;
    goto block19380;

  block19958:
    // ----- copy
    stack0i := local4;
    goto block19669;

  block19380:
    // ----- copy
    stack0i := desiredCapacity;
    // ----- branch
    goto block19669;

  block19669:
    // ----- copy
    local4 := stack0i;
    // ----- copy  ----- ArrayList.ssc(131,9)
    desiredCapacity := local4;
    // ----- serialized AssertStatement  ----- ArrayList.ssc(132,9)
    assert desiredCapacity != $Length($Heap[this, Collections.ArrayList._items]);
    goto block19159;

  block19159:
    // ----- nop
    // ----- serialized AssertStatement  ----- ArrayList.ssc(133,9)
    assert desiredCapacity > 0;
    goto block19346;

  block19346:
    // ----- nop
    // ----- copy  ----- ArrayList.ssc(135,18)
    stack0i := desiredCapacity;
    // ----- new array  ----- ArrayList.ssc(135,18)
    assert 0 <= stack0i;
    havoc temp0;
    assume $Heap[temp0, $allocated] == false && $Length(temp0) == stack0i;
    assume $Heap[$ElementProxy(temp0, -1), $allocated] == false && $ElementProxy(temp0, -1) != temp0 && $ElementProxy(temp0, -1) != null;
    assume temp0 != null;
    assume $typeof(temp0) == RefArray(System.Object, 1);
    assume $Heap[temp0, $ownerRef] == temp0 && $Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder;
    assume $Heap[$ElementProxy(temp0, -1), $ownerRef] == $ElementProxy(temp0, -1) && $Heap[$ElementProxy(temp0, -1), $ownerFrame] == $PeerGroupPlaceholder;
    assume $Heap[temp0, $inv] == $typeof(temp0) && $Heap[temp0, $localinv] == $typeof(temp0);
    assume (forall $i: int :: RefArrayGet($Heap[temp0, $elements], $i) == null);
    $Heap[temp0, $allocated] := true;
    call System.Object..ctor($ElementProxy(temp0, -1));
    newItems := temp0;
    assume IsHeap($Heap);
    // ----- load field  ----- ArrayList.ssc(136,9)
    assert this != null;
    stack0i := $Heap[this, Collections.ArrayList._size];
    // ----- load constant 0  ----- ArrayList.ssc(136,9)
    stack1i := 0;
    // ----- binary operator  ----- ArrayList.ssc(136,9)
    // ----- branch  ----- ArrayList.ssc(136,9)
    goto true19346to20247, false19346to19244;

  true19346to20247:
    assume stack0i <= stack1i;
    goto block20247;

  false19346to19244:
    assume stack0i > stack1i;
    goto block19244;

  block20247:
    // ----- store field  ----- ArrayList.ssc(137,9)
    assert this != null;
    assert $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
    assert ($Heap[newItems, $ownerRef] == this && $Heap[newItems, $ownerFrame] == Collections.ArrayList) || $Heap[newItems, $ownerFrame] == $PeerGroupPlaceholder;
    assert $Heap[newItems, $ownerFrame] == $PeerGroupPlaceholder && $Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList) ==> (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[newItems, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[newItems, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
    assert $Heap[newItems, $ownerFrame] == $PeerGroupPlaceholder && $Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList) ==> $Heap[this, $ownerRef] != $Heap[newItems, $ownerRef] || $Heap[this, $ownerFrame] != $Heap[newItems, $ownerFrame];
    call $UpdateOwnersForRep(this, Collections.ArrayList, newItems);
    havoc temp1;
    $Heap[this, $exposeVersion] := temp1;
    $Heap[this, Collections.ArrayList._items] := newItems;
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || TypeObject($typeof($Heap[this, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || 0 <= $Heap[this, Collections.ArrayList._size];
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || $Heap[this, Collections.ArrayList._size] <= $Length($Heap[this, Collections.ArrayList._items]);
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || (forall ^i: int :: $Heap[this, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[this, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], ^i) == null);
    assume IsHeap($Heap);
    goto block19210;

  block19244:
    // ----- load field  ----- ArrayList.ssc(136,24)
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- load constant 0  ----- ArrayList.ssc(136,24)
    stack1i := 0;
    // ----- copy  ----- ArrayList.ssc(136,24)
    stack2o := newItems;
    // ----- load constant 0  ----- ArrayList.ssc(136,24)
    stack3i := 0;
    // ----- load field  ----- ArrayList.ssc(136,24)
    assert this != null;
    stack4i := $Heap[this, Collections.ArrayList._size];
    // ----- call  ----- ArrayList.ssc(136,24)
    call System.Array.Copy$System.Array$notnull$System.Int32$System.Array$notnull$System.Int32$System.Int32(stack0o, stack1i, stack2o, stack3i, stack4i);
    goto block20247;
}



procedure System.Array.Copy$System.Array$notnull$System.Int32$System.Array$notnull$System.Int32$System.Int32(sourceArray$in: ref where $IsNotNull(sourceArray$in, System.Array) && $Heap[sourceArray$in, $allocated], sourceIndex$in: int where InRange(sourceIndex$in, System.Int32), destinationArray$in: ref where $IsNotNull(destinationArray$in, System.Array) && $Heap[destinationArray$in, $allocated], destinationIndex$in: int where InRange(destinationIndex$in, System.Int32), length$in: int where InRange(length$in, System.Int32));
  // user-declared preconditions
  requires sourceArray$in != null;
  requires destinationArray$in != null;
  requires $Rank(sourceArray$in) == $Rank(destinationArray$in);
  requires sourceIndex$in >= $LBound(sourceArray$in, 0);
  requires destinationIndex$in >= $LBound(destinationArray$in, 0);
  requires length$in >= 0;
  requires sourceIndex$in + length$in <= $LBound(sourceArray$in, 0) + $Length(sourceArray$in);
  requires destinationIndex$in + length$in <= $LBound(destinationArray$in, 0) + $Length(destinationArray$in);
  // sourceArray is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[sourceArray$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[sourceArray$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // sourceArray is peer consistent (owner must not be valid)
  requires $Heap[sourceArray$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[sourceArray$in, $ownerRef], $inv] <: $Heap[sourceArray$in, $ownerFrame]) || $Heap[$Heap[sourceArray$in, $ownerRef], $localinv] == $BaseClass($Heap[sourceArray$in, $ownerFrame]);
  // destinationArray is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[destinationArray$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[destinationArray$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // destinationArray is peer consistent (owner must not be valid)
  requires $Heap[destinationArray$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[destinationArray$in, $ownerRef], $inv] <: $Heap[destinationArray$in, $ownerFrame]) || $Heap[$Heap[destinationArray$in, $ownerRef], $localinv] == $BaseClass($Heap[destinationArray$in, $ownerFrame]);
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // hard-coded postcondition
  ensures (forall $k: int :: { ValueArrayGet($Heap[destinationArray$in, $elements], $k) } (destinationIndex$in <= $k && $k < destinationIndex$in + length$in ==> old(ValueArrayGet($Heap[sourceArray$in, $elements], $k + sourceIndex$in - destinationIndex$in)) == ValueArrayGet($Heap[destinationArray$in, $elements], $k)) && (!(destinationIndex$in <= $k && $k < destinationIndex$in + length$in) ==> old(ValueArrayGet($Heap[destinationArray$in, $elements], $k)) == ValueArrayGet($Heap[destinationArray$in, $elements], $k)));
  ensures (forall $k: int :: { IntArrayGet($Heap[destinationArray$in, $elements], $k) } (destinationIndex$in <= $k && $k < destinationIndex$in + length$in ==> old(IntArrayGet($Heap[sourceArray$in, $elements], $k + sourceIndex$in - destinationIndex$in)) == IntArrayGet($Heap[destinationArray$in, $elements], $k)) && (!(destinationIndex$in <= $k && $k < destinationIndex$in + length$in) ==> old(IntArrayGet($Heap[destinationArray$in, $elements], $k)) == IntArrayGet($Heap[destinationArray$in, $elements], $k)));
  ensures (forall $k: int :: { RefArrayGet($Heap[destinationArray$in, $elements], $k) } (destinationIndex$in <= $k && $k < destinationIndex$in + length$in ==> old(RefArrayGet($Heap[sourceArray$in, $elements], $k + sourceIndex$in - destinationIndex$in)) == RefArrayGet($Heap[destinationArray$in, $elements], $k)) && (!(destinationIndex$in <= $k && $k < destinationIndex$in + length$in) ==> old(RefArrayGet($Heap[destinationArray$in, $elements], $k)) == RefArrayGet($Heap[destinationArray$in, $elements], $k)));
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != destinationArray$in || !($typeof(destinationArray$in) <: DeclType($f)) || !$IncludedInModifiesStar($f)) && old($o != destinationArray$in || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



procedure Collections.ArrayList.AddRange$System.Collections.ICollection$notnull(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], c$in: ref where $IsNotNull(c$in, System.Collections.ICollection) && $Heap[c$in, $allocated]);
  // user-declared preconditions
  requires !($Heap[this, $ownerRef] == $Heap[c$in, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[c$in, $ownerFrame]);
  // target object is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // target object is peer consistent (owner must not be valid)
  requires $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
  // c is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[c$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[c$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // c is peer consistent (owner must not be valid)
  requires $Heap[c$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[c$in, $ownerRef], $inv] <: $Heap[c$in, $ownerFrame]) || $Heap[$Heap[c$in, $ownerRef], $localinv] == $BaseClass($Heap[c$in, $ownerFrame]);
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(($o != c$in || !($typeof(c$in) <: DeclType($f)) || !$IncludedInModifiesStar($f)) && ($o != this || !($typeof(this) <: DeclType($f)) || !$IncludedInModifiesStar($f))) && old($o != c$in || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Collections.ArrayList.AddRange$System.Collections.ICollection$notnull(this: ref, c$in: ref)
{
  var c: ref where $IsNotNull(c, System.Collections.ICollection) && $Heap[c, $allocated], stack0i: int, stack1o: ref;

  entry:
    c := c$in;
    goto block21845;

  block21845:
    goto block21879;

  block21879:
    // ----- nop
    // ----- load field  ----- ArrayList.ssc(146,7)
    assert this != null;
    stack0i := $Heap[this, Collections.ArrayList._size];
    // ----- copy  ----- ArrayList.ssc(146,7)
    stack1o := c;
    // ----- call  ----- ArrayList.ssc(146,7)
    assert this != null;
    call Collections.ArrayList.InsertRange$System.Int32$System.Collections.ICollection$notnull$.Virtual.$(this, stack0i, stack1o);
    // ----- return
    return;
}



procedure Collections.ArrayList.InsertRange$System.Int32$System.Collections.ICollection$notnull$.Virtual.$(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], index$in: int where InRange(index$in, System.Int32), c$in: ref where $IsNotNull(c$in, System.Collections.ICollection) && $Heap[c$in, $allocated]);
  // user-declared preconditions
  requires 0 <= index$in;
  requires index$in <= #Collections.ArrayList.get_Count($Heap, this);
  requires !($Heap[this, $ownerRef] == $Heap[c$in, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[c$in, $ownerFrame]);
  // target object is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // target object is peer consistent (owner must not be valid)
  requires $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
  // c is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[c$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[c$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // c is peer consistent (owner must not be valid)
  requires $Heap[c$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[c$in, $ownerRef], $inv] <: $Heap[c$in, $ownerFrame]) || $Heap[$Heap[c$in, $ownerRef], $localinv] == $BaseClass($Heap[c$in, $ownerFrame]);
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(($o != c$in || !($typeof(c$in) <: DeclType($f)) || !$IncludedInModifiesStar($f)) && ($o != this || !($typeof(this) <: DeclType($f)) || !$IncludedInModifiesStar($f))) && old($o != c$in || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



axiom System.Collections.IComparer <: System.Collections.IComparer;

axiom System.Collections.IComparer <: System.Object;

axiom $IsMemberlessType(System.Collections.IComparer);

axiom $AsInterface(System.Collections.IComparer) == System.Collections.IComparer;

procedure Collections.ArrayList.BinarySearch$System.Int32$System.Int32$System.Object$System.Collections.IComparer(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], index$in: int where InRange(index$in, System.Int32), count$in: int where InRange(count$in, System.Int32), value$in: ref where $Is(value$in, System.Object) && $Heap[value$in, $allocated], comparer$in: ref where $Is(comparer$in, System.Collections.IComparer) && $Heap[comparer$in, $allocated]) returns ($result: int where InRange($result, System.Int32));
  // user-declared preconditions
  requires 0 <= index$in;
  requires 0 <= count$in;
  requires index$in + count$in <= #Collections.ArrayList.get_Count($Heap, this);
  requires comparer$in == null || !($Heap[this, $ownerRef] == $Heap[comparer$in, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[comparer$in, $ownerFrame]);
  requires value$in == null || !($Heap[this, $ownerRef] == $Heap[value$in, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[value$in, $ownerFrame]);
  // target object is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // target object is peer consistent (owner must not be valid)
  requires $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
  // value is peer consistent
  requires value$in == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[value$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[value$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // value is peer consistent (owner must not be valid)
  requires value$in == null || $Heap[value$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[value$in, $ownerRef], $inv] <: $Heap[value$in, $ownerFrame]) || $Heap[$Heap[value$in, $ownerRef], $localinv] == $BaseClass($Heap[value$in, $ownerFrame]);
  // comparer is peer consistent
  requires comparer$in == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[comparer$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[comparer$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // comparer is peer consistent (owner must not be valid)
  requires comparer$in == null || $Heap[comparer$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[comparer$in, $ownerRef], $inv] <: $Heap[comparer$in, $ownerFrame]) || $Heap[$Heap[comparer$in, $ownerRef], $localinv] == $BaseClass($Heap[comparer$in, $ownerFrame]);
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // user-declared postconditions
  ensures $result < #Collections.ArrayList.get_Count($Heap, this);
  ensures 0 <= $result ==> #Collections.ArrayList.get_Item$System.Int32($Heap, this, $result) == value$in;
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



implementation Collections.ArrayList.BinarySearch$System.Int32$System.Int32$System.Object$System.Collections.IComparer(this: ref, index$in: int, count$in: int, value$in: ref, comparer$in: ref) returns ($result: int)
{
  var index: int where InRange(index, System.Int32), count: int where InRange(count, System.Int32), value: ref where $Is(value, System.Object) && $Heap[value, $allocated], comparer: ref where $Is(comparer, System.Collections.IComparer) && $Heap[comparer, $allocated], temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception) && $Heap[local2, $allocated], stack0o: ref, stack1i: int, stack2i: int, stack3o: ref, stack4o: ref, n: int where InRange(n, System.Int32), return.value: int where InRange(return.value, System.Int32), stack0b: bool, stack0s: struct, SS$Display.Return.Local: int where InRange(SS$Display.Return.Local, System.Int32), stack0i: int;

  entry:
    index := index$in;
    count := count$in;
    value := value$in;
    comparer := comparer$in;
    goto block23392;

  block23392:
    goto block23868;

  block23868:
    // ----- nop
    // ----- FrameGuard processing  ----- ArrayList.ssc(160,15)
    temp0 := this;
    // ----- load token  ----- ArrayList.ssc(160,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(160,15)
    stack1o := TypeObject(Collections.ArrayList);
    // ----- local unpack  ----- ArrayList.ssc(160,15)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: Collections.ArrayList && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block23885;

  block23885:
    // ----- load field  ----- ArrayList.ssc(161,13)
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- copy  ----- ArrayList.ssc(161,13)
    stack1i := index;
    // ----- copy  ----- ArrayList.ssc(161,13)
    stack2i := count;
    // ----- copy  ----- ArrayList.ssc(161,13)
    stack3o := value;
    // ----- copy  ----- ArrayList.ssc(161,13)
    stack4o := comparer;
    // ----- call  ----- ArrayList.ssc(161,13)
    call n := System.Array.BinarySearch$System.Array$notnull$System.Int32$System.Int32$System.Object$System.Collections.IComparer(stack0o, stack1i, stack2i, stack3o, stack4o);
    // ----- serialized AssumeStatement  ----- ArrayList.ssc(162,9)
    assume index <= n && n < index + count ==> RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], n) == value;
    goto block24089;

  block24089:
    // ----- nop
    // ----- copy  ----- ArrayList.ssc(163,9)
    return.value := n;
    // ----- branch
    goto block24514;

  block24514:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true24514to24497, false24514to24548;

  true24514to24497:
    assume local2 == stack0o;
    goto block24497;

  false24514to24548:
    assume local2 != stack0o;
    goto block24548;

  block24497:
    // ----- load token  ----- ArrayList.ssc(164,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(164,7)
    stack0o := TypeObject(Collections.ArrayList);
    // ----- local pack  ----- ArrayList.ssc(164,7)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert TypeObject($typeof($Heap[temp0, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert 0 <= $Heap[temp0, Collections.ArrayList._size];
    assert $Heap[temp0, Collections.ArrayList._size] <= $Length($Heap[temp0, Collections.ArrayList._items]);
    assert (forall ^i: int :: $Heap[temp0, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[temp0, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[temp0, Collections.ArrayList._items], $elements], ^i) == null);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Collections.ArrayList ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block24463;

  block24548:
    // ----- is instance
    // ----- branch
    goto true24548to24497, false24548to24446;

  true24548to24497:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block24497;

  false24548to24446:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block24446;

  block24446:
    // ----- branch
    goto block24463;

  block24463:
    // ----- nop
    // ----- branch
    goto block24395;

  block24395:
    // ----- nop
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0i := return.value;
    // ----- return
    $result := stack0i;
    return;
}



procedure System.Array.BinarySearch$System.Array$notnull$System.Int32$System.Int32$System.Object$System.Collections.IComparer(array$in: ref where $IsNotNull(array$in, System.Array) && $Heap[array$in, $allocated], index$in: int where InRange(index$in, System.Int32), length$in: int where InRange(length$in, System.Int32), value$in: ref where $Is(value$in, System.Object) && $Heap[value$in, $allocated], comparer$in: ref where $Is(comparer$in, System.Collections.IComparer) && $Heap[comparer$in, $allocated]) returns ($result: int where InRange($result, System.Int32));
  // user-declared preconditions
  requires array$in != null;
  requires $Rank(array$in) == 1;
  requires index$in >= $LBound(array$in, 0);
  requires length$in >= 0;
  requires length$in <= $Length(array$in) - index$in;
  // array is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[array$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[array$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // array is peer consistent (owner must not be valid)
  requires $Heap[array$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[array$in, $ownerRef], $inv] <: $Heap[array$in, $ownerFrame]) || $Heap[$Heap[array$in, $ownerRef], $localinv] == $BaseClass($Heap[array$in, $ownerFrame]);
  // value is peer consistent
  requires value$in == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[value$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[value$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // value is peer consistent (owner must not be valid)
  requires value$in == null || $Heap[value$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[value$in, $ownerRef], $inv] <: $Heap[value$in, $ownerFrame]) || $Heap[$Heap[value$in, $ownerRef], $localinv] == $BaseClass($Heap[value$in, $ownerFrame]);
  // comparer is peer consistent
  requires comparer$in == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[comparer$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[comparer$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // comparer is peer consistent (owner must not be valid)
  requires comparer$in == null || $Heap[comparer$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[comparer$in, $ownerRef], $inv] <: $Heap[comparer$in, $ownerFrame]) || $Heap[$Heap[comparer$in, $ownerRef], $localinv] == $BaseClass($Heap[comparer$in, $ownerFrame]);
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // user-declared postconditions
  ensures $result == $LBound(array$in, 0) - 1 || (index$in <= $result && $result < index$in + length$in);
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



procedure Collections.ArrayList.BinarySearch$System.Object(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], value$in: ref where $Is(value$in, System.Object) && $Heap[value$in, $allocated]) returns ($result: int where InRange($result, System.Int32));
  // user-declared preconditions
  requires value$in == null || !($Heap[this, $ownerRef] == $Heap[value$in, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[value$in, $ownerFrame]);
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
  // user-declared postconditions
  ensures $result < #Collections.ArrayList.get_Count($Heap, this);
  ensures 0 <= $result && $result < #Collections.ArrayList.get_Count($Heap, this) ==> #Collections.ArrayList.get_Item$System.Int32($Heap, this, $result) == value$in;
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



implementation Collections.ArrayList.BinarySearch$System.Object(this: ref, value$in: ref) returns ($result: int)
{
  var value: ref where $Is(value, System.Object) && $Heap[value, $allocated], stack0i: int, stack1i: int, stack2o: ref, stack3o: ref, return.value: int where InRange(return.value, System.Int32), SS$Display.Return.Local: int where InRange(SS$Display.Return.Local, System.Int32);

  entry:
    value := value$in;
    goto block25925;

  block25925:
    goto block26350;

  block26350:
    // ----- nop
    // ----- load constant 0  ----- ArrayList.ssc(173,7)
    stack0i := 0;
    // ----- call  ----- ArrayList.ssc(173,7)
    assert this != null;
    call stack1i := Collections.ArrayList.get_Count$.Virtual.$(this, false);
    // ----- copy  ----- ArrayList.ssc(173,7)
    stack2o := value;
    stack3o := null;
    // ----- call  ----- ArrayList.ssc(173,7)
    assert this != null;
    call return.value := Collections.ArrayList.BinarySearch$System.Int32$System.Int32$System.Object$System.Collections.IComparer$.Virtual.$(this, stack0i, stack1i, stack2o, stack3o);
    // ----- branch
    goto block25993;

  block25993:
    // ----- nop
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0i := return.value;
    // ----- return
    $result := stack0i;
    return;
}



procedure Collections.ArrayList.get_Count$.Virtual.$(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], $isBaseCall: bool) returns ($result: int where InRange($result, System.Int32));
  // target object is peer valid (pure method)
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // parameter of a pure method
  free requires $AsPureObject(this) == this;
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // user-declared postconditions
  ensures 0 <= $result;
  ensures $result == $Heap[this, Collections.ArrayList._size];
  // FCO info about pure receiver
  free ensures $Heap[this, $ownerFrame] != $PeerGroupPlaceholder ==> ($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame] && $Heap[$Heap[this, $ownerRef], $localinv] != $BaseClass($Heap[this, $ownerFrame]) ==> $Heap[this, $FirstConsistentOwner] == $Heap[this, $ownerRef]) && (!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame] && $Heap[$Heap[this, $ownerRef], $localinv] != $BaseClass($Heap[this, $ownerFrame])) ==> $Heap[this, $FirstConsistentOwner] == $Heap[$Heap[this, $ownerRef], $FirstConsistentOwner]);
  // parameter of a pure method
  free ensures $AsPureObject(this) == this;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  free ensures $Heap == old($Heap);
  free ensures $isBaseCall || $result == #Collections.ArrayList.get_Count($Heap, this);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



procedure Collections.ArrayList.BinarySearch$System.Int32$System.Int32$System.Object$System.Collections.IComparer$.Virtual.$(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], index$in: int where InRange(index$in, System.Int32), count$in: int where InRange(count$in, System.Int32), value$in: ref where $Is(value$in, System.Object) && $Heap[value$in, $allocated], comparer$in: ref where $Is(comparer$in, System.Collections.IComparer) && $Heap[comparer$in, $allocated]) returns ($result: int where InRange($result, System.Int32));
  // user-declared preconditions
  requires 0 <= index$in;
  requires 0 <= count$in;
  requires index$in + count$in <= #Collections.ArrayList.get_Count($Heap, this);
  requires comparer$in == null || !($Heap[this, $ownerRef] == $Heap[comparer$in, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[comparer$in, $ownerFrame]);
  requires value$in == null || !($Heap[this, $ownerRef] == $Heap[value$in, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[value$in, $ownerFrame]);
  // target object is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // target object is peer consistent (owner must not be valid)
  requires $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
  // value is peer consistent
  requires value$in == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[value$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[value$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // value is peer consistent (owner must not be valid)
  requires value$in == null || $Heap[value$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[value$in, $ownerRef], $inv] <: $Heap[value$in, $ownerFrame]) || $Heap[$Heap[value$in, $ownerRef], $localinv] == $BaseClass($Heap[value$in, $ownerFrame]);
  // comparer is peer consistent
  requires comparer$in == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[comparer$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[comparer$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // comparer is peer consistent (owner must not be valid)
  requires comparer$in == null || $Heap[comparer$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[comparer$in, $ownerRef], $inv] <: $Heap[comparer$in, $ownerFrame]) || $Heap[$Heap[comparer$in, $ownerRef], $localinv] == $BaseClass($Heap[comparer$in, $ownerFrame]);
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // user-declared postconditions
  ensures $result < #Collections.ArrayList.get_Count($Heap, this);
  ensures 0 <= $result ==> #Collections.ArrayList.get_Item$System.Int32($Heap, this, $result) == value$in;
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



procedure Collections.ArrayList.BinarySearch$System.Object$System.Collections.IComparer(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], value$in: ref where $Is(value$in, System.Object) && $Heap[value$in, $allocated], comparer$in: ref where $Is(comparer$in, System.Collections.IComparer) && $Heap[comparer$in, $allocated]) returns ($result: int where InRange($result, System.Int32));
  // user-declared preconditions
  requires value$in == null || !($Heap[this, $ownerRef] == $Heap[value$in, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[value$in, $ownerFrame]);
  requires comparer$in == null || !($Heap[this, $ownerRef] == $Heap[comparer$in, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[comparer$in, $ownerFrame]);
  // target object is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // target object is peer consistent (owner must not be valid)
  requires $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
  // value is peer consistent
  requires value$in == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[value$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[value$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // value is peer consistent (owner must not be valid)
  requires value$in == null || $Heap[value$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[value$in, $ownerRef], $inv] <: $Heap[value$in, $ownerFrame]) || $Heap[$Heap[value$in, $ownerRef], $localinv] == $BaseClass($Heap[value$in, $ownerFrame]);
  // comparer is peer consistent
  requires comparer$in == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[comparer$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[comparer$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // comparer is peer consistent (owner must not be valid)
  requires comparer$in == null || $Heap[comparer$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[comparer$in, $ownerRef], $inv] <: $Heap[comparer$in, $ownerFrame]) || $Heap[$Heap[comparer$in, $ownerRef], $localinv] == $BaseClass($Heap[comparer$in, $ownerFrame]);
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // user-declared postconditions
  ensures $result < #Collections.ArrayList.get_Count($Heap, this);
  ensures 0 <= $result && $result < #Collections.ArrayList.get_Count($Heap, this) ==> #Collections.ArrayList.get_Item$System.Int32($Heap, this, $result) == value$in;
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



implementation Collections.ArrayList.BinarySearch$System.Object$System.Collections.IComparer(this: ref, value$in: ref, comparer$in: ref) returns ($result: int)
{
  var value: ref where $Is(value, System.Object) && $Heap[value, $allocated], comparer: ref where $Is(comparer, System.Collections.IComparer) && $Heap[comparer, $allocated], stack0i: int, stack1i: int, stack2o: ref, stack3o: ref, return.value: int where InRange(return.value, System.Int32), SS$Display.Return.Local: int where InRange(SS$Display.Return.Local, System.Int32);

  entry:
    value := value$in;
    comparer := comparer$in;
    goto block27319;

  block27319:
    goto block27710;

  block27710:
    // ----- nop
    // ----- load constant 0  ----- ArrayList.ssc(183,7)
    stack0i := 0;
    // ----- call  ----- ArrayList.ssc(183,7)
    assert this != null;
    call stack1i := Collections.ArrayList.get_Count$.Virtual.$(this, false);
    // ----- copy  ----- ArrayList.ssc(183,7)
    stack2o := value;
    // ----- copy  ----- ArrayList.ssc(183,7)
    stack3o := comparer;
    // ----- call  ----- ArrayList.ssc(183,7)
    assert this != null;
    call return.value := Collections.ArrayList.BinarySearch$System.Int32$System.Int32$System.Object$System.Collections.IComparer$.Virtual.$(this, stack0i, stack1i, stack2o, stack3o);
    // ----- branch
    goto block27387;

  block27387:
    // ----- nop
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0i := return.value;
    // ----- return
    $result := stack0i;
    return;
}



procedure Collections.ArrayList.Clear(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated]);
  // target object is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // target object is peer consistent (owner must not be valid)
  requires $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // user-declared postconditions
  ensures #Collections.ArrayList.get_Count($Heap, this) == 0;
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



implementation Collections.ArrayList.Clear(this: ref)
{
  var temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception) && $Heap[local2, $allocated], stack0o: ref, stack1i: int, stack2i: int, stack0i: int, temp2: exposeVersionType, stack0b: bool, stack0s: struct;

  entry:
    goto block28951;

  block28951:
    goto block29104;

  block29104:
    // ----- nop
    // ----- FrameGuard processing  ----- ArrayList.ssc(190,15)
    temp0 := this;
    // ----- load token  ----- ArrayList.ssc(190,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(190,15)
    stack1o := TypeObject(Collections.ArrayList);
    // ----- local unpack  ----- ArrayList.ssc(190,15)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: Collections.ArrayList && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block29121;

  block29121:
    // ----- load field  ----- ArrayList.ssc(191,9)
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- load constant 0  ----- ArrayList.ssc(191,9)
    stack1i := 0;
    // ----- load field  ----- ArrayList.ssc(191,9)
    assert this != null;
    stack2i := $Heap[this, Collections.ArrayList._size];
    // ----- call  ----- ArrayList.ssc(191,9)
    call System.Array.Clear$System.Array$notnull$System.Int32$System.Int32(stack0o, stack1i, stack2i);
    // ----- serialized AssumeStatement  ----- ArrayList.ssc(192,9)
    assume (forall ^i: int :: 0 <= ^i && ^i <= $Heap[this, Collections.ArrayList._size] - 1 ==> RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], ^i) == null);
    goto block29393;

  block29393:
    // ----- nop
    // ----- load constant 0  ----- ArrayList.ssc(193,9)
    stack0i := 0;
    // ----- store field  ----- ArrayList.ssc(193,9)
    assert this != null;
    assert $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
    havoc temp2;
    $Heap[this, $exposeVersion] := temp2;
    $Heap[this, Collections.ArrayList._size] := stack0i;
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || TypeObject($typeof($Heap[this, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || 0 <= $Heap[this, Collections.ArrayList._size];
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || $Heap[this, Collections.ArrayList._size] <= $Length($Heap[this, Collections.ArrayList._items]);
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || (forall ^i: int :: $Heap[this, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[this, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], ^i) == null);
    assume IsHeap($Heap);
    // ----- branch
    goto block29563;

  block29563:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true29563to29580, false29563to29597;

  true29563to29580:
    assume local2 == stack0o;
    goto block29580;

  false29563to29597:
    assume local2 != stack0o;
    goto block29597;

  block29580:
    // ----- load token  ----- ArrayList.ssc(194,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(194,7)
    stack0o := TypeObject(Collections.ArrayList);
    // ----- local pack  ----- ArrayList.ssc(194,7)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert TypeObject($typeof($Heap[temp0, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert 0 <= $Heap[temp0, Collections.ArrayList._size];
    assert $Heap[temp0, Collections.ArrayList._size] <= $Length($Heap[temp0, Collections.ArrayList._items]);
    assert (forall ^i: int :: $Heap[temp0, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[temp0, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[temp0, Collections.ArrayList._items], $elements], ^i) == null);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Collections.ArrayList ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block29648;

  block29597:
    // ----- is instance
    // ----- branch
    goto true29597to29580, false29597to29614;

  true29597to29580:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block29580;

  false29597to29614:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block29614;

  block29614:
    // ----- branch
    goto block29648;

  block29648:
    // ----- nop
    // ----- branch
    goto block29529;

  block29529:
    // ----- nop
    // ----- return
    return;
}



procedure System.Array.Clear$System.Array$notnull$System.Int32$System.Int32(array$in: ref where $IsNotNull(array$in, System.Array) && $Heap[array$in, $allocated], index$in: int where InRange(index$in, System.Int32), length$in: int where InRange(length$in, System.Int32));
  // user-declared preconditions
  requires array$in != null;
  requires $Rank(array$in) == 1;
  requires index$in >= $LBound(array$in, 0);
  requires length$in >= 0;
  requires $Length(array$in) - (index$in + $LBound(array$in, 0)) >= length$in;
  // array is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[array$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[array$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // array is peer consistent (owner must not be valid)
  requires $Heap[array$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[array$in, $ownerRef], $inv] <: $Heap[array$in, $ownerFrame]) || $Heap[$Heap[array$in, $ownerRef], $localinv] == $BaseClass($Heap[array$in, $ownerFrame]);
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



procedure Collections.ArrayList.Clone(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated]) returns ($result: ref where $Is($result, System.Object) && $Heap[$result, $allocated]);
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



implementation Collections.ArrayList.Clone(this: ref) returns ($result: ref)
{
  var stack0i: int, stack50000o: ref, stack0o: ref, la: ref where $Is(la, Collections.ArrayList) && $Heap[la, $allocated], temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local3: ref where $Is(local3, System.Exception) && $Heap[local3, $allocated], temp2: exposeVersionType, temp3: ref, temp4: exposeVersionType, local5: ref where $Is(local5, System.Exception) && $Heap[local5, $allocated], stack1i: int, stack2o: ref, stack3i: int, stack4i: int, stack0b: bool, stack0s: struct, return.value: ref where $Is(return.value, System.Object) && $Heap[return.value, $allocated], SS$Display.Return.Local: ref where $Is(SS$Display.Return.Local, System.Object) && $Heap[SS$Display.Return.Local, $allocated];

  entry:
    goto block31110;

  block31110:
    goto block31263;

  block31263:
    // ----- nop
    // ----- load field  ----- ArrayList.ssc(200,17)
    assert this != null;
    stack0i := $Heap[this, Collections.ArrayList._size];
    // ----- new object  ----- ArrayList.ssc(200,17)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == Collections.ArrayList;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    // ----- call  ----- ArrayList.ssc(200,17)
    assert stack50000o != null;
    call Collections.ArrayList..ctor$System.Int32(stack50000o, stack0i);
    // ----- copy  ----- ArrayList.ssc(200,17)
    stack0o := stack50000o;
    // ----- copy  ----- ArrayList.ssc(200,17)
    la := stack0o;
    // ----- FrameGuard processing  ----- ArrayList.ssc(201,15)
    temp0 := la;
    // ----- load token  ----- ArrayList.ssc(201,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(201,15)
    stack1o := TypeObject(Collections.ArrayList);
    // ----- local unpack  ----- ArrayList.ssc(201,15)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: Collections.ArrayList && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local3 := null;
    goto block31280;

  block31280:
    // ----- load field  ----- ArrayList.ssc(202,9)
    assert this != null;
    stack0i := $Heap[this, Collections.ArrayList._size];
    // ----- store field  ----- ArrayList.ssc(202,9)
    assert la != null;
    assert $Heap[la, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[la, $ownerRef], $inv] <: $Heap[la, $ownerFrame]) || $Heap[$Heap[la, $ownerRef], $localinv] == $BaseClass($Heap[la, $ownerFrame]);
    havoc temp2;
    $Heap[la, $exposeVersion] := temp2;
    $Heap[la, Collections.ArrayList._size] := stack0i;
    assert !($Heap[la, $inv] <: Collections.ArrayList && $Heap[la, $localinv] != $BaseClass(Collections.ArrayList)) || TypeObject($typeof($Heap[la, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert !($Heap[la, $inv] <: Collections.ArrayList && $Heap[la, $localinv] != $BaseClass(Collections.ArrayList)) || 0 <= $Heap[la, Collections.ArrayList._size];
    assert !($Heap[la, $inv] <: Collections.ArrayList && $Heap[la, $localinv] != $BaseClass(Collections.ArrayList)) || $Heap[la, Collections.ArrayList._size] <= $Length($Heap[la, Collections.ArrayList._items]);
    assert !($Heap[la, $inv] <: Collections.ArrayList && $Heap[la, $localinv] != $BaseClass(Collections.ArrayList)) || (forall ^i: int :: $Heap[la, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[la, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[la, Collections.ArrayList._items], $elements], ^i) == null);
    assume IsHeap($Heap);
    // ----- FrameGuard processing  ----- ArrayList.ssc(203,17)
    temp3 := this;
    // ----- load token  ----- ArrayList.ssc(203,17)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(203,17)
    stack1o := TypeObject(Collections.ArrayList);
    // ----- local unpack  ----- ArrayList.ssc(203,17)
    assert temp3 != null;
    assert ($Heap[temp3, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp3, $ownerRef], $inv] <: $Heap[temp3, $ownerFrame]) || $Heap[$Heap[temp3, $ownerRef], $localinv] == $BaseClass($Heap[temp3, $ownerFrame])) && $Heap[temp3, $inv] <: Collections.ArrayList && $Heap[temp3, $localinv] == $typeof(temp3);
    $Heap[temp3, $localinv] := System.Object;
    havoc temp4;
    $Heap[temp3, $exposeVersion] := temp4;
    assume IsHeap($Heap);
    local5 := null;
    goto block31297;

  block31297:
    // ----- load field  ----- ArrayList.ssc(204,11)
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- load constant 0  ----- ArrayList.ssc(204,11)
    stack1i := 0;
    // ----- load field  ----- ArrayList.ssc(204,11)
    assert la != null;
    stack2o := $Heap[la, Collections.ArrayList._items];
    // ----- load constant 0  ----- ArrayList.ssc(204,11)
    stack3i := 0;
    // ----- load field  ----- ArrayList.ssc(204,11)
    assert this != null;
    stack4i := $Heap[this, Collections.ArrayList._size];
    // ----- call  ----- ArrayList.ssc(204,11)
    call System.Array.Copy$System.Array$notnull$System.Int32$System.Array$notnull$System.Int32$System.Int32(stack0o, stack1i, stack2o, stack3i, stack4i);
    // ----- branch
    goto block31535;

  block31535:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true31535to31637, false31535to31654;

  true31535to31637:
    assume local5 == stack0o;
    goto block31637;

  false31535to31654:
    assume local5 != stack0o;
    goto block31654;

  block31637:
    // ----- load token  ----- ArrayList.ssc(205,9)
    havoc stack0s;
    assume $IsTokenForType(stack0s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(205,9)
    stack0o := TypeObject(Collections.ArrayList);
    // ----- local pack  ----- ArrayList.ssc(205,9)
    assert temp3 != null;
    assert $Heap[temp3, $localinv] == System.Object;
    assert TypeObject($typeof($Heap[temp3, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert 0 <= $Heap[temp3, Collections.ArrayList._size];
    assert $Heap[temp3, Collections.ArrayList._size] <= $Length($Heap[temp3, Collections.ArrayList._items]);
    assert (forall ^i: int :: $Heap[temp3, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[temp3, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[temp3, Collections.ArrayList._items], $elements], ^i) == null);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == temp3 && $Heap[$p, $ownerFrame] == Collections.ArrayList ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp3, $localinv] := $typeof(temp3);
    assume IsHeap($Heap);
    goto block31688;

  block31654:
    // ----- is instance
    // ----- branch
    goto true31654to31637, false31654to31569;

  true31654to31637:
    assume $As(local5, Microsoft.Contracts.ICheckedException) != null;
    goto block31637;

  false31654to31569:
    assume $As(local5, Microsoft.Contracts.ICheckedException) == null;
    goto block31569;

  block31569:
    // ----- branch
    goto block31688;

  block31688:
    // ----- nop
    // ----- branch
    goto block31348;

  block31348:
    // ----- branch
    goto block31620;

  block31620:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true31620to31484, false31620to31671;

  true31620to31484:
    assume local3 == stack0o;
    goto block31484;

  false31620to31671:
    assume local3 != stack0o;
    goto block31671;

  block31484:
    // ----- load token  ----- ArrayList.ssc(206,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(206,7)
    stack0o := TypeObject(Collections.ArrayList);
    // ----- local pack  ----- ArrayList.ssc(206,7)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert TypeObject($typeof($Heap[temp0, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert 0 <= $Heap[temp0, Collections.ArrayList._size];
    assert $Heap[temp0, Collections.ArrayList._size] <= $Length($Heap[temp0, Collections.ArrayList._items]);
    assert (forall ^i: int :: $Heap[temp0, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[temp0, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[temp0, Collections.ArrayList._items], $elements], ^i) == null);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Collections.ArrayList ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block31450;

  block31671:
    // ----- is instance
    // ----- branch
    goto true31671to31484, false31671to31518;

  true31671to31484:
    assume $As(local3, Microsoft.Contracts.ICheckedException) != null;
    goto block31484;

  false31671to31518:
    assume $As(local3, Microsoft.Contracts.ICheckedException) == null;
    goto block31518;

  block31518:
    // ----- branch
    goto block31450;

  block31450:
    // ----- nop
    // ----- branch
    goto block31399;

  block31399:
    // ----- copy  ----- ArrayList.ssc(207,7)
    return.value := la;
    // ----- branch
    goto block31416;

  block31416:
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0o := return.value;
    // ----- return
    $result := stack0o;
    return;
}



procedure Collections.ArrayList.Contains$System.Object(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], item$in: ref where $Is(item$in, System.Object) && $Heap[item$in, $allocated]) returns ($result: bool where true);
  // target object is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // target object is peer consistent (owner must not be valid)
  requires $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
  // item is peer consistent
  requires item$in == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[item$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[item$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // item is peer consistent (owner must not be valid)
  requires item$in == null || $Heap[item$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[item$in, $ownerRef], $inv] <: $Heap[item$in, $ownerFrame]) || $Heap[$Heap[item$in, $ownerRef], $localinv] == $BaseClass($Heap[item$in, $ownerFrame]);
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



implementation Collections.ArrayList.Contains$System.Object(this: ref, item$in: ref) returns ($result: bool)
{
  var item: ref where $Is(item, System.Object) && $Heap[item, $allocated], stack0o: ref, stack0b: bool, i: int where InRange(i, System.Int32), stack0i: int, return.value: bool where true, stack1i: int, stack1o: ref, SS$Display.Return.Local: bool where true, local3: int where InRange(local3, System.Int32), local5: int where InRange(local5, System.Int32), $Heap$block33643$LoopPreheader: [ref,<x>name]x, $Heap$block33507$LoopPreheader: [ref,<x>name]x;

  entry:
    item := item$in;
    goto block33320;

  block33320:
    goto block33456;

  block33456:
    // ----- nop
    stack0o := null;
    // ----- binary operator  ----- ArrayList.ssc(213,7)
    // ----- branch  ----- ArrayList.ssc(213,7)
    goto true33456to33371, false33456to33490;

  true33456to33371:
    assume item != stack0o;
    goto block33371;

  false33456to33490:
    assume item == stack0o;
    goto block33490;

  block33371:
    // ----- load constant 0  ----- ArrayList.ssc(222,17)
    i := 0;
    goto block33507$LoopPreheader;

  block33490:
    // ----- load constant 0  ----- ArrayList.ssc(215,17)
    i := 0;
    goto block33643$LoopPreheader;

  block33643:
    // ----- default loop invariant: allocation and ownership are stable  ----- ArrayList.ssc(215,22)
    assume (forall $o: ref :: { $Heap[$o, $allocated] } $Heap$block33643$LoopPreheader[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } $Heap$block33643$LoopPreheader[$ot, $allocated] && $Heap$block33643$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block33643$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block33643$LoopPreheader[$ot, $ownerFrame]) && $Heap$block33643$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: exposure  ----- ArrayList.ssc(215,22)
    assume (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $Heap$block33643$LoopPreheader[$o, $allocated] ==> $Heap$block33643$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block33643$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]);
    assume (forall $o: ref :: !$Heap$block33643$LoopPreheader[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: modifies  ----- ArrayList.ssc(215,22)
    assert (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || !($typeof(this) <: DeclType($f)) || !$IncludedInModifiesStar($f)) && old(true) ==> $Heap$block33643$LoopPreheader[$o, $f] == $Heap[$o, $f]);
    assume $HeapSucc($Heap$block33643$LoopPreheader, $Heap);
    // ----- default loop invariant: owner fields  ----- ArrayList.ssc(215,22)
    assert (forall $o: ref :: { $Heap[$o, $ownerFrame] } { $Heap[$o, $ownerRef] } $o != null && $Heap$block33643$LoopPreheader[$o, $allocated] ==> $Heap[$o, $ownerRef] == $Heap$block33643$LoopPreheader[$o, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap$block33643$LoopPreheader[$o, $ownerFrame]);
    // ----- advance activity
    havoc $ActivityIndicator;
    // ----- load field  ----- ArrayList.ssc(215,22)
    assert this != null;
    stack0i := $Heap[this, Collections.ArrayList._size];
    // ----- binary operator  ----- ArrayList.ssc(215,22)
    // ----- branch  ----- ArrayList.ssc(215,22)
    goto true33643to33558, false33643to33626;

  true33643to33558:
    assume i >= stack0i;
    goto block33558;

  false33643to33626:
    assume i < stack0i;
    goto block33626;

  block33558:
    // ----- load constant 0  ----- ArrayList.ssc(218,9)
    return.value := false;
    // ----- branch
    goto block33660;

  block33626:
    // ----- load field  ----- ArrayList.ssc(216,11)
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- copy  ----- ArrayList.ssc(216,11)
    stack1i := i;
    // ----- load element  ----- ArrayList.ssc(216,11)
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    stack0o := RefArrayGet($Heap[stack0o, $elements], stack1i);
    stack1o := null;
    // ----- binary operator  ----- ArrayList.ssc(216,11)
    // ----- branch  ----- ArrayList.ssc(216,11)
    goto true33626to33524, false33626to33422;

  block33507:
    // ----- default loop invariant: allocation and ownership are stable  ----- ArrayList.ssc(222,22)
    assume (forall $o: ref :: { $Heap[$o, $allocated] } $Heap$block33507$LoopPreheader[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } $Heap$block33507$LoopPreheader[$ot, $allocated] && $Heap$block33507$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block33507$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block33507$LoopPreheader[$ot, $ownerFrame]) && $Heap$block33507$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: exposure  ----- ArrayList.ssc(222,22)
    assume (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $Heap$block33507$LoopPreheader[$o, $allocated] ==> $Heap$block33507$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block33507$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]);
    assume (forall $o: ref :: !$Heap$block33507$LoopPreheader[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: modifies  ----- ArrayList.ssc(222,22)
    assert (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || !($typeof(this) <: DeclType($f)) || !$IncludedInModifiesStar($f)) && old(true) ==> $Heap$block33507$LoopPreheader[$o, $f] == $Heap[$o, $f]);
    assume $HeapSucc($Heap$block33507$LoopPreheader, $Heap);
    // ----- default loop invariant: owner fields  ----- ArrayList.ssc(222,22)
    assert (forall $o: ref :: { $Heap[$o, $ownerFrame] } { $Heap[$o, $ownerRef] } $o != null && $Heap$block33507$LoopPreheader[$o, $allocated] ==> $Heap[$o, $ownerRef] == $Heap$block33507$LoopPreheader[$o, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap$block33507$LoopPreheader[$o, $ownerFrame]);
    // ----- advance activity
    havoc $ActivityIndicator;
    // ----- load field  ----- ArrayList.ssc(222,22)
    assert this != null;
    stack0i := $Heap[this, Collections.ArrayList._size];
    // ----- binary operator  ----- ArrayList.ssc(222,22)
    // ----- branch  ----- ArrayList.ssc(222,22)
    goto true33507to33337, false33507to33592;

  true33507to33337:
    assume i >= stack0i;
    goto block33337;

  false33507to33592:
    assume i < stack0i;
    goto block33592;

  block33337:
    // ----- load constant 0  ----- ArrayList.ssc(225,9)
    return.value := false;
    // ----- branch
    goto block33660;

  block33592:
    // ----- load field  ----- ArrayList.ssc(223,11)
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- copy  ----- ArrayList.ssc(223,11)
    stack1i := i;
    // ----- load element  ----- ArrayList.ssc(223,11)
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    stack0o := RefArrayGet($Heap[stack0o, $elements], stack1i);
    // ----- binary operator  ----- ArrayList.ssc(223,11)
    // ----- branch  ----- ArrayList.ssc(223,11)
    goto true33592to33575, false33592to33354;

  true33626to33524:
    assume stack0o != stack1o;
    goto block33524;

  false33626to33422:
    assume stack0o == stack1o;
    goto block33422;

  block33524:
    // ----- copy  ----- ArrayList.ssc(215,31)
    local3 := i;
    // ----- load constant 1  ----- ArrayList.ssc(215,31)
    stack0i := 1;
    // ----- binary operator  ----- ArrayList.ssc(215,31)
    stack0i := local3 + stack0i;
    // ----- copy  ----- ArrayList.ssc(215,31)
    i := stack0i;
    // ----- copy
    stack0i := local3;
    // ----- branch
    goto block33643;

  block33422:
    // ----- load constant 1  ----- ArrayList.ssc(217,13)
    return.value := true;
    // ----- branch
    goto block33660;

  true33592to33575:
    assume item != stack0o;
    goto block33575;

  false33592to33354:
    assume item == stack0o;
    goto block33354;

  block33575:
    // ----- copy  ----- ArrayList.ssc(222,31)
    local5 := i;
    // ----- load constant 1  ----- ArrayList.ssc(222,31)
    stack0i := 1;
    // ----- binary operator  ----- ArrayList.ssc(222,31)
    stack0i := local5 + stack0i;
    // ----- copy  ----- ArrayList.ssc(222,31)
    i := stack0i;
    // ----- copy
    stack0i := local5;
    // ----- branch
    goto block33507;

  block33354:
    // ----- load constant 1  ----- ArrayList.ssc(224,13)
    return.value := true;
    // ----- branch
    goto block33660;

  block33660:
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0b := return.value;
    // ----- return
    $result := stack0b;
    return;

  block33643$LoopPreheader:
    $Heap$block33643$LoopPreheader := $Heap;
    goto block33643;

  block33507$LoopPreheader:
    $Heap$block33507$LoopPreheader := $Heap;
    goto block33507;
}



procedure Collections.ArrayList.CopyTo$System.Array$notnull(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], array$in: ref where $IsNotNull(array$in, System.Array) && $Heap[array$in, $allocated]);
  // user-declared preconditions
  requires #Collections.ArrayList.get_Count($Heap, this) <= $Length(array$in);
  requires $Rank(array$in) == 1;
  requires !($Heap[this, $ownerRef] == $Heap[array$in, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[array$in, $ownerFrame]);
  // target object is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // target object is peer consistent (owner must not be valid)
  requires $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
  // array is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[array$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[array$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // array is peer consistent (owner must not be valid)
  requires $Heap[array$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[array$in, $ownerRef], $inv] <: $Heap[array$in, $ownerFrame]) || $Heap[$Heap[array$in, $ownerRef], $localinv] == $BaseClass($Heap[array$in, $ownerFrame]);
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(($o != array$in || !($typeof(array$in) <: DeclType($f)) || !$IncludedInModifiesStar($f)) && ($o != this || !($typeof(this) <: DeclType($f)) || !$IncludedInModifiesStar($f))) && old($o != array$in || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Collections.ArrayList.CopyTo$System.Array$notnull(this: ref, array$in: ref)
{
  var array: ref where $IsNotNull(array, System.Array) && $Heap[array, $allocated], stack0o: ref, stack1i: int;

  entry:
    array := array$in;
    goto block34782;

  block34782:
    goto block35105;

  block35105:
    // ----- nop
    // ----- copy  ----- ArrayList.ssc(236,7)
    stack0o := array;
    // ----- load constant 0  ----- ArrayList.ssc(236,7)
    stack1i := 0;
    // ----- call  ----- ArrayList.ssc(236,7)
    assert this != null;
    call Collections.ArrayList.CopyTo$System.Array$notnull$System.Int32$.Virtual.$(this, stack0o, stack1i);
    // ----- return
    return;
}



procedure Collections.ArrayList.CopyTo$System.Array$notnull$System.Int32$.Virtual.$(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], array$in: ref where $IsNotNull(array$in, System.Array) && $Heap[array$in, $allocated], arrayIndex$in: int where InRange(arrayIndex$in, System.Int32));
  // user-declared preconditions
  requires $Rank(array$in) == 1;
  requires 0 <= arrayIndex$in;
  requires arrayIndex$in + #Collections.ArrayList.get_Count($Heap, this) <= $Length(array$in);
  requires !($Heap[this, $ownerRef] == $Heap[array$in, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[array$in, $ownerFrame]);
  // target object is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // target object is peer consistent (owner must not be valid)
  requires $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
  // array is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[array$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[array$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // array is peer consistent (owner must not be valid)
  requires $Heap[array$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[array$in, $ownerRef], $inv] <: $Heap[array$in, $ownerFrame]) || $Heap[$Heap[array$in, $ownerRef], $localinv] == $BaseClass($Heap[array$in, $ownerFrame]);
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(($o != array$in || !($typeof(array$in) <: DeclType($f)) || !$IncludedInModifiesStar($f)) && ($o != this || !($typeof(this) <: DeclType($f)) || !$IncludedInModifiesStar($f))) && old($o != array$in || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



procedure Collections.ArrayList.CopyTo$System.Array$notnull$System.Int32(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], array$in: ref where $IsNotNull(array$in, System.Array) && $Heap[array$in, $allocated], arrayIndex$in: int where InRange(arrayIndex$in, System.Int32));
  // user-declared preconditions
  requires $Rank(array$in) == 1;
  requires 0 <= arrayIndex$in;
  requires arrayIndex$in + #Collections.ArrayList.get_Count($Heap, this) <= $Length(array$in);
  requires !($Heap[this, $ownerRef] == $Heap[array$in, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[array$in, $ownerFrame]);
  // target object is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // target object is peer consistent (owner must not be valid)
  requires $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
  // array is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[array$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[array$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // array is peer consistent (owner must not be valid)
  requires $Heap[array$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[array$in, $ownerRef], $inv] <: $Heap[array$in, $ownerFrame]) || $Heap[$Heap[array$in, $ownerRef], $localinv] == $BaseClass($Heap[array$in, $ownerFrame]);
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(($o != array$in || !($typeof(array$in) <: DeclType($f)) || !$IncludedInModifiesStar($f)) && ($o != this || !($typeof(this) <: DeclType($f)) || !$IncludedInModifiesStar($f))) && old($o != array$in || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Collections.ArrayList.CopyTo$System.Array$notnull$System.Int32(this: ref, array$in: ref, arrayIndex$in: int)
{
  var array: ref where $IsNotNull(array, System.Array) && $Heap[array, $allocated], arrayIndex: int where InRange(arrayIndex, System.Int32), temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception) && $Heap[local2, $allocated], stack0o: ref, stack1i: int, stack2o: ref, stack3i: int, stack4i: int, stack0b: bool, stack0s: struct;

  entry:
    array := array$in;
    arrayIndex := arrayIndex$in;
    goto block35870;

  block35870:
    goto block36244;

  block36244:
    // ----- nop
    // ----- FrameGuard processing  ----- ArrayList.ssc(246,15)
    temp0 := this;
    // ----- load token  ----- ArrayList.ssc(246,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(246,15)
    stack1o := TypeObject(Collections.ArrayList);
    // ----- local unpack  ----- ArrayList.ssc(246,15)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: Collections.ArrayList && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block36261;

  block36261:
    // ----- load field  ----- ArrayList.ssc(247,9)
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- load constant 0  ----- ArrayList.ssc(247,9)
    stack1i := 0;
    // ----- copy  ----- ArrayList.ssc(247,9)
    stack2o := array;
    // ----- copy  ----- ArrayList.ssc(247,9)
    stack3i := arrayIndex;
    // ----- load field  ----- ArrayList.ssc(247,9)
    assert this != null;
    stack4i := $Heap[this, Collections.ArrayList._size];
    // ----- call  ----- ArrayList.ssc(247,9)
    call System.Array.Copy$System.Array$notnull$System.Int32$System.Array$notnull$System.Int32$System.Int32(stack0o, stack1i, stack2o, stack3i, stack4i);
    // ----- branch
    goto block36414;

  block36414:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true36414to36346, false36414to36465;

  true36414to36346:
    assume local2 == stack0o;
    goto block36346;

  false36414to36465:
    assume local2 != stack0o;
    goto block36465;

  block36346:
    // ----- load token  ----- ArrayList.ssc(248,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(248,7)
    stack0o := TypeObject(Collections.ArrayList);
    // ----- local pack  ----- ArrayList.ssc(248,7)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert TypeObject($typeof($Heap[temp0, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert 0 <= $Heap[temp0, Collections.ArrayList._size];
    assert $Heap[temp0, Collections.ArrayList._size] <= $Length($Heap[temp0, Collections.ArrayList._items]);
    assert (forall ^i: int :: $Heap[temp0, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[temp0, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[temp0, Collections.ArrayList._items], $elements], ^i) == null);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Collections.ArrayList ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block36397;

  block36465:
    // ----- is instance
    // ----- branch
    goto true36465to36346, false36465to36363;

  true36465to36346:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block36346;

  false36465to36363:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block36363;

  block36363:
    // ----- branch
    goto block36397;

  block36397:
    // ----- nop
    // ----- branch
    goto block36312;

  block36312:
    // ----- return
    return;
}



procedure Collections.ArrayList.CopyTo$System.Int32$System.Array$notnull$System.Int32$System.Int32(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], index$in: int where InRange(index$in, System.Int32), array$in: ref where $IsNotNull(array$in, System.Array) && $Heap[array$in, $allocated], arrayIndex$in: int where InRange(arrayIndex$in, System.Int32), count$in: int where InRange(count$in, System.Int32));
  // user-declared preconditions
  requires $Rank(array$in) == 1;
  requires 0 <= index$in;
  requires index$in < #Collections.ArrayList.get_Count($Heap, this);
  requires 0 <= arrayIndex$in;
  requires arrayIndex$in < $Length(array$in);
  requires 0 <= count$in;
  requires index$in + count$in <= #Collections.ArrayList.get_Count($Heap, this);
  requires arrayIndex$in + count$in <= $Length(array$in);
  requires !($Heap[this, $ownerRef] == $Heap[array$in, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[array$in, $ownerFrame]);
  // target object is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // target object is peer consistent (owner must not be valid)
  requires $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
  // array is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[array$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[array$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // array is peer consistent (owner must not be valid)
  requires $Heap[array$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[array$in, $ownerRef], $inv] <: $Heap[array$in, $ownerFrame]) || $Heap[$Heap[array$in, $ownerRef], $localinv] == $BaseClass($Heap[array$in, $ownerFrame]);
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(($o != array$in || !($typeof(array$in) <: DeclType($f)) || !$IncludedInModifiesStar($f)) && ($o != this || !($typeof(this) <: DeclType($f)) || !$IncludedInModifiesStar($f))) && old($o != array$in || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Collections.ArrayList.CopyTo$System.Int32$System.Array$notnull$System.Int32$System.Int32(this: ref, index$in: int, array$in: ref, arrayIndex$in: int, count$in: int)
{
  var index: int where InRange(index, System.Int32), array: ref where $IsNotNull(array, System.Array) && $Heap[array, $allocated], arrayIndex: int where InRange(arrayIndex, System.Int32), count: int where InRange(count, System.Int32), temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception) && $Heap[local2, $allocated], stack0o: ref, stack1i: int, stack2o: ref, stack3i: int, stack4i: int, stack0b: bool, stack0s: struct;

  entry:
    index := index$in;
    array := array$in;
    arrayIndex := arrayIndex$in;
    count := count$in;
    goto block37893;

  block37893:
    goto block38488;

  block38488:
    // ----- nop
    // ----- FrameGuard processing  ----- ArrayList.ssc(262,15)
    temp0 := this;
    // ----- load token  ----- ArrayList.ssc(262,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(262,15)
    stack1o := TypeObject(Collections.ArrayList);
    // ----- local unpack  ----- ArrayList.ssc(262,15)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: Collections.ArrayList && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block38505;

  block38505:
    // ----- load field  ----- ArrayList.ssc(263,9)
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- copy  ----- ArrayList.ssc(263,9)
    stack1i := index;
    // ----- copy  ----- ArrayList.ssc(263,9)
    stack2o := array;
    // ----- copy  ----- ArrayList.ssc(263,9)
    stack3i := arrayIndex;
    // ----- copy  ----- ArrayList.ssc(263,9)
    stack4i := count;
    // ----- call  ----- ArrayList.ssc(263,9)
    call System.Array.Copy$System.Array$notnull$System.Int32$System.Array$notnull$System.Int32$System.Int32(stack0o, stack1i, stack2o, stack3i, stack4i);
    // ----- branch
    goto block38709;

  block38709:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true38709to38607, false38709to38658;

  true38709to38607:
    assume local2 == stack0o;
    goto block38607;

  false38709to38658:
    assume local2 != stack0o;
    goto block38658;

  block38607:
    // ----- load token  ----- ArrayList.ssc(264,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(264,7)
    stack0o := TypeObject(Collections.ArrayList);
    // ----- local pack  ----- ArrayList.ssc(264,7)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert TypeObject($typeof($Heap[temp0, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert 0 <= $Heap[temp0, Collections.ArrayList._size];
    assert $Heap[temp0, Collections.ArrayList._size] <= $Length($Heap[temp0, Collections.ArrayList._items]);
    assert (forall ^i: int :: $Heap[temp0, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[temp0, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[temp0, Collections.ArrayList._items], $elements], ^i) == null);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Collections.ArrayList ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block38675;

  block38658:
    // ----- is instance
    // ----- branch
    goto true38658to38607, false38658to38624;

  true38658to38607:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block38607;

  false38658to38624:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block38624;

  block38624:
    // ----- branch
    goto block38675;

  block38675:
    // ----- nop
    // ----- branch
    goto block38556;

  block38556:
    // ----- return
    return;
}



procedure Collections.ArrayList.IndexOf$System.Object(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], value$in: ref where $Is(value$in, System.Object) && $Heap[value$in, $allocated]) returns ($result: int where InRange($result, System.Int32));
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
  // user-declared postconditions
  ensures -1 <= $result;
  ensures $result < #Collections.ArrayList.get_Count($Heap, this);
  ensures ($result == -1 && !(exists ^i: int :: 0 <= ^i && ^i <= #Collections.ArrayList.get_Count($Heap, this) - 1 && #Collections.ArrayList.get_Item$System.Int32($Heap, this, ^i) == value$in)) || (0 <= $result && $result < #Collections.ArrayList.get_Count($Heap, this) && #Collections.ArrayList.get_Item$System.Int32($Heap, this, $result) == value$in);
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



implementation Collections.ArrayList.IndexOf$System.Object(this: ref, value$in: ref) returns ($result: int)
{
  var value: ref where $Is(value, System.Object) && $Heap[value, $allocated], temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception) && $Heap[local2, $allocated], stack0o: ref, stack2i: int, stack3i: int, return.value: int where InRange(return.value, System.Int32), stack0b: bool, stack0s: struct, SS$Display.Return.Local: int where InRange(SS$Display.Return.Local, System.Int32), stack0i: int;

  entry:
    value := value$in;
    goto block40358;

  block40358:
    goto block40511;

  block40511:
    // ----- nop
    // ----- FrameGuard processing  ----- ArrayList.ssc(275,15)
    temp0 := this;
    // ----- load token  ----- ArrayList.ssc(275,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(275,15)
    stack1o := TypeObject(Collections.ArrayList);
    // ----- local unpack  ----- ArrayList.ssc(275,15)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: Collections.ArrayList && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block40528;

  block40528:
    // ----- load field  ----- ArrayList.ssc(276,9)
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- copy  ----- ArrayList.ssc(276,9)
    stack1o := value;
    // ----- load constant 0  ----- ArrayList.ssc(276,9)
    stack2i := 0;
    // ----- load field  ----- ArrayList.ssc(276,9)
    assert this != null;
    stack3i := $Heap[this, Collections.ArrayList._size];
    // ----- call  ----- ArrayList.ssc(276,9)
    call return.value := System.Array.IndexOf...System.Object$System.Object.array$System.Object$System.Int32$System.Int32(stack0o, stack1o, stack2i, stack3i);
    // ----- branch
    goto block41123;

  block41123:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true41123to41106, false41123to41089;

  true41123to41106:
    assume local2 == stack0o;
    goto block41106;

  false41123to41089:
    assume local2 != stack0o;
    goto block41089;

  block41106:
    // ----- load token  ----- ArrayList.ssc(277,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(277,7)
    stack0o := TypeObject(Collections.ArrayList);
    // ----- local pack  ----- ArrayList.ssc(277,7)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert TypeObject($typeof($Heap[temp0, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert 0 <= $Heap[temp0, Collections.ArrayList._size];
    assert $Heap[temp0, Collections.ArrayList._size] <= $Length($Heap[temp0, Collections.ArrayList._items]);
    assert (forall ^i: int :: $Heap[temp0, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[temp0, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[temp0, Collections.ArrayList._items], $elements], ^i) == null);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Collections.ArrayList ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block41225;

  block41089:
    // ----- is instance
    // ----- branch
    goto true41089to41106, false41089to41157;

  true41089to41106:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block41106;

  false41089to41157:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block41157;

  block41157:
    // ----- branch
    goto block41225;

  block41225:
    // ----- nop
    // ----- branch
    goto block41055;

  block41055:
    // ----- nop
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0i := return.value;
    // ----- return
    $result := stack0i;
    return;
}



procedure System.Array.IndexOf...System.Object$System.Object.array$System.Object$System.Int32$System.Int32(array$in: ref where $Is(array$in, RefArray(System.Object, 1)) && $Heap[array$in, $allocated], value$in: ref where $Is(value$in, System.Object) && $Heap[value$in, $allocated], startIndex$in: int where InRange(startIndex$in, System.Int32), count$in: int where InRange(count$in, System.Int32)) returns ($result: int where InRange($result, System.Int32));
  // array is peer consistent
  requires array$in == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[array$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[array$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // array is peer consistent (owner must not be valid)
  requires array$in == null || $Heap[array$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[array$in, $ownerRef], $inv] <: $Heap[array$in, $ownerFrame]) || $Heap[$Heap[array$in, $ownerRef], $localinv] == $BaseClass($Heap[array$in, $ownerFrame]);
  // value is a peer of the expected elements of the generic object
  requires true;
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



procedure Collections.ArrayList.IndexOf$System.Object$System.Int32(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], value$in: ref where $Is(value$in, System.Object) && $Heap[value$in, $allocated], startIndex$in: int where InRange(startIndex$in, System.Int32)) returns ($result: int where InRange($result, System.Int32));
  // user-declared preconditions
  requires 0 <= startIndex$in;
  requires startIndex$in <= #Collections.ArrayList.get_Count($Heap, this);
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
  // user-declared postconditions
  ensures -1 <= $result;
  ensures $result < #Collections.ArrayList.get_Count($Heap, this);
  ensures ($result == -1 && !(exists ^i: int :: 0 <= ^i && ^i <= #Collections.ArrayList.get_Count($Heap, this) - 1 && #Collections.ArrayList.get_Item$System.Int32($Heap, this, ^i) == value$in)) || (0 <= $result && $result < #Collections.ArrayList.get_Count($Heap, this) && #Collections.ArrayList.get_Item$System.Int32($Heap, this, $result) == value$in);
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



implementation Collections.ArrayList.IndexOf$System.Object$System.Int32(this: ref, value$in: ref, startIndex$in: int) returns ($result: int)
{
  var value: ref where $Is(value, System.Object) && $Heap[value, $allocated], startIndex: int where InRange(startIndex, System.Int32), temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception) && $Heap[local2, $allocated], stack0o: ref, stack2i: int, stack3i: int, return.value: int where InRange(return.value, System.Int32), stack0b: bool, stack0s: struct, SS$Display.Return.Local: int where InRange(SS$Display.Return.Local, System.Int32), stack0i: int;

  entry:
    value := value$in;
    startIndex := startIndex$in;
    goto block42874;

  block42874:
    goto block43095;

  block43095:
    // ----- nop
    // ----- FrameGuard processing  ----- ArrayList.ssc(289,15)
    temp0 := this;
    // ----- load token  ----- ArrayList.ssc(289,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(289,15)
    stack1o := TypeObject(Collections.ArrayList);
    // ----- local unpack  ----- ArrayList.ssc(289,15)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: Collections.ArrayList && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block43112;

  block43112:
    // ----- load field  ----- ArrayList.ssc(290,9)
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- copy  ----- ArrayList.ssc(290,9)
    stack1o := value;
    // ----- copy  ----- ArrayList.ssc(290,9)
    stack2i := startIndex;
    // ----- load field  ----- ArrayList.ssc(290,9)
    assert this != null;
    stack3i := $Heap[this, Collections.ArrayList._size];
    // ----- binary operator  ----- ArrayList.ssc(290,9)
    stack3i := stack3i - startIndex;
    // ----- call  ----- ArrayList.ssc(290,9)
    call return.value := System.Array.IndexOf...System.Object$System.Object.array$System.Object$System.Int32$System.Int32(stack0o, stack1o, stack2i, stack3i);
    // ----- branch
    goto block43707;

  block43707:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true43707to43741, false43707to43673;

  true43707to43741:
    assume local2 == stack0o;
    goto block43741;

  false43707to43673:
    assume local2 != stack0o;
    goto block43673;

  block43741:
    // ----- load token  ----- ArrayList.ssc(291,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(291,7)
    stack0o := TypeObject(Collections.ArrayList);
    // ----- local pack  ----- ArrayList.ssc(291,7)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert TypeObject($typeof($Heap[temp0, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert 0 <= $Heap[temp0, Collections.ArrayList._size];
    assert $Heap[temp0, Collections.ArrayList._size] <= $Length($Heap[temp0, Collections.ArrayList._items]);
    assert (forall ^i: int :: $Heap[temp0, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[temp0, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[temp0, Collections.ArrayList._items], $elements], ^i) == null);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Collections.ArrayList ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block43775;

  block43673:
    // ----- is instance
    // ----- branch
    goto true43673to43741, false43673to43724;

  true43673to43741:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block43741;

  false43673to43724:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block43724;

  block43724:
    // ----- branch
    goto block43775;

  block43775:
    // ----- nop
    // ----- branch
    goto block43639;

  block43639:
    // ----- nop
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0i := return.value;
    // ----- return
    $result := stack0i;
    return;
}



procedure Collections.ArrayList.IndexOf$System.Object$System.Int32$System.Int32(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], value$in: ref where $Is(value$in, System.Object) && $Heap[value$in, $allocated], startIndex$in: int where InRange(startIndex$in, System.Int32), count$in: int where InRange(count$in, System.Int32)) returns ($result: int where InRange($result, System.Int32));
  // user-declared preconditions
  requires 0 <= startIndex$in;
  requires 0 <= count$in;
  requires startIndex$in + count$in <= #Collections.ArrayList.get_Count($Heap, this);
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
  // user-declared postconditions
  ensures -1 <= $result;
  ensures $result < #Collections.ArrayList.get_Count($Heap, this);
  ensures ($result == -1 && !(exists ^i: int :: 0 <= ^i && ^i <= #Collections.ArrayList.get_Count($Heap, this) - 1 && #Collections.ArrayList.get_Item$System.Int32($Heap, this, ^i) == value$in)) || (0 <= $result && $result < #Collections.ArrayList.get_Count($Heap, this) && #Collections.ArrayList.get_Item$System.Int32($Heap, this, $result) == value$in);
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



implementation Collections.ArrayList.IndexOf$System.Object$System.Int32$System.Int32(this: ref, value$in: ref, startIndex$in: int, count$in: int) returns ($result: int)
{
  var value: ref where $Is(value, System.Object) && $Heap[value, $allocated], startIndex: int where InRange(startIndex, System.Int32), count: int where InRange(count, System.Int32), temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception) && $Heap[local2, $allocated], stack0o: ref, stack2i: int, stack3i: int, return.value: int where InRange(return.value, System.Int32), stack0b: bool, stack0s: struct, SS$Display.Return.Local: int where InRange(SS$Display.Return.Local, System.Int32), stack0i: int;

  entry:
    value := value$in;
    startIndex := startIndex$in;
    count := count$in;
    goto block45560;

  block45560:
    goto block45866;

  block45866:
    // ----- nop
    // ----- FrameGuard processing  ----- ArrayList.ssc(305,15)
    temp0 := this;
    // ----- load token  ----- ArrayList.ssc(305,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(305,15)
    stack1o := TypeObject(Collections.ArrayList);
    // ----- local unpack  ----- ArrayList.ssc(305,15)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: Collections.ArrayList && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block45883;

  block45883:
    // ----- load field  ----- ArrayList.ssc(306,9)
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- copy  ----- ArrayList.ssc(306,9)
    stack1o := value;
    // ----- copy  ----- ArrayList.ssc(306,9)
    stack2i := startIndex;
    // ----- copy  ----- ArrayList.ssc(306,9)
    stack3i := count;
    // ----- call  ----- ArrayList.ssc(306,9)
    call return.value := System.Array.IndexOf...System.Object$System.Object.array$System.Object$System.Int32$System.Int32(stack0o, stack1o, stack2i, stack3i);
    // ----- branch
    goto block46563;

  block46563:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true46563to46580, false46563to46512;

  true46563to46580:
    assume local2 == stack0o;
    goto block46580;

  false46563to46512:
    assume local2 != stack0o;
    goto block46512;

  block46580:
    // ----- load token  ----- ArrayList.ssc(307,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(307,7)
    stack0o := TypeObject(Collections.ArrayList);
    // ----- local pack  ----- ArrayList.ssc(307,7)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert TypeObject($typeof($Heap[temp0, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert 0 <= $Heap[temp0, Collections.ArrayList._size];
    assert $Heap[temp0, Collections.ArrayList._size] <= $Length($Heap[temp0, Collections.ArrayList._items]);
    assert (forall ^i: int :: $Heap[temp0, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[temp0, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[temp0, Collections.ArrayList._items], $elements], ^i) == null);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Collections.ArrayList ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block46529;

  block46512:
    // ----- is instance
    // ----- branch
    goto true46512to46580, false46512to46444;

  true46512to46580:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block46580;

  false46512to46444:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block46444;

  block46444:
    // ----- branch
    goto block46529;

  block46529:
    // ----- nop
    // ----- branch
    goto block46410;

  block46410:
    // ----- nop
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0i := return.value;
    // ----- return
    $result := stack0i;
    return;
}



procedure Collections.ArrayList.Insert$System.Int32$System.Object(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], index$in: int where InRange(index$in, System.Int32), value$in: ref where $Is(value$in, System.Object) && $Heap[value$in, $allocated]);
  // user-declared preconditions
  requires 0 <= index$in;
  requires index$in <= #Collections.ArrayList.get_Count($Heap, this);
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



implementation Collections.ArrayList.Insert$System.Int32$System.Object(this: ref, index$in: int, value$in: ref)
{
  var index: int where InRange(index, System.Int32), value: ref where $Is(value, System.Object) && $Heap[value, $allocated], temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception) && $Heap[local2, $allocated], stack0i: int, stack1i: int, stack0b: bool, stack0o: ref, local3: int where InRange(local3, System.Int32), temp2: exposeVersionType, stack2o: ref, stack3i: int, stack4i: int, stack0s: struct;

  entry:
    index := index$in;
    value := value$in;
    goto block47821;

  block47821:
    goto block48042;

  block48042:
    // ----- nop
    // ----- FrameGuard processing  ----- ArrayList.ssc(314,15)
    temp0 := this;
    // ----- load token  ----- ArrayList.ssc(314,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(314,15)
    stack1o := TypeObject(Collections.ArrayList);
    // ----- local unpack  ----- ArrayList.ssc(314,15)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: Collections.ArrayList && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block48059;

  block48059:
    // ----- load field  ----- ArrayList.ssc(315,9)
    assert this != null;
    stack0i := $Heap[this, Collections.ArrayList._size];
    // ----- load field  ----- ArrayList.ssc(315,9)
    assert this != null;
    stack1o := $Heap[this, Collections.ArrayList._items];
    // ----- unary operator  ----- ArrayList.ssc(315,9)
    assert stack1o != null;
    stack1i := $Length(stack1o);
    // ----- unary operator  ----- ArrayList.ssc(315,9)
    stack1i := $IntToInt(stack1i, System.UIntPtr, System.Int32);
    // ----- binary operator  ----- ArrayList.ssc(315,9)
    // ----- branch  ----- ArrayList.ssc(315,9)
    goto true48059to48093, false48059to48076;

  true48059to48093:
    assume stack0i != stack1i;
    goto block48093;

  false48059to48076:
    assume stack0i == stack1i;
    goto block48076;

  block48093:
    // ----- load field  ----- ArrayList.ssc(316,9)
    assert this != null;
    stack0i := $Heap[this, Collections.ArrayList._size];
    // ----- binary operator  ----- ArrayList.ssc(316,9)
    // ----- branch  ----- ArrayList.ssc(316,9)
    goto true48093to48127, false48093to48110;

  block48076:
    // ----- load field  ----- ArrayList.ssc(315,37)
    assert this != null;
    stack0i := $Heap[this, Collections.ArrayList._size];
    // ----- load constant 1  ----- ArrayList.ssc(315,37)
    stack1i := 1;
    // ----- binary operator  ----- ArrayList.ssc(315,37)
    stack0i := stack0i + stack1i;
    // ----- call  ----- ArrayList.ssc(315,37)
    assert this != null;
    call Collections.ArrayList.EnsureCapacity$System.Int32(this, stack0i);
    goto block48093;

  true48093to48127:
    assume index >= stack0i;
    goto block48127;

  false48093to48110:
    assume index < stack0i;
    goto block48110;

  block48127:
    // ----- load field  ----- ArrayList.ssc(320,9)
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- copy  ----- ArrayList.ssc(320,9)
    stack1i := index;
    // ----- store element  ----- ArrayList.ssc(320,9)
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    assert value == null || $typeof(value) <: $ElementType($typeof(stack0o));
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]);
    $Heap[stack0o, $elements] := RefArraySet($Heap[stack0o, $elements], stack1i, value);
    assume IsHeap($Heap);
    // ----- load field  ----- ArrayList.ssc(321,9)
    assert this != null;
    local3 := $Heap[this, Collections.ArrayList._size];
    // ----- load constant 1  ----- ArrayList.ssc(321,9)
    stack0i := 1;
    // ----- binary operator  ----- ArrayList.ssc(321,9)
    stack0i := local3 + stack0i;
    // ----- store field  ----- ArrayList.ssc(321,9)
    assert this != null;
    assert $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
    havoc temp2;
    $Heap[this, $exposeVersion] := temp2;
    $Heap[this, Collections.ArrayList._size] := stack0i;
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || TypeObject($typeof($Heap[this, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || 0 <= $Heap[this, Collections.ArrayList._size];
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || $Heap[this, Collections.ArrayList._size] <= $Length($Heap[this, Collections.ArrayList._items]);
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || (forall ^i: int :: $Heap[this, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[this, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], ^i) == null);
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local3;
    // ----- branch
    goto block48229;

  block48110:
    // ----- load field  ----- ArrayList.ssc(318,11)
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- copy  ----- ArrayList.ssc(318,11)
    stack1i := index;
    // ----- load field  ----- ArrayList.ssc(318,11)
    assert this != null;
    stack2o := $Heap[this, Collections.ArrayList._items];
    // ----- load constant 1  ----- ArrayList.ssc(318,11)
    stack3i := 1;
    // ----- binary operator  ----- ArrayList.ssc(318,11)
    stack3i := index + stack3i;
    // ----- load field  ----- ArrayList.ssc(318,11)
    assert this != null;
    stack4i := $Heap[this, Collections.ArrayList._size];
    // ----- binary operator  ----- ArrayList.ssc(318,11)
    stack4i := stack4i - index;
    // ----- call  ----- ArrayList.ssc(318,11)
    call System.Array.Copy$System.Array$notnull$System.Int32$System.Array$notnull$System.Int32$System.Int32(stack0o, stack1i, stack2o, stack3i, stack4i);
    goto block48127;

  block48229:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true48229to48212, false48229to48297;

  true48229to48212:
    assume local2 == stack0o;
    goto block48212;

  false48229to48297:
    assume local2 != stack0o;
    goto block48297;

  block48212:
    // ----- load token  ----- ArrayList.ssc(322,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(322,7)
    stack0o := TypeObject(Collections.ArrayList);
    // ----- local pack  ----- ArrayList.ssc(322,7)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert TypeObject($typeof($Heap[temp0, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert 0 <= $Heap[temp0, Collections.ArrayList._size];
    assert $Heap[temp0, Collections.ArrayList._size] <= $Length($Heap[temp0, Collections.ArrayList._items]);
    assert (forall ^i: int :: $Heap[temp0, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[temp0, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[temp0, Collections.ArrayList._items], $elements], ^i) == null);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Collections.ArrayList ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block48331;

  block48297:
    // ----- is instance
    // ----- branch
    goto true48297to48212, false48297to48280;

  true48297to48212:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block48212;

  false48297to48280:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block48280;

  block48280:
    // ----- branch
    goto block48331;

  block48331:
    // ----- nop
    // ----- branch
    goto block48178;

  block48178:
    // ----- return
    return;
}



procedure Collections.ArrayList.InsertRange$System.Int32$System.Collections.ICollection$notnull(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], index$in: int where InRange(index$in, System.Int32), c$in: ref where $IsNotNull(c$in, System.Collections.ICollection) && $Heap[c$in, $allocated]);
  // user-declared preconditions
  requires 0 <= index$in;
  requires index$in <= #Collections.ArrayList.get_Count($Heap, this);
  requires !($Heap[this, $ownerRef] == $Heap[c$in, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[c$in, $ownerFrame]);
  // target object is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // target object is peer consistent (owner must not be valid)
  requires $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
  // c is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[c$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[c$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // c is peer consistent (owner must not be valid)
  requires $Heap[c$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[c$in, $ownerRef], $inv] <: $Heap[c$in, $ownerFrame]) || $Heap[$Heap[c$in, $ownerRef], $localinv] == $BaseClass($Heap[c$in, $ownerFrame]);
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(($o != c$in || !($typeof(c$in) <: DeclType($f)) || !$IncludedInModifiesStar($f)) && ($o != this || !($typeof(this) <: DeclType($f)) || !$IncludedInModifiesStar($f))) && old($o != c$in || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Collections.ArrayList.InsertRange$System.Int32$System.Collections.ICollection$notnull(this: ref, index$in: int, c$in: ref)
{
  var index: int where InRange(index, System.Int32), c: ref where $IsNotNull(c, System.Collections.ICollection) && $Heap[c, $allocated], temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception) && $Heap[local2, $allocated], stack0i: int, stack0o: ref, stack0b: bool, stack0s: struct;

  entry:
    index := index$in;
    c := c$in;
    goto block49878;

  block49878:
    goto block50201;

  block50201:
    // ----- nop
    // ----- FrameGuard processing  ----- ArrayList.ssc(331,15)
    temp0 := this;
    // ----- load token  ----- ArrayList.ssc(331,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(331,15)
    stack1o := TypeObject(Collections.ArrayList);
    // ----- local unpack  ----- ArrayList.ssc(331,15)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: Collections.ArrayList && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block50218;

  block50218:
    // ----- copy  ----- ArrayList.ssc(332,9)
    stack0i := index;
    // ----- copy  ----- ArrayList.ssc(332,9)
    stack1o := c;
    // ----- call  ----- ArrayList.ssc(332,9)
    assert this != null;
    call Collections.ArrayList.InsertRangeWorker$System.Int32$System.Collections.ICollection$notnull(this, stack0i, stack1o);
    // ----- branch
    goto block50303;

  block50303:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true50303to50422, false50303to50354;

  true50303to50422:
    assume local2 == stack0o;
    goto block50422;

  false50303to50354:
    assume local2 != stack0o;
    goto block50354;

  block50422:
    // ----- load token  ----- ArrayList.ssc(333,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(333,7)
    stack0o := TypeObject(Collections.ArrayList);
    // ----- local pack  ----- ArrayList.ssc(333,7)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert TypeObject($typeof($Heap[temp0, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert 0 <= $Heap[temp0, Collections.ArrayList._size];
    assert $Heap[temp0, Collections.ArrayList._size] <= $Length($Heap[temp0, Collections.ArrayList._items]);
    assert (forall ^i: int :: $Heap[temp0, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[temp0, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[temp0, Collections.ArrayList._items], $elements], ^i) == null);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Collections.ArrayList ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block50388;

  block50354:
    // ----- is instance
    // ----- branch
    goto true50354to50422, false50354to50337;

  true50354to50422:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block50422;

  false50354to50337:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block50337;

  block50337:
    // ----- branch
    goto block50388;

  block50388:
    // ----- nop
    // ----- branch
    goto block50269;

  block50269:
    // ----- return
    return;
}



implementation Collections.ArrayList.InsertRangeWorker$System.Int32$System.Collections.ICollection$notnull(this: ref, index$in: int, c$in: ref)
{
  var index: int where InRange(index, System.Int32), c: ref where $IsNotNull(c, System.Collections.ICollection) && $Heap[c, $allocated], count: int where InRange(count, System.Int32), stack0i: int, stack0b: bool, stack0o: ref, stack1i: int, stack2o: ref, stack3i: int, stack4i: int, temp0: exposeVersionType;

  entry:
    index := index$in;
    c := c$in;
    goto block52054;

  block52054:
    goto block52428;

  block52428:
    // ----- nop
    // ----- call  ----- ArrayList.ssc(347,11)
    assert c != null;
    call count := System.Collections.ICollection.get_Count$.Virtual.$(c, false);
    // ----- load constant 0  ----- ArrayList.ssc(348,7)
    stack0i := 0;
    // ----- binary operator  ----- ArrayList.ssc(348,7)
    // ----- branch  ----- ArrayList.ssc(348,7)
    goto true52428to52139, false52428to52768;

  true52428to52139:
    assume count <= stack0i;
    goto block52139;

  false52428to52768:
    assume count > stack0i;
    goto block52768;

  block52139:
    goto block52530;

  block52768:
    // ----- load field  ----- ArrayList.ssc(350,9)
    assert this != null;
    stack0i := $Heap[this, Collections.ArrayList._size];
    // ----- binary operator  ----- ArrayList.ssc(350,9)
    stack0i := stack0i + count;
    // ----- call  ----- ArrayList.ssc(350,9)
    assert this != null;
    call Collections.ArrayList.EnsureCapacity$System.Int32(this, stack0i);
    // ----- load field  ----- ArrayList.ssc(351,9)
    assert this != null;
    stack0i := $Heap[this, Collections.ArrayList._size];
    // ----- binary operator  ----- ArrayList.ssc(351,9)
    // ----- branch  ----- ArrayList.ssc(351,9)
    goto true52768to53006, false52768to52207;

  true52768to53006:
    assume index >= stack0i;
    goto block53006;

  false52768to52207:
    assume index < stack0i;
    goto block52207;

  block53006:
    // ----- call  ----- ArrayList.ssc(355,9)
    assert c != null;
    call stack0i := System.Collections.ICollection.get_Count$.Virtual.$(c, false);
    // ----- binary operator  ----- ArrayList.ssc(355,9)
    // ----- branch  ----- ArrayList.ssc(355,9)
    goto true53006to52734, false53006to53074;

  block52207:
    // ----- load field  ----- ArrayList.ssc(353,11)
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- copy  ----- ArrayList.ssc(353,11)
    stack1i := index;
    // ----- load field  ----- ArrayList.ssc(353,11)
    assert this != null;
    stack2o := $Heap[this, Collections.ArrayList._items];
    // ----- binary operator  ----- ArrayList.ssc(353,11)
    stack3i := index + count;
    // ----- load field  ----- ArrayList.ssc(353,11)
    assert this != null;
    stack4i := $Heap[this, Collections.ArrayList._size];
    // ----- binary operator  ----- ArrayList.ssc(353,11)
    stack4i := stack4i - index;
    // ----- call  ----- ArrayList.ssc(353,11)
    call System.Array.Copy$System.Array$notnull$System.Int32$System.Array$notnull$System.Int32$System.Int32(stack0o, stack1i, stack2o, stack3i, stack4i);
    goto block53006;

  block52530:
    // ----- nop
    // ----- return
    return;

  true53006to52734:
    assume index >= stack0i;
    goto block52734;

  false53006to53074:
    assume index < stack0i;
    goto block53074;

  block52734:
    // ----- load field  ----- ArrayList.ssc(358,9)
    assert this != null;
    stack0i := $Heap[this, Collections.ArrayList._size];
    // ----- binary operator  ----- ArrayList.ssc(358,9)
    stack0i := stack0i + count;
    // ----- store field  ----- ArrayList.ssc(358,9)
    assert this != null;
    assert $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
    havoc temp0;
    $Heap[this, $exposeVersion] := temp0;
    $Heap[this, Collections.ArrayList._size] := stack0i;
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || TypeObject($typeof($Heap[this, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || 0 <= $Heap[this, Collections.ArrayList._size];
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || $Heap[this, Collections.ArrayList._size] <= $Length($Heap[this, Collections.ArrayList._items]);
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || (forall ^i: int :: $Heap[this, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[this, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], ^i) == null);
    assume IsHeap($Heap);
    goto block52530;

  block53074:
    // ----- load field  ----- ArrayList.ssc(356,11)
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- copy  ----- ArrayList.ssc(356,11)
    stack1i := index;
    // ----- call  ----- ArrayList.ssc(356,11)
    assert c != null;
    call System.Collections.ICollection.CopyTo$System.Array$notnull$System.Int32$.Virtual.$(c, stack0o, stack1i);
    goto block52734;
}



procedure System.Collections.ICollection.CopyTo$System.Array$notnull$System.Int32$.Virtual.$(this: ref where $IsNotNull(this, System.Collections.ICollection) && $Heap[this, $allocated], array$in: ref where $IsNotNull(array$in, System.Array) && $Heap[array$in, $allocated], index$in: int where InRange(index$in, System.Int32));
  // user-declared preconditions
  requires array$in != null;
  requires $Rank(array$in) == 1;
  requires index$in >= 0;
  requires index$in < #System.Collections.ICollection.get_Count($Heap, this);
  // target object is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // target object is peer consistent (owner must not be valid)
  requires $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
  // array is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[array$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[array$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // array is peer consistent (owner must not be valid)
  requires $Heap[array$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[array$in, $ownerRef], $inv] <: $Heap[array$in, $ownerFrame]) || $Heap[$Heap[array$in, $ownerRef], $localinv] == $BaseClass($Heap[array$in, $ownerFrame]);
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



procedure Collections.ArrayList.LastIndexOf$System.Object(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], value$in: ref where $Is(value$in, System.Object) && $Heap[value$in, $allocated]) returns ($result: int where InRange($result, System.Int32));
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
  // user-declared postconditions
  ensures -1 <= $result;
  ensures $result < #Collections.ArrayList.get_Count($Heap, this);
  ensures ($result == -1 && !(exists ^i: int :: 0 <= ^i && ^i <= #Collections.ArrayList.get_Count($Heap, this) - 1 && #Collections.ArrayList.get_Item$System.Int32($Heap, this, ^i) == value$in)) || (0 <= $result && $result < #Collections.ArrayList.get_Count($Heap, this) && #Collections.ArrayList.get_Item$System.Int32($Heap, this, $result) == value$in);
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



implementation Collections.ArrayList.LastIndexOf$System.Object(this: ref, value$in: ref) returns ($result: int)
{
  var value: ref where $Is(value, System.Object) && $Heap[value, $allocated], stack0i: int, stack1i: int, stack0b: bool, return.value: int where InRange(return.value, System.Int32), stack0o: ref, stack2i: int, SS$Display.Return.Local: int where InRange(SS$Display.Return.Local, System.Int32);

  entry:
    value := value$in;
    goto block54434;

  block54434:
    goto block54944;

  block54944:
    // ----- nop
    // ----- load field  ----- ArrayList.ssc(370,7)
    assert this != null;
    stack0i := $Heap[this, Collections.ArrayList._size];
    // ----- load constant 0  ----- ArrayList.ssc(370,7)
    stack1i := 0;
    // ----- binary operator  ----- ArrayList.ssc(370,7)
    // ----- branch  ----- ArrayList.ssc(370,7)
    goto true54944to54757, false54944to54519;

  true54944to54757:
    assume stack0i != stack1i;
    goto block54757;

  false54944to54519:
    assume stack0i == stack1i;
    goto block54519;

  block54757:
    // ----- copy  ----- ArrayList.ssc(372,7)
    stack0o := value;
    // ----- load field  ----- ArrayList.ssc(372,7)
    assert this != null;
    stack1i := $Heap[this, Collections.ArrayList._size];
    // ----- load constant 1  ----- ArrayList.ssc(372,7)
    stack2i := 1;
    // ----- binary operator  ----- ArrayList.ssc(372,7)
    stack1i := stack1i - stack2i;
    // ----- load field  ----- ArrayList.ssc(372,7)
    assert this != null;
    stack2i := $Heap[this, Collections.ArrayList._size];
    // ----- call  ----- ArrayList.ssc(372,7)
    assert this != null;
    call return.value := Collections.ArrayList.LastIndexOf$System.Object$System.Int32$System.Int32$.Virtual.$(this, stack0o, stack1i, stack2i);
    // ----- branch
    goto block54553;

  block54519:
    // ----- load constant -1  ----- ArrayList.ssc(371,9)
    return.value := -1;
    // ----- branch
    goto block54553;

  block54553:
    // ----- nop
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0i := return.value;
    // ----- return
    $result := stack0i;
    return;
}



procedure Collections.ArrayList.LastIndexOf$System.Object$System.Int32$System.Int32$.Virtual.$(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], value$in: ref where $Is(value$in, System.Object) && $Heap[value$in, $allocated], startIndex$in: int where InRange(startIndex$in, System.Int32), count$in: int where InRange(count$in, System.Int32)) returns ($result: int where InRange($result, System.Int32));
  // user-declared preconditions
  requires 0 <= count$in;
  requires 0 <= startIndex$in;
  requires startIndex$in < #Collections.ArrayList.get_Count($Heap, this);
  requires 0 <= startIndex$in + 1 - count$in;
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
  // user-declared postconditions
  ensures -1 == $result || (startIndex$in + 1 - count$in <= $result && $result <= startIndex$in);
  ensures ($result == -1 && !(exists ^i: int :: 0 <= ^i && ^i <= #Collections.ArrayList.get_Count($Heap, this) - 1 && #Collections.ArrayList.get_Item$System.Int32($Heap, this, ^i) == value$in)) || (0 <= $result && $result < #Collections.ArrayList.get_Count($Heap, this) && #Collections.ArrayList.get_Item$System.Int32($Heap, this, $result) == value$in);
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



procedure Collections.ArrayList.LastIndexOf$System.Object$System.Int32(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], value$in: ref where $Is(value$in, System.Object) && $Heap[value$in, $allocated], startIndex$in: int where InRange(startIndex$in, System.Int32)) returns ($result: int where InRange($result, System.Int32));
  // user-declared preconditions
  requires 0 <= startIndex$in;
  requires startIndex$in < #Collections.ArrayList.get_Count($Heap, this);
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
  // user-declared postconditions
  ensures -1 <= $result;
  ensures $result <= startIndex$in;
  ensures ($result == -1 && !(exists ^i: int :: 0 <= ^i && ^i <= #Collections.ArrayList.get_Count($Heap, this) - 1 && #Collections.ArrayList.get_Item$System.Int32($Heap, this, ^i) == value$in)) || (0 <= $result && $result < #Collections.ArrayList.get_Count($Heap, this) && #Collections.ArrayList.get_Item$System.Int32($Heap, this, $result) == value$in);
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



implementation Collections.ArrayList.LastIndexOf$System.Object$System.Int32(this: ref, value$in: ref, startIndex$in: int) returns ($result: int)
{
  var value: ref where $Is(value, System.Object) && $Heap[value, $allocated], startIndex: int where InRange(startIndex, System.Int32), stack0o: ref, stack1i: int, stack2i: int, return.value: int where InRange(return.value, System.Int32), SS$Display.Return.Local: int where InRange(SS$Display.Return.Local, System.Int32), stack0i: int;

  entry:
    value := value$in;
    startIndex := startIndex$in;
    goto block56219;

  block56219:
    goto block56848;

  block56848:
    // ----- nop
    // ----- copy  ----- ArrayList.ssc(384,7)
    stack0o := value;
    // ----- copy  ----- ArrayList.ssc(384,7)
    stack1i := startIndex;
    // ----- load constant 1  ----- ArrayList.ssc(384,7)
    stack2i := 1;
    // ----- binary operator  ----- ArrayList.ssc(384,7)
    stack2i := startIndex + stack2i;
    // ----- call  ----- ArrayList.ssc(384,7)
    assert this != null;
    call return.value := Collections.ArrayList.LastIndexOf$System.Object$System.Int32$System.Int32$.Virtual.$(this, stack0o, stack1i, stack2i);
    // ----- branch
    goto block56899;

  block56899:
    // ----- nop
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0i := return.value;
    // ----- return
    $result := stack0i;
    return;
}



procedure Collections.ArrayList.LastIndexOf$System.Object$System.Int32$System.Int32(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], value$in: ref where $Is(value$in, System.Object) && $Heap[value$in, $allocated], startIndex$in: int where InRange(startIndex$in, System.Int32), count$in: int where InRange(count$in, System.Int32)) returns ($result: int where InRange($result, System.Int32));
  // user-declared preconditions
  requires 0 <= count$in;
  requires 0 <= startIndex$in;
  requires startIndex$in < #Collections.ArrayList.get_Count($Heap, this);
  requires 0 <= startIndex$in + 1 - count$in;
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
  // user-declared postconditions
  ensures -1 == $result || (startIndex$in + 1 - count$in <= $result && $result <= startIndex$in);
  ensures ($result == -1 && !(exists ^i: int :: 0 <= ^i && ^i <= #Collections.ArrayList.get_Count($Heap, this) - 1 && #Collections.ArrayList.get_Item$System.Int32($Heap, this, ^i) == value$in)) || (0 <= $result && $result < #Collections.ArrayList.get_Count($Heap, this) && #Collections.ArrayList.get_Item$System.Int32($Heap, this, $result) == value$in);
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



implementation Collections.ArrayList.LastIndexOf$System.Object$System.Int32$System.Int32(this: ref, value$in: ref, startIndex$in: int, count$in: int) returns ($result: int)
{
  var value: ref where $Is(value, System.Object) && $Heap[value, $allocated], startIndex: int where InRange(startIndex, System.Int32), count: int where InRange(count, System.Int32), temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception) && $Heap[local2, $allocated], stack0o: ref, stack2i: int, stack3i: int, n: int where InRange(n, System.Int32), return.value: int where InRange(return.value, System.Int32), stack0b: bool, stack0s: struct, SS$Display.Return.Local: int where InRange(SS$Display.Return.Local, System.Int32), stack0i: int;

  entry:
    value := value$in;
    startIndex := startIndex$in;
    count := count$in;
    goto block58854;

  block58854:
    goto block59177;

  block59177:
    // ----- nop
    // ----- FrameGuard processing  ----- ArrayList.ssc(398,15)
    temp0 := this;
    // ----- load token  ----- ArrayList.ssc(398,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(398,15)
    stack1o := TypeObject(Collections.ArrayList);
    // ----- local unpack  ----- ArrayList.ssc(398,15)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: Collections.ArrayList && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block59194;

  block59194:
    // ----- load field  ----- ArrayList.ssc(399,13)
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- copy  ----- ArrayList.ssc(399,13)
    stack1o := value;
    // ----- copy  ----- ArrayList.ssc(399,13)
    stack2i := startIndex;
    // ----- copy  ----- ArrayList.ssc(399,13)
    stack3i := count;
    // ----- call  ----- ArrayList.ssc(399,13)
    call n := System.Array.LastIndexOf...System.Object$System.Object.array$System.Object$System.Int32$System.Int32(stack0o, stack1o, stack2i, stack3i);
    // ----- serialized AssumeStatement  ----- ArrayList.ssc(400,9)
    assume (n == -1 && !(exists ^i: int :: 0 <= ^i && ^i <= #Collections.ArrayList.get_Count($Heap, this) - 1 && #Collections.ArrayList.get_Item$System.Int32($Heap, this, ^i) == value)) || (0 <= n && n < #Collections.ArrayList.get_Count($Heap, this) && #Collections.ArrayList.get_Item$System.Int32($Heap, this, n) == value);
    goto block59568;

  block59568:
    // ----- nop
    // ----- copy  ----- ArrayList.ssc(402,9)
    return.value := n;
    // ----- branch
    goto block60248;

  block60248:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true60248to60197, false60248to60265;

  true60248to60197:
    assume local2 == stack0o;
    goto block60197;

  false60248to60265:
    assume local2 != stack0o;
    goto block60265;

  block60197:
    // ----- load token  ----- ArrayList.ssc(403,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(403,7)
    stack0o := TypeObject(Collections.ArrayList);
    // ----- local pack  ----- ArrayList.ssc(403,7)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert TypeObject($typeof($Heap[temp0, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert 0 <= $Heap[temp0, Collections.ArrayList._size];
    assert $Heap[temp0, Collections.ArrayList._size] <= $Length($Heap[temp0, Collections.ArrayList._items]);
    assert (forall ^i: int :: $Heap[temp0, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[temp0, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[temp0, Collections.ArrayList._items], $elements], ^i) == null);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Collections.ArrayList ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block60214;

  block60265:
    // ----- is instance
    // ----- branch
    goto true60265to60197, false60265to60231;

  true60265to60197:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block60197;

  false60265to60231:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block60231;

  block60231:
    // ----- branch
    goto block60214;

  block60214:
    // ----- nop
    // ----- branch
    goto block60146;

  block60146:
    // ----- nop
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0i := return.value;
    // ----- return
    $result := stack0i;
    return;
}



procedure System.Array.LastIndexOf...System.Object$System.Object.array$System.Object$System.Int32$System.Int32(array$in: ref where $Is(array$in, RefArray(System.Object, 1)) && $Heap[array$in, $allocated], value$in: ref where $Is(value$in, System.Object) && $Heap[value$in, $allocated], startIndex$in: int where InRange(startIndex$in, System.Int32), count$in: int where InRange(count$in, System.Int32)) returns ($result: int where InRange($result, System.Int32));
  // array is peer consistent
  requires array$in == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[array$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[array$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // array is peer consistent (owner must not be valid)
  requires array$in == null || $Heap[array$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[array$in, $ownerRef], $inv] <: $Heap[array$in, $ownerFrame]) || $Heap[$Heap[array$in, $ownerRef], $localinv] == $BaseClass($Heap[array$in, $ownerFrame]);
  // value is a peer of the expected elements of the generic object
  requires true;
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



procedure Collections.ArrayList.Remove$System.Object(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], obj$in: ref where $Is(obj$in, System.Object) && $Heap[obj$in, $allocated]);
  // target object is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // target object is peer consistent (owner must not be valid)
  requires $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
  // obj is peer consistent
  requires obj$in == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[obj$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[obj$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // obj is peer consistent (owner must not be valid)
  requires obj$in == null || $Heap[obj$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[obj$in, $ownerRef], $inv] <: $Heap[obj$in, $ownerFrame]) || $Heap[$Heap[obj$in, $ownerRef], $localinv] == $BaseClass($Heap[obj$in, $ownerFrame]);
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



implementation Collections.ArrayList.Remove$System.Object(this: ref, obj$in: ref)
{
  var obj: ref where $Is(obj, System.Object) && $Heap[obj, $allocated], stack0o: ref, index: int where InRange(index, System.Int32), stack0i: int, stack0b: bool;

  entry:
    obj := obj$in;
    goto block61353;

  block61353:
    goto block61421;

  block61421:
    // ----- nop
    // ----- copy  ----- ArrayList.ssc(409,11)
    stack0o := obj;
    // ----- call  ----- ArrayList.ssc(409,11)
    assert this != null;
    call index := Collections.ArrayList.IndexOf$System.Object$.Virtual.$(this, stack0o);
    // ----- load constant 0  ----- ArrayList.ssc(410,7)
    stack0i := 0;
    // ----- binary operator  ----- ArrayList.ssc(410,7)
    // ----- branch  ----- ArrayList.ssc(410,7)
    goto true61421to61455, false61421to61489;

  true61421to61455:
    assume stack0i > index;
    goto block61455;

  false61421to61489:
    assume stack0i <= index;
    goto block61489;

  block61455:
    // ----- return
    return;

  block61489:
    // ----- copy  ----- ArrayList.ssc(411,9)
    stack0i := index;
    // ----- call  ----- ArrayList.ssc(411,9)
    assert this != null;
    call Collections.ArrayList.RemoveAt$System.Int32$.Virtual.$(this, stack0i);
    goto block61455;
}



procedure Collections.ArrayList.IndexOf$System.Object$.Virtual.$(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], value$in: ref where $Is(value$in, System.Object) && $Heap[value$in, $allocated]) returns ($result: int where InRange($result, System.Int32));
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
  // user-declared postconditions
  ensures -1 <= $result;
  ensures $result < #Collections.ArrayList.get_Count($Heap, this);
  ensures ($result == -1 && !(exists ^i: int :: 0 <= ^i && ^i <= #Collections.ArrayList.get_Count($Heap, this) - 1 && #Collections.ArrayList.get_Item$System.Int32($Heap, this, ^i) == value$in)) || (0 <= $result && $result < #Collections.ArrayList.get_Count($Heap, this) && #Collections.ArrayList.get_Item$System.Int32($Heap, this, $result) == value$in);
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



procedure Collections.ArrayList.RemoveAt$System.Int32$.Virtual.$(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], index$in: int where InRange(index$in, System.Int32));
  // user-declared preconditions
  requires 0 <= index$in;
  requires index$in < #Collections.ArrayList.get_Count($Heap, this);
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



procedure Collections.ArrayList.RemoveAt$System.Int32(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], index$in: int where InRange(index$in, System.Int32));
  // user-declared preconditions
  requires 0 <= index$in;
  requires index$in < #Collections.ArrayList.get_Count($Heap, this);
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



implementation Collections.ArrayList.RemoveAt$System.Int32(this: ref, index$in: int)
{
  var index: int where InRange(index, System.Int32), temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception) && $Heap[local2, $allocated], local3: int where InRange(local3, System.Int32), stack0i: int, temp2: exposeVersionType, stack0b: bool, stack0o: ref, stack1i: int, stack2o: ref, stack3i: int, stack4i: int, stack0s: struct;

  entry:
    index := index$in;
    goto block62220;

  block62220:
    goto block62441;

  block62441:
    // ----- nop
    // ----- FrameGuard processing  ----- ArrayList.ssc(418,15)
    temp0 := this;
    // ----- load token  ----- ArrayList.ssc(418,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(418,15)
    stack1o := TypeObject(Collections.ArrayList);
    // ----- local unpack  ----- ArrayList.ssc(418,15)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: Collections.ArrayList && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block62458;

  block62458:
    // ----- load field  ----- ArrayList.ssc(419,9)
    assert this != null;
    local3 := $Heap[this, Collections.ArrayList._size];
    // ----- load constant 1  ----- ArrayList.ssc(419,9)
    stack0i := 1;
    // ----- binary operator  ----- ArrayList.ssc(419,9)
    stack0i := local3 - stack0i;
    // ----- store field  ----- ArrayList.ssc(419,9)
    assert this != null;
    assert $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
    havoc temp2;
    $Heap[this, $exposeVersion] := temp2;
    $Heap[this, Collections.ArrayList._size] := stack0i;
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || TypeObject($typeof($Heap[this, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || 0 <= $Heap[this, Collections.ArrayList._size];
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || $Heap[this, Collections.ArrayList._size] <= $Length($Heap[this, Collections.ArrayList._items]);
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || (forall ^i: int :: $Heap[this, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[this, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], ^i) == null);
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local3;
    // ----- load field  ----- ArrayList.ssc(420,9)
    assert this != null;
    stack0i := $Heap[this, Collections.ArrayList._size];
    // ----- binary operator  ----- ArrayList.ssc(420,9)
    // ----- branch  ----- ArrayList.ssc(420,9)
    goto true62458to62492, false62458to62475;

  true62458to62492:
    assume index >= stack0i;
    goto block62492;

  false62458to62475:
    assume index < stack0i;
    goto block62475;

  block62492:
    // ----- load field  ----- ArrayList.ssc(424,9)
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- load field  ----- ArrayList.ssc(424,9)
    assert this != null;
    stack1i := $Heap[this, Collections.ArrayList._size];
    stack2o := null;
    // ----- store element  ----- ArrayList.ssc(424,9)
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    assert stack2o == null || $typeof(stack2o) <: $ElementType($typeof(stack0o));
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]);
    $Heap[stack0o, $elements] := RefArraySet($Heap[stack0o, $elements], stack1i, stack2o);
    assume IsHeap($Heap);
    // ----- branch
    goto block62628;

  block62475:
    // ----- load field  ----- ArrayList.ssc(422,11)
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- load constant 1  ----- ArrayList.ssc(422,11)
    stack1i := 1;
    // ----- binary operator  ----- ArrayList.ssc(422,11)
    stack1i := index + stack1i;
    // ----- load field  ----- ArrayList.ssc(422,11)
    assert this != null;
    stack2o := $Heap[this, Collections.ArrayList._items];
    // ----- copy  ----- ArrayList.ssc(422,11)
    stack3i := index;
    // ----- load field  ----- ArrayList.ssc(422,11)
    assert this != null;
    stack4i := $Heap[this, Collections.ArrayList._size];
    // ----- binary operator  ----- ArrayList.ssc(422,11)
    stack4i := stack4i - index;
    // ----- call  ----- ArrayList.ssc(422,11)
    call System.Array.Copy$System.Array$notnull$System.Int32$System.Array$notnull$System.Int32$System.Int32(stack0o, stack1i, stack2o, stack3i, stack4i);
    goto block62492;

  block62628:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true62628to62662, false62628to62611;

  true62628to62662:
    assume local2 == stack0o;
    goto block62662;

  false62628to62611:
    assume local2 != stack0o;
    goto block62611;

  block62662:
    // ----- load token  ----- ArrayList.ssc(425,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(425,7)
    stack0o := TypeObject(Collections.ArrayList);
    // ----- local pack  ----- ArrayList.ssc(425,7)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert TypeObject($typeof($Heap[temp0, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert 0 <= $Heap[temp0, Collections.ArrayList._size];
    assert $Heap[temp0, Collections.ArrayList._size] <= $Length($Heap[temp0, Collections.ArrayList._items]);
    assert (forall ^i: int :: $Heap[temp0, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[temp0, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[temp0, Collections.ArrayList._items], $elements], ^i) == null);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Collections.ArrayList ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block62679;

  block62611:
    // ----- is instance
    // ----- branch
    goto true62611to62662, false62611to62577;

  true62611to62662:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block62662;

  false62611to62577:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block62577;

  block62577:
    // ----- branch
    goto block62679;

  block62679:
    // ----- nop
    // ----- branch
    goto block62543;

  block62543:
    // ----- return
    return;
}



procedure Collections.ArrayList.RemoveRange$System.Int32$System.Int32(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], index$in: int where InRange(index$in, System.Int32), count$in: int where InRange(count$in, System.Int32));
  // user-declared preconditions
  requires 0 <= index$in;
  requires 0 <= count$in;
  requires index$in + count$in <= #Collections.ArrayList.get_Count($Heap, this);
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



implementation Collections.ArrayList.RemoveRange$System.Int32$System.Int32(this: ref, index$in: int, count$in: int)
{
  var index: int where InRange(index, System.Int32), count: int where InRange(count, System.Int32), temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception) && $Heap[local2, $allocated], stack0i: int, stack0b: bool, i: int where InRange(i, System.Int32), temp2: exposeVersionType, itemsBeforeLoop: ref where $Is(itemsBeforeLoop, RefArray(System.Object, 1)) && $Heap[itemsBeforeLoop, $allocated], stack0o: ref, stack1i: int, stack2o: ref, stack3i: int, stack4i: int, stack0s: struct, local8: int where InRange(local8, System.Int32), $Heap$block64957$LoopPreheader: [ref,<x>name]x;

  entry:
    index := index$in;
    count := count$in;
    goto block64566;

  block64566:
    goto block64872;

  block64872:
    // ----- nop
    // ----- FrameGuard processing  ----- ArrayList.ssc(434,15)
    temp0 := this;
    // ----- load token  ----- ArrayList.ssc(434,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(434,15)
    stack1o := TypeObject(Collections.ArrayList);
    // ----- local unpack  ----- ArrayList.ssc(434,15)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: Collections.ArrayList && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block64889;

  block64889:
    // ----- load constant 0  ----- ArrayList.ssc(435,9)
    stack0i := 0;
    // ----- binary operator  ----- ArrayList.ssc(435,9)
    // ----- branch  ----- ArrayList.ssc(435,9)
    goto true64889to65382, false64889to64906;

  true64889to65382:
    assume count <= stack0i;
    goto block65382;

  false64889to64906:
    assume count > stack0i;
    goto block64906;

  block65382:
    // ----- branch
    goto block65501;

  block64906:
    // ----- load field  ----- ArrayList.ssc(437,15)
    assert this != null;
    i := $Heap[this, Collections.ArrayList._size];
    // ----- load field  ----- ArrayList.ssc(438,11)
    assert this != null;
    stack0i := $Heap[this, Collections.ArrayList._size];
    // ----- binary operator  ----- ArrayList.ssc(438,11)
    stack0i := stack0i - count;
    // ----- store field  ----- ArrayList.ssc(438,11)
    assert this != null;
    assert $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
    havoc temp2;
    $Heap[this, $exposeVersion] := temp2;
    $Heap[this, Collections.ArrayList._size] := stack0i;
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || TypeObject($typeof($Heap[this, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || 0 <= $Heap[this, Collections.ArrayList._size];
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || $Heap[this, Collections.ArrayList._size] <= $Length($Heap[this, Collections.ArrayList._items]);
    assert !($Heap[this, $inv] <: Collections.ArrayList && $Heap[this, $localinv] != $BaseClass(Collections.ArrayList)) || (forall ^i: int :: $Heap[this, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[this, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], ^i) == null);
    assume IsHeap($Heap);
    // ----- load field  ----- ArrayList.ssc(439,11)
    assert this != null;
    stack0i := $Heap[this, Collections.ArrayList._size];
    // ----- binary operator  ----- ArrayList.ssc(439,11)
    // ----- branch  ----- ArrayList.ssc(439,11)
    goto true64906to64940, false64906to64923;

  true64906to64940:
    assume index >= stack0i;
    goto block64940;

  false64906to64923:
    assume index < stack0i;
    goto block64923;

  block64940:
    // ----- load field  ----- ArrayList.ssc(443,20)
    assert this != null;
    itemsBeforeLoop := $Heap[this, Collections.ArrayList._items];
    goto block64957$LoopPreheader;

  block64923:
    // ----- load field  ----- ArrayList.ssc(441,13)
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- binary operator  ----- ArrayList.ssc(441,13)
    stack1i := index + count;
    // ----- load field  ----- ArrayList.ssc(441,13)
    assert this != null;
    stack2o := $Heap[this, Collections.ArrayList._items];
    // ----- copy  ----- ArrayList.ssc(441,13)
    stack3i := index;
    // ----- load field  ----- ArrayList.ssc(441,13)
    assert this != null;
    stack4i := $Heap[this, Collections.ArrayList._size];
    // ----- binary operator  ----- ArrayList.ssc(441,13)
    stack4i := stack4i - index;
    // ----- call  ----- ArrayList.ssc(441,13)
    call System.Array.Copy$System.Array$notnull$System.Int32$System.Array$notnull$System.Int32$System.Int32(stack0o, stack1i, stack2o, stack3i, stack4i);
    goto block64940;

  block65501:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true65501to65586, false65501to65535;

  true65501to65586:
    assume local2 == stack0o;
    goto block65586;

  false65501to65535:
    assume local2 != stack0o;
    goto block65535;

  block65586:
    // ----- load token  ----- ArrayList.ssc(452,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(452,7)
    stack0o := TypeObject(Collections.ArrayList);
    // ----- local pack  ----- ArrayList.ssc(452,7)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert TypeObject($typeof($Heap[temp0, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert 0 <= $Heap[temp0, Collections.ArrayList._size];
    assert $Heap[temp0, Collections.ArrayList._size] <= $Length($Heap[temp0, Collections.ArrayList._items]);
    assert (forall ^i: int :: $Heap[temp0, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[temp0, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[temp0, Collections.ArrayList._items], $elements], ^i) == null);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Collections.ArrayList ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block65552;

  block65535:
    // ----- is instance
    // ----- branch
    goto true65535to65586, false65535to65467;

  block64957:
    // ----- serialized LoopInvariant  ----- ArrayList.ssc(445,23)
    assert 0 <= $Heap[this, Collections.ArrayList._size];
    // ----- serialized LoopInvariant  ----- ArrayList.ssc(445,23)
    assert $Heap[this, Collections.ArrayList._size] <= i;
    // ----- serialized LoopInvariant  ----- ArrayList.ssc(445,23)
    assert i <= $Length($Heap[this, Collections.ArrayList._items]);
    // ----- serialized LoopInvariant  ----- ArrayList.ssc(446,23)
    assert $Heap[this, Collections.ArrayList._items] == itemsBeforeLoop;
    // ----- serialized LoopInvariant  ----- ArrayList.ssc(447,23)
    assert (forall ^j: int :: i <= ^j && ^j <= $Length($Heap[this, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[this, Collections.ArrayList._items], $elements], ^j) == null);
    // ----- default loop invariant: allocation and ownership are stable  ----- ArrayList.ssc(445,23)
    assume (forall $o: ref :: { $Heap[$o, $allocated] } $Heap$block64957$LoopPreheader[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } $Heap$block64957$LoopPreheader[$ot, $allocated] && $Heap$block64957$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block64957$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block64957$LoopPreheader[$ot, $ownerFrame]) && $Heap$block64957$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: exposure  ----- ArrayList.ssc(445,23)
    assume (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $Heap$block64957$LoopPreheader[$o, $allocated] ==> $Heap$block64957$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block64957$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]);
    assume (forall $o: ref :: !$Heap$block64957$LoopPreheader[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: modifies  ----- ArrayList.ssc(445,23)
    assert (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || !($typeof(this) <: DeclType($f)) || !$IncludedInModifiesStar($f)) && old(true) ==> $Heap$block64957$LoopPreheader[$o, $f] == $Heap[$o, $f]);
    assume $HeapSucc($Heap$block64957$LoopPreheader, $Heap);
    // ----- default loop invariant: owner fields  ----- ArrayList.ssc(445,23)
    assert (forall $o: ref :: { $Heap[$o, $ownerFrame] } { $Heap[$o, $ownerRef] } $o != null && $Heap$block64957$LoopPreheader[$o, $allocated] ==> $Heap[$o, $ownerRef] == $Heap$block64957$LoopPreheader[$o, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap$block64957$LoopPreheader[$o, $ownerFrame]);
    // ----- advance activity
    havoc $ActivityIndicator;
    goto block65348;

  true65535to65586:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block65586;

  false65535to65467:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block65467;

  block65467:
    // ----- branch
    goto block65552;

  block65348:
    // ----- nop
    // ----- load field  ----- ArrayList.ssc(444,11)
    assert this != null;
    stack0i := $Heap[this, Collections.ArrayList._size];
    // ----- binary operator  ----- ArrayList.ssc(444,11)
    // ----- branch  ----- ArrayList.ssc(444,11)
    goto true65348to65382, false65348to65365;

  true65348to65382:
    assume stack0i >= i;
    goto block65382;

  false65348to65365:
    assume stack0i < i;
    goto block65365;

  block65365:
    // ----- load field
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- load constant 1  ----- ArrayList.ssc(449,13)
    stack1i := 1;
    // ----- binary operator  ----- ArrayList.ssc(449,13)
    stack1i := i - stack1i;
    // ----- copy  ----- ArrayList.ssc(449,13)
    local8 := stack1i;
    // ----- copy  ----- ArrayList.ssc(449,20)
    i := local8;
    // ----- copy  ----- ArrayList.ssc(449,20)
    stack1i := local8;
    stack2o := null;
    // ----- store element  ----- ArrayList.ssc(449,20)
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    assert stack2o == null || $typeof(stack2o) <: $ElementType($typeof(stack0o));
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]);
    $Heap[stack0o, $elements] := RefArraySet($Heap[stack0o, $elements], stack1i, stack2o);
    assume IsHeap($Heap);
    // ----- branch  ----- ArrayList.ssc(450,12)
    goto block64957;

  block65552:
    // ----- nop
    // ----- branch
    goto block65433;

  block65433:
    // ----- return
    return;

  block64957$LoopPreheader:
    $Heap$block64957$LoopPreheader := $Heap;
    goto block64957;
}



procedure Collections.ArrayList.Repeat$System.Object$System.Int32(value$in: ref where $Is(value$in, System.Object) && $Heap[value$in, $allocated], count$in: int where InRange(count$in, System.Int32)) returns ($result: ref where $IsNotNull($result, Collections.ArrayList) && $Heap[$result, $allocated]);
  // user-declared preconditions
  requires 0 <= count$in;
  // value is peer consistent
  requires value$in == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[value$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[value$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // value is peer consistent (owner must not be valid)
  requires value$in == null || $Heap[value$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[value$in, $ownerRef], $inv] <: $Heap[value$in, $ownerFrame]) || $Heap[$Heap[value$in, $ownerRef], $localinv] == $BaseClass($Heap[value$in, $ownerFrame]);
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



implementation Collections.ArrayList.Repeat$System.Object$System.Int32(value$in: ref, count$in: int) returns ($result: ref)
{
  var value: ref where $Is(value, System.Object) && $Heap[value, $allocated], count: int where InRange(count, System.Int32), local2: int where InRange(local2, System.Int32), stack0b: bool, stack0i: int, stack50000o: ref, stack0o: ref, list: ref where $Is(list, Collections.ArrayList) && $Heap[list, $allocated], i: int where InRange(i, System.Int32), stack1o: ref, return.value: ref where $Is(return.value, Collections.ArrayList) && $Heap[return.value, $allocated], local5: int where InRange(local5, System.Int32), SS$Display.Return.Local: ref where $Is(SS$Display.Return.Local, Collections.ArrayList) && $Heap[SS$Display.Return.Local, $allocated], $Heap$block67405$LoopPreheader: [ref,<x>name]x;

  entry:
    value := value$in;
    count := count$in;
    goto block67337;

  block67337:
    goto block67575;

  block67575:
    // ----- nop
    // ----- load constant -2147483648  ----- ArrayList.ssc(459,17)
    local2 := int#m2147483648;
    // ----- binary operator
    // ----- branch
    goto true67575to67711, false67575to67541;

  true67575to67711:
    assume local2 >= count;
    goto block67711;

  false67575to67541:
    assume local2 < count;
    goto block67541;

  block67711:
    // ----- copy
    stack0i := local2;
    goto block67422;

  block67541:
    // ----- copy
    stack0i := count;
    // ----- branch
    goto block67422;

  block67422:
    // ----- copy
    local2 := stack0i;
    // ----- load constant 16
    stack0i := 16;
    // ----- binary operator
    // ----- branch
    goto true67422to67388, false67422to67507;

  true67422to67388:
    assume local2 >= stack0i;
    goto block67388;

  false67422to67507:
    assume local2 < stack0i;
    goto block67507;

  block67388:
    // ----- copy
    stack0i := local2;
    goto block67660;

  block67507:
    // ----- load constant 16
    stack0i := 16;
    // ----- branch
    goto block67660;

  block67660:
    // ----- copy
    local2 := stack0i;
    // ----- copy  ----- ArrayList.ssc(459,17)
    stack0i := local2;
    // ----- new object  ----- ArrayList.ssc(459,17)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == Collections.ArrayList;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    // ----- call  ----- ArrayList.ssc(459,17)
    assert stack50000o != null;
    call Collections.ArrayList..ctor$System.Int32(stack50000o, stack0i);
    // ----- copy  ----- ArrayList.ssc(459,17)
    stack0o := stack50000o;
    // ----- copy  ----- ArrayList.ssc(459,17)
    list := stack0o;
    // ----- load constant 0  ----- ArrayList.ssc(460,16)
    i := 0;
    goto block67405$LoopPreheader;

  block67405:
    // ----- serialized LoopInvariant  ----- ArrayList.ssc(461,19)
    assert ($Heap[list, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[list, $ownerRef], $inv] <: $Heap[list, $ownerFrame]) || $Heap[$Heap[list, $ownerRef], $localinv] == $BaseClass($Heap[list, $ownerFrame])) && (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[list, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[list, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
    // ----- default loop invariant: allocation and ownership are stable  ----- ArrayList.ssc(461,19)
    assume (forall $o: ref :: { $Heap[$o, $allocated] } $Heap$block67405$LoopPreheader[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } $Heap$block67405$LoopPreheader[$ot, $allocated] && $Heap$block67405$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block67405$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block67405$LoopPreheader[$ot, $ownerFrame]) && $Heap$block67405$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: exposure  ----- ArrayList.ssc(461,19)
    assume (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $Heap$block67405$LoopPreheader[$o, $allocated] ==> $Heap$block67405$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block67405$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]);
    assume (forall $o: ref :: !$Heap$block67405$LoopPreheader[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: modifies  ----- ArrayList.ssc(461,19)
    assert (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old(true) ==> $Heap$block67405$LoopPreheader[$o, $f] == $Heap[$o, $f]);
    assume $HeapSucc($Heap$block67405$LoopPreheader, $Heap);
    // ----- default loop invariant: owner fields  ----- ArrayList.ssc(461,19)
    assert (forall $o: ref :: { $Heap[$o, $ownerFrame] } { $Heap[$o, $ownerRef] } $o != null && $Heap$block67405$LoopPreheader[$o, $allocated] ==> $Heap[$o, $ownerRef] == $Heap$block67405$LoopPreheader[$o, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap$block67405$LoopPreheader[$o, $ownerFrame]);
    // ----- advance activity
    havoc $ActivityIndicator;
    goto block67558;

  block67558:
    // ----- nop
    // ----- binary operator  ----- ArrayList.ssc(460,23)
    // ----- branch  ----- ArrayList.ssc(460,23)
    goto true67558to67694, false67558to67524;

  true67558to67694:
    assume i >= count;
    goto block67694;

  false67558to67524:
    assume i < count;
    goto block67524;

  block67694:
    // ----- copy  ----- ArrayList.ssc(465,7)
    return.value := list;
    // ----- branch
    goto block67456;

  block67524:
    // ----- copy  ----- ArrayList.ssc(463,9)
    stack0o := value;
    // ----- call  ----- ArrayList.ssc(463,9)
    assert list != null;
    call stack0i := Collections.ArrayList.Add$System.Object$.Virtual.$(list, stack0o);
    // ----- copy  ----- ArrayList.ssc(460,34)
    local5 := i;
    // ----- load constant 1  ----- ArrayList.ssc(460,34)
    stack0i := 1;
    // ----- binary operator  ----- ArrayList.ssc(460,34)
    stack0i := local5 + stack0i;
    // ----- copy  ----- ArrayList.ssc(460,34)
    i := stack0i;
    // ----- copy
    stack0i := local5;
    // ----- branch
    goto block67405;

  block67456:
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0o := return.value;
    // ----- return
    $result := stack0o;
    return;

  block67405$LoopPreheader:
    $Heap$block67405$LoopPreheader := $Heap;
    goto block67405;
}



procedure Collections.ArrayList.Add$System.Object$.Virtual.$(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], value$in: ref where $Is(value$in, System.Object) && $Heap[value$in, $allocated]) returns ($result: int where InRange($result, System.Int32));
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
  // user-declared postconditions
  ensures #Collections.ArrayList.get_Count($Heap, this) == old(#Collections.ArrayList.get_Count($Heap, this)) + 1;
  ensures #Collections.ArrayList.get_Item$System.Int32($Heap, this, $result) == value$in;
  ensures $result == old(#Collections.ArrayList.get_Count($Heap, this));
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



procedure Collections.ArrayList.Reverse(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated]);
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



implementation Collections.ArrayList.Reverse(this: ref)
{
  var stack0i: int, stack1i: int;

  entry:
    goto block68629;

  block68629:
    goto block68748;

  block68748:
    // ----- nop
    // ----- load constant 0  ----- ArrayList.ssc(471,7)
    stack0i := 0;
    // ----- call  ----- ArrayList.ssc(471,7)
    assert this != null;
    call stack1i := Collections.ArrayList.get_Count$.Virtual.$(this, false);
    // ----- call  ----- ArrayList.ssc(471,7)
    assert this != null;
    call Collections.ArrayList.Reverse$System.Int32$System.Int32$.Virtual.$(this, stack0i, stack1i);
    // ----- return
    return;
}



procedure Collections.ArrayList.Reverse$System.Int32$System.Int32$.Virtual.$(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], index$in: int where InRange(index$in, System.Int32), count$in: int where InRange(count$in, System.Int32));
  // user-declared preconditions
  requires 0 <= index$in;
  requires 0 <= count$in;
  requires index$in + count$in <= #Collections.ArrayList.get_Count($Heap, this);
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



procedure Collections.ArrayList.Reverse$System.Int32$System.Int32(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], index$in: int where InRange(index$in, System.Int32), count$in: int where InRange(count$in, System.Int32));
  // user-declared preconditions
  requires 0 <= index$in;
  requires 0 <= count$in;
  requires index$in + count$in <= #Collections.ArrayList.get_Count($Heap, this);
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



implementation Collections.ArrayList.Reverse$System.Int32$System.Int32(this: ref, index$in: int, count$in: int)
{
  var index: int where InRange(index, System.Int32), count: int where InRange(count, System.Int32), temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception) && $Heap[local2, $allocated], stack0o: ref, stack1i: int, stack2i: int, stack0b: bool, stack0s: struct;

  entry:
    index := index$in;
    count := count$in;
    goto block69445;

  block69445:
    goto block69751;

  block69751:
    // ----- nop
    // ----- FrameGuard processing  ----- ArrayList.ssc(480,15)
    temp0 := this;
    // ----- load token  ----- ArrayList.ssc(480,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(480,15)
    stack1o := TypeObject(Collections.ArrayList);
    // ----- local unpack  ----- ArrayList.ssc(480,15)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: Collections.ArrayList && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block69768;

  block69768:
    // ----- load field  ----- ArrayList.ssc(481,9)
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- copy  ----- ArrayList.ssc(481,9)
    stack1i := index;
    // ----- copy  ----- ArrayList.ssc(481,9)
    stack2i := count;
    // ----- call  ----- ArrayList.ssc(481,9)
    call System.Array.Reverse$System.Array$notnull$System.Int32$System.Int32(stack0o, stack1i, stack2i);
    // ----- branch
    goto block69853;

  block69853:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true69853to69870, false69853to69938;

  true69853to69870:
    assume local2 == stack0o;
    goto block69870;

  false69853to69938:
    assume local2 != stack0o;
    goto block69938;

  block69870:
    // ----- load token  ----- ArrayList.ssc(482,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(482,7)
    stack0o := TypeObject(Collections.ArrayList);
    // ----- local pack  ----- ArrayList.ssc(482,7)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert TypeObject($typeof($Heap[temp0, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert 0 <= $Heap[temp0, Collections.ArrayList._size];
    assert $Heap[temp0, Collections.ArrayList._size] <= $Length($Heap[temp0, Collections.ArrayList._items]);
    assert (forall ^i: int :: $Heap[temp0, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[temp0, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[temp0, Collections.ArrayList._items], $elements], ^i) == null);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Collections.ArrayList ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block69921;

  block69938:
    // ----- is instance
    // ----- branch
    goto true69938to69870, false69938to69972;

  true69938to69870:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block69870;

  false69938to69972:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block69972;

  block69972:
    // ----- branch
    goto block69921;

  block69921:
    // ----- nop
    // ----- branch
    goto block69819;

  block69819:
    // ----- return
    return;
}



procedure System.Array.Reverse$System.Array$notnull$System.Int32$System.Int32(array$in: ref where $IsNotNull(array$in, System.Array) && $Heap[array$in, $allocated], index$in: int where InRange(index$in, System.Int32), length$in: int where InRange(length$in, System.Int32));
  // user-declared preconditions
  requires array$in != null;
  requires $Rank(array$in) == 1;
  requires length$in >= 0;
  requires index$in >= $LBound(array$in, 0);
  requires $LBound(array$in, 0) + index$in + length$in <= $Length(array$in);
  // array is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[array$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[array$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // array is peer consistent (owner must not be valid)
  requires $Heap[array$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[array$in, $ownerRef], $inv] <: $Heap[array$in, $ownerFrame]) || $Heap[$Heap[array$in, $ownerRef], $localinv] == $BaseClass($Heap[array$in, $ownerFrame]);
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



procedure Collections.ArrayList.Sort(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated]);
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



implementation Collections.ArrayList.Sort(this: ref)
{
  var stack0o: ref, stack0i: int, stack1i: int, stack2o: ref;

  entry:
    goto block70805;

  block70805:
    goto block71043;

  block71043:
    // ----- nop
    // ----- serialized AssumeStatement  ----- ArrayList.ssc(488,7)
    assume ($Heap[$Heap[ClassRepr(System.Collections.Comparer), System.Collections.Comparer.Default], $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[$Heap[ClassRepr(System.Collections.Comparer), System.Collections.Comparer.Default], $ownerRef], $inv] <: $Heap[$Heap[ClassRepr(System.Collections.Comparer), System.Collections.Comparer.Default], $ownerFrame]) || $Heap[$Heap[$Heap[ClassRepr(System.Collections.Comparer), System.Collections.Comparer.Default], $ownerRef], $localinv] == $BaseClass($Heap[$Heap[ClassRepr(System.Collections.Comparer), System.Collections.Comparer.Default], $ownerFrame])) && (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[$Heap[ClassRepr(System.Collections.Comparer), System.Collections.Comparer.Default], $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[$Heap[ClassRepr(System.Collections.Comparer), System.Collections.Comparer.Default], $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
    // ----- serialized AssumeStatement  ----- ArrayList.ssc(488,7)
    assume $Heap[$Heap[ClassRepr(System.Collections.Comparer), System.Collections.Comparer.Default], $ownerFrame] == $PeerGroupPlaceholder;
    goto block70992;

  block70992:
    // ----- nop
    // ----- load constant 0  ----- ArrayList.ssc(489,7)
    stack0i := 0;
    // ----- call  ----- ArrayList.ssc(489,7)
    assert this != null;
    call stack1i := Collections.ArrayList.get_Count$.Virtual.$(this, false);
    // ----- load field  ----- ArrayList.ssc(489,7)
    stack2o := $Heap[ClassRepr(System.Collections.Comparer), System.Collections.Comparer.Default];
    // ----- call  ----- ArrayList.ssc(489,7)
    assert this != null;
    call Collections.ArrayList.Sort$System.Int32$System.Int32$System.Collections.IComparer$.Virtual.$(this, stack0i, stack1i, stack2o);
    // ----- return
    return;
}



axiom System.Collections.Comparer <: System.Collections.Comparer;

axiom $BaseClass(System.Collections.Comparer) == System.Object && AsDirectSubClass(System.Collections.Comparer, $BaseClass(System.Collections.Comparer)) == System.Collections.Comparer;

axiom !$IsImmutable(System.Collections.Comparer) && $AsMutable(System.Collections.Comparer) == System.Collections.Comparer;

axiom System.Collections.Comparer <: System.Collections.IComparer;

axiom System.Collections.Comparer <: System.Runtime.Serialization.ISerializable;

axiom (forall $U: name :: { $U <: System.Collections.Comparer } $U <: System.Collections.Comparer ==> $U == System.Collections.Comparer);

// System.Collections.Comparer object invariant
axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: System.Collections.Comparer } IsHeap($h) && $h[$oi, $inv] <: System.Collections.Comparer && $h[$oi, $localinv] != $BaseClass(System.Collections.Comparer) ==> true);

procedure Collections.ArrayList.Sort$System.Int32$System.Int32$System.Collections.IComparer$.Virtual.$(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], index$in: int where InRange(index$in, System.Int32), count$in: int where InRange(count$in, System.Int32), comparer$in: ref where $Is(comparer$in, System.Collections.IComparer) && $Heap[comparer$in, $allocated]);
  // user-declared preconditions
  requires 0 <= index$in;
  requires 0 <= count$in;
  requires index$in + count$in <= #Collections.ArrayList.get_Count($Heap, this);
  requires comparer$in == null || !($Heap[this, $ownerRef] == $Heap[comparer$in, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[comparer$in, $ownerFrame]);
  // target object is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // target object is peer consistent (owner must not be valid)
  requires $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
  // comparer is peer consistent
  requires comparer$in == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[comparer$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[comparer$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // comparer is peer consistent (owner must not be valid)
  requires comparer$in == null || $Heap[comparer$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[comparer$in, $ownerRef], $inv] <: $Heap[comparer$in, $ownerFrame]) || $Heap[$Heap[comparer$in, $ownerRef], $localinv] == $BaseClass($Heap[comparer$in, $ownerFrame]);
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



procedure Collections.ArrayList.Sort$System.Collections.IComparer(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], comparer$in: ref where $Is(comparer$in, System.Collections.IComparer) && $Heap[comparer$in, $allocated]);
  // user-declared preconditions
  requires comparer$in == null || !($Heap[this, $ownerRef] == $Heap[comparer$in, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[comparer$in, $ownerFrame]);
  // target object is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // target object is peer consistent (owner must not be valid)
  requires $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
  // comparer is peer consistent
  requires comparer$in == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[comparer$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[comparer$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // comparer is peer consistent (owner must not be valid)
  requires comparer$in == null || $Heap[comparer$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[comparer$in, $ownerRef], $inv] <: $Heap[comparer$in, $ownerFrame]) || $Heap[$Heap[comparer$in, $ownerRef], $localinv] == $BaseClass($Heap[comparer$in, $ownerFrame]);
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



implementation Collections.ArrayList.Sort$System.Collections.IComparer(this: ref, comparer$in: ref)
{
  var comparer: ref where $Is(comparer, System.Collections.IComparer) && $Heap[comparer, $allocated], stack0i: int, stack1i: int, stack2o: ref;

  entry:
    comparer := comparer$in;
    goto block71570;

  block71570:
    goto block71672;

  block71672:
    // ----- nop
    // ----- load constant 0  ----- ArrayList.ssc(496,7)
    stack0i := 0;
    // ----- call  ----- ArrayList.ssc(496,7)
    assert this != null;
    call stack1i := Collections.ArrayList.get_Count$.Virtual.$(this, false);
    // ----- copy  ----- ArrayList.ssc(496,7)
    stack2o := comparer;
    // ----- call  ----- ArrayList.ssc(496,7)
    assert this != null;
    call Collections.ArrayList.Sort$System.Int32$System.Int32$System.Collections.IComparer$.Virtual.$(this, stack0i, stack1i, stack2o);
    // ----- return
    return;
}



procedure Collections.ArrayList.Sort$System.Int32$System.Int32$System.Collections.IComparer(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], index$in: int where InRange(index$in, System.Int32), count$in: int where InRange(count$in, System.Int32), comparer$in: ref where $Is(comparer$in, System.Collections.IComparer) && $Heap[comparer$in, $allocated]);
  // user-declared preconditions
  requires 0 <= index$in;
  requires 0 <= count$in;
  requires index$in + count$in <= #Collections.ArrayList.get_Count($Heap, this);
  requires comparer$in == null || !($Heap[this, $ownerRef] == $Heap[comparer$in, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[comparer$in, $ownerFrame]);
  // target object is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // target object is peer consistent (owner must not be valid)
  requires $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
  // comparer is peer consistent
  requires comparer$in == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[comparer$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[comparer$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // comparer is peer consistent (owner must not be valid)
  requires comparer$in == null || $Heap[comparer$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[comparer$in, $ownerRef], $inv] <: $Heap[comparer$in, $ownerFrame]) || $Heap[$Heap[comparer$in, $ownerRef], $localinv] == $BaseClass($Heap[comparer$in, $ownerFrame]);
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



implementation Collections.ArrayList.Sort$System.Int32$System.Int32$System.Collections.IComparer(this: ref, index$in: int, count$in: int, comparer$in: ref)
{
  var index: int where InRange(index, System.Int32), count: int where InRange(count, System.Int32), comparer: ref where $Is(comparer, System.Collections.IComparer) && $Heap[comparer, $allocated], temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception) && $Heap[local2, $allocated], stack0o: ref, stack1i: int, stack2i: int, stack3o: ref, stack0b: bool, stack0s: struct;

  entry:
    index := index$in;
    count := count$in;
    comparer := comparer$in;
    goto block72573;

  block72573:
    goto block72964;

  block72964:
    // ----- nop
    // ----- FrameGuard processing  ----- ArrayList.ssc(506,15)
    temp0 := this;
    // ----- load token  ----- ArrayList.ssc(506,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(506,15)
    stack1o := TypeObject(Collections.ArrayList);
    // ----- local unpack  ----- ArrayList.ssc(506,15)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: Collections.ArrayList && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block72981;

  block72981:
    // ----- load field  ----- ArrayList.ssc(507,9)
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- copy  ----- ArrayList.ssc(507,9)
    stack1i := index;
    // ----- copy  ----- ArrayList.ssc(507,9)
    stack2i := count;
    // ----- copy  ----- ArrayList.ssc(507,9)
    stack3o := comparer;
    // ----- call  ----- ArrayList.ssc(507,9)
    call System.Array.Sort$System.Array$System.Int32$System.Int32$System.Collections.IComparer(stack0o, stack1i, stack2i, stack3o);
    // ----- branch
    goto block73066;

  block73066:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true73066to73151, false73066to73168;

  true73066to73151:
    assume local2 == stack0o;
    goto block73151;

  false73066to73168:
    assume local2 != stack0o;
    goto block73168;

  block73151:
    // ----- load token  ----- ArrayList.ssc(508,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(508,7)
    stack0o := TypeObject(Collections.ArrayList);
    // ----- local pack  ----- ArrayList.ssc(508,7)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert TypeObject($typeof($Heap[temp0, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert 0 <= $Heap[temp0, Collections.ArrayList._size];
    assert $Heap[temp0, Collections.ArrayList._size] <= $Length($Heap[temp0, Collections.ArrayList._items]);
    assert (forall ^i: int :: $Heap[temp0, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[temp0, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[temp0, Collections.ArrayList._items], $elements], ^i) == null);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Collections.ArrayList ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block73083;

  block73168:
    // ----- is instance
    // ----- branch
    goto true73168to73151, false73168to73100;

  true73168to73151:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block73151;

  false73168to73100:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block73100;

  block73100:
    // ----- branch
    goto block73083;

  block73083:
    // ----- nop
    // ----- branch
    goto block73032;

  block73032:
    // ----- return
    return;
}



procedure System.Array.Sort$System.Array$System.Int32$System.Int32$System.Collections.IComparer(array$in: ref where $Is(array$in, System.Array) && $Heap[array$in, $allocated], index$in: int where InRange(index$in, System.Int32), length$in: int where InRange(length$in, System.Int32), comparer$in: ref where $Is(comparer$in, System.Collections.IComparer) && $Heap[comparer$in, $allocated]);
  // user-declared preconditions
  requires array$in != null;
  requires $Rank(array$in) == 1;
  requires index$in >= $LBound(array$in, 0);
  requires length$in >= 0;
  requires $LBound(array$in, 0) + index$in + length$in <= $Length(array$in);
  // array is peer consistent
  requires array$in == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[array$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[array$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // array is peer consistent (owner must not be valid)
  requires array$in == null || $Heap[array$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[array$in, $ownerRef], $inv] <: $Heap[array$in, $ownerFrame]) || $Heap[$Heap[array$in, $ownerRef], $localinv] == $BaseClass($Heap[array$in, $ownerFrame]);
  // comparer is peer consistent
  requires comparer$in == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[comparer$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[comparer$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // comparer is peer consistent (owner must not be valid)
  requires comparer$in == null || $Heap[comparer$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[comparer$in, $ownerRef], $inv] <: $Heap[comparer$in, $ownerFrame]) || $Heap[$Heap[comparer$in, $ownerRef], $localinv] == $BaseClass($Heap[comparer$in, $ownerFrame]);
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



procedure Collections.ArrayList.ToArray(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated]) returns ($result: ref where $Is($result, RefArray(System.Object, 1)) && $Heap[$result, $allocated]);
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



implementation Collections.ArrayList.ToArray(this: ref) returns ($result: ref)
{
  var temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception) && $Heap[local2, $allocated], stack0i: int, array: ref where $Is(array, RefArray(System.Object, 1)) && $Heap[array, $allocated], temp2: ref, stack0o: ref, stack1i: int, stack2o: ref, stack3i: int, stack4i: int, return.value: ref where $Is(return.value, RefArray(System.Object, 1)) && $Heap[return.value, $allocated], stack0b: bool, stack0s: struct, SS$Display.Return.Local: ref where $Is(SS$Display.Return.Local, RefArray(System.Object, 1)) && $Heap[SS$Display.Return.Local, $allocated];

  entry:
    goto block74171;

  block74171:
    goto block74324;

  block74324:
    // ----- nop
    // ----- FrameGuard processing  ----- ArrayList.ssc(514,15)
    temp0 := this;
    // ----- load token  ----- ArrayList.ssc(514,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(514,15)
    stack1o := TypeObject(Collections.ArrayList);
    // ----- local unpack  ----- ArrayList.ssc(514,15)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: Collections.ArrayList && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block74341;

  block74341:
    // ----- load field  ----- ArrayList.ssc(515,18)
    assert this != null;
    stack0i := $Heap[this, Collections.ArrayList._size];
    // ----- new array  ----- ArrayList.ssc(515,18)
    assert 0 <= stack0i;
    havoc temp2;
    assume $Heap[temp2, $allocated] == false && $Length(temp2) == stack0i;
    assume $Heap[$ElementProxy(temp2, -1), $allocated] == false && $ElementProxy(temp2, -1) != temp2 && $ElementProxy(temp2, -1) != null;
    assume temp2 != null;
    assume $typeof(temp2) == RefArray(System.Object, 1);
    assume $Heap[temp2, $ownerRef] == temp2 && $Heap[temp2, $ownerFrame] == $PeerGroupPlaceholder;
    assume $Heap[$ElementProxy(temp2, -1), $ownerRef] == $ElementProxy(temp2, -1) && $Heap[$ElementProxy(temp2, -1), $ownerFrame] == $PeerGroupPlaceholder;
    assume $Heap[temp2, $inv] == $typeof(temp2) && $Heap[temp2, $localinv] == $typeof(temp2);
    assume (forall $i: int :: RefArrayGet($Heap[temp2, $elements], $i) == null);
    $Heap[temp2, $allocated] := true;
    call System.Object..ctor($ElementProxy(temp2, -1));
    array := temp2;
    assume IsHeap($Heap);
    // ----- load field  ----- ArrayList.ssc(516,9)
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- load constant 0  ----- ArrayList.ssc(516,9)
    stack1i := 0;
    // ----- copy  ----- ArrayList.ssc(516,9)
    stack2o := array;
    // ----- load constant 0  ----- ArrayList.ssc(516,9)
    stack3i := 0;
    // ----- load field  ----- ArrayList.ssc(516,9)
    assert this != null;
    stack4i := $Heap[this, Collections.ArrayList._size];
    // ----- call  ----- ArrayList.ssc(516,9)
    call System.Array.Copy$System.Array$notnull$System.Int32$System.Array$notnull$System.Int32$System.Int32(stack0o, stack1i, stack2o, stack3i, stack4i);
    // ----- copy  ----- ArrayList.ssc(517,9)
    return.value := array;
    // ----- branch
    goto block74562;

  block74562:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true74562to74545, false74562to74528;

  true74562to74545:
    assume local2 == stack0o;
    goto block74545;

  false74562to74528:
    assume local2 != stack0o;
    goto block74528;

  block74545:
    // ----- load token  ----- ArrayList.ssc(518,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(518,7)
    stack0o := TypeObject(Collections.ArrayList);
    // ----- local pack  ----- ArrayList.ssc(518,7)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert TypeObject($typeof($Heap[temp0, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert 0 <= $Heap[temp0, Collections.ArrayList._size];
    assert $Heap[temp0, Collections.ArrayList._size] <= $Length($Heap[temp0, Collections.ArrayList._items]);
    assert (forall ^i: int :: $Heap[temp0, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[temp0, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[temp0, Collections.ArrayList._items], $elements], ^i) == null);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Collections.ArrayList ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block74511;

  block74528:
    // ----- is instance
    // ----- branch
    goto true74528to74545, false74528to74460;

  true74528to74545:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block74545;

  false74528to74460:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block74460;

  block74460:
    // ----- branch
    goto block74511;

  block74511:
    // ----- nop
    // ----- branch
    goto block74409;

  block74409:
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0o := return.value;
    // ----- return
    $result := stack0o;
    return;
}



procedure Collections.ArrayList.ToArray$System.Type$notnull(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], type$in: ref where $IsNotNull(type$in, System.Type) && $Heap[type$in, $allocated]) returns ($result: ref where $Is($result, System.Array) && $Heap[$result, $allocated]);
  // target object is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // target object is peer consistent (owner must not be valid)
  requires $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
  // type is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[type$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[type$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // type is peer consistent (owner must not be valid)
  requires $Heap[type$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[type$in, $ownerRef], $inv] <: $Heap[type$in, $ownerFrame]) || $Heap[$Heap[type$in, $ownerRef], $localinv] == $BaseClass($Heap[type$in, $ownerFrame]);
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



implementation Collections.ArrayList.ToArray$System.Type$notnull(this: ref, type$in: ref) returns ($result: ref)
{
  var \type: ref where $IsNotNull(\type, System.Type) && $Heap[\type, $allocated], temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception) && $Heap[local2, $allocated], stack0o: ref, stack1i: int, array: ref where $Is(array, System.Array) && $Heap[array, $allocated], stack2o: ref, stack3i: int, stack4i: int, return.value: ref where $Is(return.value, System.Array) && $Heap[return.value, $allocated], stack0b: bool, stack0s: struct, SS$Display.Return.Local: ref where $Is(SS$Display.Return.Local, System.Array) && $Heap[SS$Display.Return.Local, $allocated];

  entry:
    \type := type$in;
    goto block75718;

  block75718:
    goto block75922;

  block75922:
    // ----- nop
    // ----- FrameGuard processing  ----- ArrayList.ssc(524,15)
    temp0 := this;
    // ----- load token  ----- ArrayList.ssc(524,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(524,15)
    stack1o := TypeObject(Collections.ArrayList);
    // ----- local unpack  ----- ArrayList.ssc(524,15)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: Collections.ArrayList && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block75939;

  block75939:
    // ----- copy  ----- ArrayList.ssc(525,15)
    stack0o := \type;
    // ----- load field  ----- ArrayList.ssc(525,15)
    assert this != null;
    stack1i := $Heap[this, Collections.ArrayList._size];
    // ----- call  ----- ArrayList.ssc(525,15)
    call array := System.Array.CreateInstance$System.Type$notnull$System.Int32(stack0o, stack1i);
    // ----- load field  ----- ArrayList.ssc(526,9)
    assert this != null;
    stack0o := $Heap[this, Collections.ArrayList._items];
    // ----- load constant 0  ----- ArrayList.ssc(526,9)
    stack1i := 0;
    // ----- copy  ----- ArrayList.ssc(526,9)
    stack2o := array;
    // ----- load constant 0  ----- ArrayList.ssc(526,9)
    stack3i := 0;
    // ----- load field  ----- ArrayList.ssc(526,9)
    assert this != null;
    stack4i := $Heap[this, Collections.ArrayList._size];
    // ----- call  ----- ArrayList.ssc(526,9)
    call System.Array.Copy$System.Array$notnull$System.Int32$System.Array$notnull$System.Int32$System.Int32(stack0o, stack1i, stack2o, stack3i, stack4i);
    // ----- copy  ----- ArrayList.ssc(527,9)
    return.value := array;
    // ----- branch
    goto block76075;

  block76075:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true76075to76092, false76075to76109;

  true76075to76092:
    assume local2 == stack0o;
    goto block76092;

  false76075to76109:
    assume local2 != stack0o;
    goto block76109;

  block76092:
    // ----- load token  ----- ArrayList.ssc(528,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, Collections.ArrayList);
    // ----- statically resolved GetTypeFromHandle call  ----- ArrayList.ssc(528,7)
    stack0o := TypeObject(Collections.ArrayList);
    // ----- local pack  ----- ArrayList.ssc(528,7)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert TypeObject($typeof($Heap[temp0, Collections.ArrayList._items])) == TypeObject(RefArray(System.Object, 1));
    assert 0 <= $Heap[temp0, Collections.ArrayList._size];
    assert $Heap[temp0, Collections.ArrayList._size] <= $Length($Heap[temp0, Collections.ArrayList._items]);
    assert (forall ^i: int :: $Heap[temp0, Collections.ArrayList._size] <= ^i && ^i <= $Length($Heap[temp0, Collections.ArrayList._items]) - 1 ==> RefArrayGet($Heap[$Heap[temp0, Collections.ArrayList._items], $elements], ^i) == null);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Collections.ArrayList ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block76143;

  block76109:
    // ----- is instance
    // ----- branch
    goto true76109to76092, false76109to76041;

  true76109to76092:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block76092;

  false76109to76041:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block76041;

  block76041:
    // ----- branch
    goto block76143;

  block76143:
    // ----- nop
    // ----- branch
    goto block76007;

  block76007:
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0o := return.value;
    // ----- return
    $result := stack0o;
    return;
}



procedure System.Array.CreateInstance$System.Type$notnull$System.Int32(elementType$in: ref where $IsNotNull(elementType$in, System.Type) && $Heap[elementType$in, $allocated], length$in: int where InRange(length$in, System.Int32)) returns ($result: ref where $IsNotNull($result, System.Array) && $Heap[$result, $allocated]);
  // user-declared preconditions
  requires elementType$in != null;
  requires length$in >= 0;
  // elementType is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[elementType$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[elementType$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // elementType is peer consistent (owner must not be valid)
  requires $Heap[elementType$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[elementType$in, $ownerRef], $inv] <: $Heap[elementType$in, $ownerFrame]) || $Heap[$Heap[elementType$in, $ownerRef], $localinv] == $BaseClass($Heap[elementType$in, $ownerFrame]);
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // user-declared postconditions
  ensures $Rank($result) == 1;
  ensures $DimLength($result, 0) == length$in;
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



procedure Collections.ArrayList.TrimToSize(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated]);
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



implementation Collections.ArrayList.TrimToSize(this: ref)
{
  var stack0i: int;

  entry:
    goto block77027;

  block77027:
    goto block77078;

  block77078:
    // ----- nop
    // ----- load field  ----- ArrayList.ssc(534,7)
    assert this != null;
    stack0i := $Heap[this, Collections.ArrayList._size];
    // ----- call  ----- ArrayList.ssc(534,7)
    assert this != null;
    call Collections.ArrayList.set_Capacity$System.Int32$.Virtual.$(this, stack0i);
    // ----- return
    return;
}



procedure Collections.ArrayList.set_Capacity$System.Int32$.Virtual.$(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], value$in: int where InRange(value$in, System.Int32));
  // user-declared preconditions
  requires #Collections.ArrayList.get_Count($Heap, this) <= value$in;
  // target object is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // target object is peer consistent (owner must not be valid)
  requires $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // user-declared postconditions
  ensures value$in <= $Length($Heap[this, Collections.ArrayList._items]);
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



procedure Collections.ArrayList..cctor();
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



implementation Collections.ArrayList..cctor()
{

  entry:
    goto block77384;

  block77384:
    goto block77435;

  block77435:
    // ----- nop
    // ----- return
    return;
}



axiom Collections.TestArrayList <: Collections.TestArrayList;

axiom $BaseClass(Collections.TestArrayList) == System.Object && AsDirectSubClass(Collections.TestArrayList, $BaseClass(Collections.TestArrayList)) == Collections.TestArrayList;

axiom !$IsImmutable(Collections.TestArrayList) && $AsMutable(Collections.TestArrayList) == Collections.TestArrayList;

// Collections.TestArrayList object invariant
axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: Collections.TestArrayList } IsHeap($h) && $h[$oi, $inv] <: Collections.TestArrayList && $h[$oi, $localinv] != $BaseClass(Collections.TestArrayList) ==> true);

procedure Collections.TestArrayList.Main$System.String.array(args$in: ref where $Is(args$in, RefArray(System.String, 1)) && $Heap[args$in, $allocated]);
  // args is peer consistent
  requires args$in == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[args$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[args$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // args is peer consistent (owner must not be valid)
  requires args$in == null || $Heap[args$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[args$in, $ownerRef], $inv] <: $Heap[args$in, $ownerFrame]) || $Heap[$Heap[args$in, $ownerRef], $localinv] == $BaseClass($Heap[args$in, $ownerFrame]);
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



implementation Collections.TestArrayList.Main$System.String.array(args$in: ref)
{
  var args: ref where $Is(args, RefArray(System.String, 1)) && $Heap[args, $allocated], stack50000o: ref, stack0o: ref, a: ref where $Is(a, Collections.ArrayList) && $Heap[a, $allocated], stack1o: ref, stack0i: int, idx: int where InRange(idx, System.Int32), bs: int where InRange(bs, System.Int32), stack1i: int, r: int where InRange(r, System.Int32);

  entry:
    args := args$in;
    goto block80002;

  block80002:
    goto block81311;

  block81311:
    // ----- new object  ----- ArrayList.ssc(546,17)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == Collections.ArrayList;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    // ----- call  ----- ArrayList.ssc(546,17)
    assert stack50000o != null;
    call Collections.ArrayList..ctor(stack50000o);
    // ----- copy  ----- ArrayList.ssc(546,17)
    stack0o := stack50000o;
    // ----- copy  ----- ArrayList.ssc(546,17)
    a := stack0o;
    // ----- serialized AssertStatement  ----- ArrayList.ssc(547,7)
    assert #Collections.ArrayList.get_Count($Heap, a) == 0;
    goto block82280;

  block82280:
    // ----- nop
    // ----- load constant "apple"  ----- ArrayList.ssc(549,7)
    stack0o := $stringLiteral26;
    // ----- call  ----- ArrayList.ssc(549,7)
    assert a != null;
    call stack0i := Collections.ArrayList.Add$System.Object$.Virtual.$(a, stack0o);
    // ----- load constant "cranberry"  ----- ArrayList.ssc(550,7)
    stack0o := $stringLiteral27;
    // ----- call  ----- ArrayList.ssc(550,7)
    assert a != null;
    call stack0i := Collections.ArrayList.Add$System.Object$.Virtual.$(a, stack0o);
    // ----- load constant "banana"  ----- ArrayList.ssc(551,7)
    stack0o := $stringLiteral28;
    // ----- call  ----- ArrayList.ssc(551,7)
    assert a != null;
    call stack0i := Collections.ArrayList.Add$System.Object$.Virtual.$(a, stack0o);
    // ----- serialized AssertStatement  ----- ArrayList.ssc(552,7)
    assert #Collections.ArrayList.get_Count($Heap, a) == 3;
    goto block82399;

  block82399:
    // ----- nop
    // ----- serialized AssertStatement  ----- ArrayList.ssc(553,7)
    assert #Collections.ArrayList.get_Item$System.Int32($Heap, a, 0) == $stringLiteral26;
    goto block80886;

  block80886:
    // ----- nop
    // ----- serialized AssertStatement  ----- ArrayList.ssc(554,7)
    assert #Collections.ArrayList.get_Item$System.Int32($Heap, a, 1) == $stringLiteral27;
    goto block82620;

  block82620:
    // ----- nop
    // ----- serialized AssertStatement  ----- ArrayList.ssc(555,7)
    assert #Collections.ArrayList.get_Item$System.Int32($Heap, a, 2) == $stringLiteral28;
    goto block80767;

  block80767:
    // ----- nop
    // ----- load constant "apple"  ----- ArrayList.ssc(557,11)
    stack0o := $stringLiteral26;
    // ----- call  ----- ArrayList.ssc(557,11)
    assert a != null;
    call idx := Collections.ArrayList.IndexOf$System.Object$.Virtual.$(a, stack0o);
    // ----- serialized AssertStatement  ----- ArrayList.ssc(558,7)
    assert idx == 0;
    goto block82365;

  block82365:
    // ----- nop
    // ----- load constant "cranberry"  ----- ArrayList.ssc(559,7)
    stack0o := $stringLiteral27;
    // ----- call  ----- ArrayList.ssc(559,7)
    assert a != null;
    call idx := Collections.ArrayList.IndexOf$System.Object$.Virtual.$(a, stack0o);
    // ----- serialized AssertStatement  ----- ArrayList.ssc(560,7)
    assert idx == 1;
    goto block81702;

  block81702:
    // ----- nop
    // ----- load constant "banana"  ----- ArrayList.ssc(561,7)
    stack0o := $stringLiteral28;
    // ----- call  ----- ArrayList.ssc(561,7)
    assert a != null;
    call idx := Collections.ArrayList.IndexOf$System.Object$.Virtual.$(a, stack0o);
    // ----- serialized AssertStatement  ----- ArrayList.ssc(562,7)
    assert idx == 2;
    goto block82008;

  block82008:
    // ----- nop
    // ----- load constant "donut"  ----- ArrayList.ssc(563,7)
    stack0o := $stringLiteral43;
    // ----- call  ----- ArrayList.ssc(563,7)
    assert a != null;
    call idx := Collections.ArrayList.IndexOf$System.Object$.Virtual.$(a, stack0o);
    // ----- serialized AssertStatement  ----- ArrayList.ssc(564,7)
    assert idx == -1;
    goto block81549;

  block81549:
    // ----- nop
    // ----- call  ----- ArrayList.ssc(566,7)
    assert a != null;
    call Collections.ArrayList.Sort$.Virtual.$(a);
    // ----- serialized AssertStatement  ----- ArrayList.ssc(567,7)
    assert #Collections.ArrayList.get_Count($Heap, a) == 3;
    goto block81481;

  block81481:
    // ----- nop
    // ----- serialized AssertStatement  ----- ArrayList.ssc(568,7)
    assert #Collections.ArrayList.get_Item$System.Int32($Heap, a, 0) == $stringLiteral26;
    goto block81804;

  block81804:
    // ----- nop
    // ----- serialized AssertStatement  ----- ArrayList.ssc(569,7)
    assert #Collections.ArrayList.get_Item$System.Int32($Heap, a, 1) == $stringLiteral28;
    goto block80903;

  block80903:
    // ----- nop
    // ----- serialized AssertStatement  ----- ArrayList.ssc(570,7)
    assert #Collections.ArrayList.get_Item$System.Int32($Heap, a, 2) == $stringLiteral27;
    goto block80274;

  block80274:
    // ----- nop
    // ----- load constant "apple"  ----- ArrayList.ssc(572,11)
    stack0o := $stringLiteral26;
    // ----- call  ----- ArrayList.ssc(572,11)
    assert a != null;
    call bs := Collections.ArrayList.BinarySearch$System.Object$.Virtual.$(a, stack0o);
    // ----- serialized AssertStatement  ----- ArrayList.ssc(573,7)
    assert bs == 0;
    goto block82603;

  block82603:
    // ----- nop
    // ----- load constant "banana"  ----- ArrayList.ssc(574,7)
    stack0o := $stringLiteral28;
    // ----- call  ----- ArrayList.ssc(574,7)
    assert a != null;
    call bs := Collections.ArrayList.BinarySearch$System.Object$.Virtual.$(a, stack0o);
    // ----- serialized AssertStatement  ----- ArrayList.ssc(575,7)
    assert bs == 1;
    goto block80529;

  block80529:
    // ----- nop
    // ----- load constant "cranberry"  ----- ArrayList.ssc(576,7)
    stack0o := $stringLiteral27;
    // ----- call  ----- ArrayList.ssc(576,7)
    assert a != null;
    call bs := Collections.ArrayList.BinarySearch$System.Object$.Virtual.$(a, stack0o);
    // ----- serialized AssertStatement  ----- ArrayList.ssc(577,7)
    assert bs == 2;
    goto block81634;

  block81634:
    // ----- nop
    // ----- load constant "donut"  ----- ArrayList.ssc(578,7)
    stack0o := $stringLiteral43;
    // ----- call  ----- ArrayList.ssc(578,7)
    assert a != null;
    call bs := Collections.ArrayList.BinarySearch$System.Object$.Virtual.$(a, stack0o);
    // ----- serialized AssertStatement  ----- ArrayList.ssc(579,7)
    assert bs < 0;
    goto block81464;

  block81464:
    // ----- nop
    // ----- call  ----- ArrayList.ssc(581,7)
    assert a != null;
    call Collections.ArrayList.Reverse$.Virtual.$(a);
    // ----- serialized AssertStatement  ----- ArrayList.ssc(582,7)
    assert #Collections.ArrayList.get_Count($Heap, a) == 3;
    goto block82331;

  block82331:
    // ----- nop
    // ----- serialized AssertStatement  ----- ArrayList.ssc(583,7)
    assert #Collections.ArrayList.get_Item$System.Int32($Heap, a, 2) == $stringLiteral26;
    goto block81107;

  block81107:
    // ----- nop
    // ----- serialized AssertStatement  ----- ArrayList.ssc(584,7)
    assert #Collections.ArrayList.get_Item$System.Int32($Heap, a, 1) == $stringLiteral28;
    goto block81685;

  block81685:
    // ----- nop
    // ----- serialized AssertStatement  ----- ArrayList.ssc(585,7)
    assert #Collections.ArrayList.get_Item$System.Int32($Heap, a, 0) == $stringLiteral27;
    goto block81073;

  block81073:
    // ----- nop
    // ----- load constant "apple"  ----- ArrayList.ssc(587,7)
    stack0o := $stringLiteral26;
    // ----- call  ----- ArrayList.ssc(587,7)
    assert a != null;
    call Collections.ArrayList.Remove$System.Object$.Virtual.$(a, stack0o);
    // ----- serialized AssertStatement  ----- ArrayList.ssc(588,7)
    assert #Collections.ArrayList.get_Count($Heap, a) == 2;
    goto block81260;

  block81260:
    // ----- nop
    // ----- serialized AssertStatement  ----- ArrayList.ssc(589,7)
    assert #Collections.ArrayList.get_Item$System.Int32($Heap, a, 0) == $stringLiteral27;
    goto block81090;

  block81090:
    // ----- nop
    // ----- serialized AssertStatement  ----- ArrayList.ssc(590,7)
    assert #Collections.ArrayList.get_Item$System.Int32($Heap, a, 1) == $stringLiteral28;
    goto block81243;

  block81243:
    // ----- nop
    // ----- load constant 0  ----- ArrayList.ssc(592,7)
    stack0i := 0;
    // ----- call  ----- ArrayList.ssc(592,7)
    assert a != null;
    call Collections.ArrayList.RemoveAt$System.Int32$.Virtual.$(a, stack0i);
    // ----- serialized AssertStatement  ----- ArrayList.ssc(593,7)
    assert #Collections.ArrayList.get_Count($Heap, a) == 1;
    goto block82688;

  block82688:
    // ----- nop
    // ----- serialized AssertStatement  ----- ArrayList.ssc(594,7)
    assert #Collections.ArrayList.get_Item$System.Int32($Heap, a, 0) == $stringLiteral28;
    goto block80699;

  block80699:
    // ----- nop
    // ----- call  ----- ArrayList.ssc(596,7)
    assert a != null;
    call Collections.ArrayList.Clear$.Virtual.$(a);
    // ----- serialized AssertStatement  ----- ArrayList.ssc(597,7)
    assert #Collections.ArrayList.get_Count($Heap, a) == 0;
    goto block81600;

  block81600:
    // ----- nop
    // ----- load constant "carrot"  ----- ArrayList.ssc(599,11)
    stack0o := $stringLiteral68;
    // ----- load constant 3  ----- ArrayList.ssc(599,11)
    stack1i := 3;
    // ----- call  ----- ArrayList.ssc(599,11)
    call stack0o := Collections.ArrayList.Repeat$System.Object$System.Int32(stack0o, stack1i);
    // ----- call  ----- ArrayList.ssc(599,11)
    assert stack0o != null;
    call r := Collections.ArrayList.get_Count$.Virtual.$(stack0o, false);
    // ----- serialized AssertStatement  ----- ArrayList.ssc(600,7)
    assert r == 3;
    goto block80597;

  block80597:
    // ----- nop
    // ----- return  ----- ArrayList.ssc(601,5)
    return;
}



procedure Collections.ArrayList.Sort$.Virtual.$(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated]);
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



procedure Collections.ArrayList.BinarySearch$System.Object$.Virtual.$(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], value$in: ref where $Is(value$in, System.Object) && $Heap[value$in, $allocated]) returns ($result: int where InRange($result, System.Int32));
  // user-declared preconditions
  requires value$in == null || !($Heap[this, $ownerRef] == $Heap[value$in, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[value$in, $ownerFrame]);
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
  // user-declared postconditions
  ensures $result < #Collections.ArrayList.get_Count($Heap, this);
  ensures 0 <= $result && $result < #Collections.ArrayList.get_Count($Heap, this) ==> #Collections.ArrayList.get_Item$System.Int32($Heap, this, $result) == value$in;
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



procedure Collections.ArrayList.Reverse$.Virtual.$(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated]);
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



procedure Collections.ArrayList.Remove$System.Object$.Virtual.$(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated], obj$in: ref where $Is(obj$in, System.Object) && $Heap[obj$in, $allocated]);
  // target object is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // target object is peer consistent (owner must not be valid)
  requires $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
  // obj is peer consistent
  requires obj$in == null || (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[obj$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[obj$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // obj is peer consistent (owner must not be valid)
  requires obj$in == null || $Heap[obj$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[obj$in, $ownerRef], $inv] <: $Heap[obj$in, $ownerFrame]) || $Heap[$Heap[obj$in, $ownerRef], $localinv] == $BaseClass($Heap[obj$in, $ownerFrame]);
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



procedure Collections.ArrayList.Clear$.Virtual.$(this: ref where $IsNotNull(this, Collections.ArrayList) && $Heap[this, $allocated]);
  // target object is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // target object is peer consistent (owner must not be valid)
  requires $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
  free requires $BeingConstructed == null;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // user-declared postconditions
  ensures #Collections.ArrayList.get_Count($Heap, this) == 0;
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



procedure Collections.TestArrayList..ctor(this: ref where $IsNotNull(this, Collections.TestArrayList) && $Heap[this, $allocated]);
  // object is fully unpacked:  this.inv == Object
  free requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
  // nothing is owned by [this,*] and 'this' is alone in its own peer group
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this) && $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires $BeingConstructed == this;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // target object is allocated upon return
  free ensures $Heap[this, $allocated];
  // target object is additively exposable for Collections.TestArrayList
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == Collections.TestArrayList && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(Collections.TestArrayList <: DeclType($f))) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] && $o != this ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Collections.TestArrayList..ctor(this: ref)
{

  entry:
    goto block86020;

  block86020:
    goto block86037;

  block86037:
    // ----- call  ----- ArrayList.ssc(542,17)
    assert this != null;
    call System.Object..ctor(this);
    // ----- return
    // ----- translation-inserted post-constructor pack
    assert this != null;
    assert $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == Collections.TestArrayList ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[this, $inv] := Collections.TestArrayList;
    assume IsHeap($Heap);
    return;
}



const unique $stringLiteral2: ref;

// $stringLiteral2 is allocated, interned, and has the appropriate type and length
axiom $IsNotNull($stringLiteral2, System.String) && $StringLength($stringLiteral2) == 13 && (forall heap: [ref,<x>name]x :: { heap[$stringLiteral2, $allocated] } IsHeap(heap) ==> heap[$stringLiteral2, $allocated]) && (forall heap: [ref,<x>name]x :: { #System.String.IsInterned$System.String$notnull(heap, $stringLiteral2) } IsHeap(heap) ==> #System.String.IsInterned$System.String$notnull(heap, $stringLiteral2) == $stringLiteral2);

const unique $stringLiteral26: ref;

// $stringLiteral26 is allocated, interned, and has the appropriate type and length
axiom $IsNotNull($stringLiteral26, System.String) && $StringLength($stringLiteral26) == 5 && (forall heap: [ref,<x>name]x :: { heap[$stringLiteral26, $allocated] } IsHeap(heap) ==> heap[$stringLiteral26, $allocated]) && (forall heap: [ref,<x>name]x :: { #System.String.IsInterned$System.String$notnull(heap, $stringLiteral26) } IsHeap(heap) ==> #System.String.IsInterned$System.String$notnull(heap, $stringLiteral26) == $stringLiteral26);

const unique $stringLiteral27: ref;

// $stringLiteral27 is allocated, interned, and has the appropriate type and length
axiom $IsNotNull($stringLiteral27, System.String) && $StringLength($stringLiteral27) == 9 && (forall heap: [ref,<x>name]x :: { heap[$stringLiteral27, $allocated] } IsHeap(heap) ==> heap[$stringLiteral27, $allocated]) && (forall heap: [ref,<x>name]x :: { #System.String.IsInterned$System.String$notnull(heap, $stringLiteral27) } IsHeap(heap) ==> #System.String.IsInterned$System.String$notnull(heap, $stringLiteral27) == $stringLiteral27);

const unique $stringLiteral28: ref;

// $stringLiteral28 is allocated, interned, and has the appropriate type and length
axiom $IsNotNull($stringLiteral28, System.String) && $StringLength($stringLiteral28) == 6 && (forall heap: [ref,<x>name]x :: { heap[$stringLiteral28, $allocated] } IsHeap(heap) ==> heap[$stringLiteral28, $allocated]) && (forall heap: [ref,<x>name]x :: { #System.String.IsInterned$System.String$notnull(heap, $stringLiteral28) } IsHeap(heap) ==> #System.String.IsInterned$System.String$notnull(heap, $stringLiteral28) == $stringLiteral28);

const unique $stringLiteral43: ref;

// $stringLiteral43 is allocated, interned, and has the appropriate type and length
axiom $IsNotNull($stringLiteral43, System.String) && $StringLength($stringLiteral43) == 5 && (forall heap: [ref,<x>name]x :: { heap[$stringLiteral43, $allocated] } IsHeap(heap) ==> heap[$stringLiteral43, $allocated]) && (forall heap: [ref,<x>name]x :: { #System.String.IsInterned$System.String$notnull(heap, $stringLiteral43) } IsHeap(heap) ==> #System.String.IsInterned$System.String$notnull(heap, $stringLiteral43) == $stringLiteral43);

const unique $stringLiteral68: ref;

// $stringLiteral68 is allocated, interned, and has the appropriate type and length
axiom $IsNotNull($stringLiteral68, System.String) && $StringLength($stringLiteral68) == 6 && (forall heap: [ref,<x>name]x :: { heap[$stringLiteral68, $allocated] } IsHeap(heap) ==> heap[$stringLiteral68, $allocated]) && (forall heap: [ref,<x>name]x :: { #System.String.IsInterned$System.String$notnull(heap, $stringLiteral68) } IsHeap(heap) ==> #System.String.IsInterned$System.String$notnull(heap, $stringLiteral68) == $stringLiteral68);
