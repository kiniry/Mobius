// Spec# program verifier version 0.90, Copyright (c) 2003-2008, Microsoft.
// Command Line Options: /print:BagFixed.bpl BagFixed.dll

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

const unique BagFixed.elems: <ref>name;

const unique BagFixed.count: <int>name;

const unique System.IComparable`1...System.String: name;

const unique System.Reflection.IReflect: name;

const unique System.Reflection.ICustomAttributeProvider: name;

const unique Microsoft.Contracts.GuardException: name;

const unique System.IEquatable`1...System.String: name;

const unique System.ICloneable: name;

const unique Microsoft.Contracts.ObjectInvariantException: name;

const unique BagFixed: name;

const unique System.Collections.IEnumerable: name;

const unique System.Collections.IList: name;

const unique System.Collections.Generic.IEnumerable`1...System.Char: name;

const unique System.Runtime.InteropServices._MemberInfo: name;

const unique System.Runtime.InteropServices._Type: name;

const unique System.IConvertible: name;

const unique System.Exception: name;

const unique System.Reflection.MemberInfo: name;

const unique Microsoft.Contracts.ICheckedException: name;

const unique System.IComparable: name;

const unique System.Collections.ICollection: name;

const unique System.Runtime.InteropServices._Exception: name;

const unique System.Runtime.Serialization.ISerializable: name;

axiom !IsStaticField(BagFixed.count);

axiom IncludeInMainFrameCondition(BagFixed.count);

axiom $IncludedInModifiesStar(BagFixed.count);

axiom DeclType(BagFixed.count) == BagFixed;

axiom AsRangeField(BagFixed.count, System.Int32) == BagFixed.count;

axiom !IsStaticField(BagFixed.elems);

axiom IncludeInMainFrameCondition(BagFixed.elems);

axiom $IncludedInModifiesStar(BagFixed.elems);

axiom AsRepField(BagFixed.elems, BagFixed) == BagFixed.elems;

axiom DeclType(BagFixed.elems) == BagFixed;

axiom AsNonNullRefField(BagFixed.elems, IntArray(System.Int32, 1)) == BagFixed.elems;

axiom BagFixed <: BagFixed;

axiom $BaseClass(BagFixed) == System.Object && AsDirectSubClass(BagFixed, $BaseClass(BagFixed)) == BagFixed;

axiom !$IsImmutable(BagFixed) && $AsMutable(BagFixed) == BagFixed;

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

// BagFixed object invariant
axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: BagFixed } IsHeap($h) && $h[$oi, $inv] <: BagFixed && $h[$oi, $localinv] != $BaseClass(BagFixed) ==> 0 <= $h[$oi, BagFixed.count] && $h[$oi, BagFixed.count] <= $Length($h[$oi, BagFixed.elems]));

procedure BagFixed.SpecSharp.CheckInvariant$System.Boolean(this: ref where $IsNotNull(this, BagFixed) && $Heap[this, $allocated], throwException$in: bool where true) returns ($result: bool where true);
  // user-declared preconditions
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this) && (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == BagFixed ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
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



implementation BagFixed.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool) returns ($result: bool)
{
  var throwException: bool where true, stack0i: int, stack1i: int, stack0b: bool, stack1o: ref, return.value: bool where true, stack50000o: ref, stack0o: ref, SS$Display.Return.Local: bool where true;

  entry:
    throwException := throwException$in;
    goto block2397;

  block2397:
    goto block2499;

  block2499:
    // ----- nop
    // ----- load constant 0
    stack0i := 0;
    // ----- load field
    assert this != null;
    stack1i := $Heap[this, BagFixed.count];
    // ----- binary operator
    // ----- branch
    goto true2499to2567, false2499to2431;

  true2499to2567:
    assume stack0i > stack1i;
    goto block2567;

  false2499to2431:
    assume stack0i <= stack1i;
    goto block2431;

  block2567:
    // ----- copy
    stack0b := throwException;
    // ----- unary operator
    // ----- branch
    goto true2567to2601, false2567to2618;

  block2431:
    // ----- load field
    assert this != null;
    stack0i := $Heap[this, BagFixed.count];
    // ----- load field
    assert this != null;
    stack1o := $Heap[this, BagFixed.elems];
    // ----- unary operator
    assert stack1o != null;
    stack1i := $Length(stack1o);
    // ----- unary operator
    stack1i := $IntToInt(stack1i, System.UIntPtr, System.Int32);
    // ----- binary operator
    // ----- branch
    goto true2431to2567, false2431to2482;

  true2431to2567:
    assume stack0i > stack1i;
    goto block2567;

  false2431to2482:
    assume stack0i <= stack1i;
    goto block2482;

  block2482:
    // ----- branch
    goto block2465;

  true2567to2601:
    assume !stack0b;
    goto block2601;

  false2567to2618:
    assume stack0b;
    goto block2618;

  block2601:
    // ----- load constant 0
    return.value := false;
    // ----- branch
    goto block2584;

  block2618:
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

  block2465:
    // ----- load constant 1
    return.value := true;
    // ----- branch
    goto block2584;

  block2584:
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0b := return.value;
    // ----- return
    $result := stack0b;
    return;
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



procedure BagFixed..ctor$System.Int32.array$notnull(this: ref where $IsNotNull(this, BagFixed) && $Heap[this, $allocated], initialElements$in: ref where $IsNotNull(initialElements$in, IntArray(System.Int32, 1)) && $Heap[initialElements$in, $allocated]);
  // object is fully unpacked:  this.inv == Object
  free requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
  // initialElements is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[initialElements$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[initialElements$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // initialElements is peer consistent (owner must not be valid)
  requires $Heap[initialElements$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[initialElements$in, $ownerRef], $inv] <: $Heap[initialElements$in, $ownerFrame]) || $Heap[$Heap[initialElements$in, $ownerRef], $localinv] == $BaseClass($Heap[initialElements$in, $ownerFrame]);
  // nothing is owned by [this,*] and 'this' is alone in its own peer group
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this) && $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires $BeingConstructed == this;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // target object is allocated upon return
  free ensures $Heap[this, $allocated];
  // target object is additively exposable for BagFixed
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == BagFixed && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(BagFixed <: DeclType($f))) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] && $o != this ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation BagFixed..ctor$System.Int32.array$notnull(this: ref, initialElements$in: ref)
{
  var initialElements: ref where $IsNotNull(initialElements, IntArray(System.Int32, 1)) && $Heap[initialElements, $allocated], stack0o: ref, stack0i: int, temp0: exposeVersionType, e: ref where $Is(e, IntArray(System.Int32, 1)) && $Heap[e, $allocated], temp1: ref, stack1i: int, stack2o: ref, stack3i: int, stack4o: ref, stack4i: int, temp2: exposeVersionType, temp3: ref;

  entry:
    initialElements := initialElements$in;
    assume $Heap[this, BagFixed.count] == 0;
    goto block3349;

  block3349:
    goto block3485;

  block3485:
    // ----- nop
    // ----- copy  ----- BagFixed.ssc(11,5)
    stack0o := initialElements;
    // ----- unary operator  ----- BagFixed.ssc(11,5)
    assert stack0o != null;
    stack0i := $Length(stack0o);
    // ----- unary operator  ----- BagFixed.ssc(11,5)
    stack0i := $IntToInt(stack0i, System.UIntPtr, System.Int32);
    // ----- store field  ----- BagFixed.ssc(11,5)
    assert this != null;
    assert $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
    havoc temp0;
    $Heap[this, $exposeVersion] := temp0;
    $Heap[this, BagFixed.count] := stack0i;
    assert !($Heap[this, $inv] <: BagFixed && $Heap[this, $localinv] != $BaseClass(BagFixed)) || 0 <= $Heap[this, BagFixed.count];
    assert !($Heap[this, $inv] <: BagFixed && $Heap[this, $localinv] != $BaseClass(BagFixed)) || $Heap[this, BagFixed.count] <= $Length($Heap[this, BagFixed.elems]);
    assume IsHeap($Heap);
    // ----- copy  ----- BagFixed.ssc(12,11)
    stack0o := initialElements;
    // ----- unary operator  ----- BagFixed.ssc(12,11)
    assert stack0o != null;
    stack0i := $Length(stack0o);
    // ----- unary operator  ----- BagFixed.ssc(12,11)
    stack0i := $IntToInt(stack0i, System.UIntPtr, System.Int32);
    // ----- new array  ----- BagFixed.ssc(12,11)
    assert 0 <= stack0i;
    havoc temp1;
    assume $Heap[temp1, $allocated] == false && $Length(temp1) == stack0i;
    assume $Heap[$ElementProxy(temp1, -1), $allocated] == false && $ElementProxy(temp1, -1) != temp1 && $ElementProxy(temp1, -1) != null;
    assume temp1 != null;
    assume $typeof(temp1) == IntArray(System.Int32, 1);
    assume $Heap[temp1, $ownerRef] == temp1 && $Heap[temp1, $ownerFrame] == $PeerGroupPlaceholder;
    assume $Heap[$ElementProxy(temp1, -1), $ownerRef] == $ElementProxy(temp1, -1) && $Heap[$ElementProxy(temp1, -1), $ownerFrame] == $PeerGroupPlaceholder;
    assume $Heap[temp1, $inv] == $typeof(temp1) && $Heap[temp1, $localinv] == $typeof(temp1);
    assume (forall $i: int :: IntArrayGet($Heap[temp1, $elements], $i) == 0);
    $Heap[temp1, $allocated] := true;
    call System.Object..ctor($ElementProxy(temp1, -1));
    e := temp1;
    assume IsHeap($Heap);
    // ----- copy  ----- BagFixed.ssc(13,5)
    stack0o := initialElements;
    // ----- load constant 0  ----- BagFixed.ssc(13,5)
    stack1i := 0;
    // ----- copy  ----- BagFixed.ssc(13,5)
    stack2o := e;
    // ----- load constant 0  ----- BagFixed.ssc(13,5)
    stack3i := 0;
    // ----- copy  ----- BagFixed.ssc(13,5)
    stack4o := initialElements;
    // ----- unary operator  ----- BagFixed.ssc(13,5)
    assert stack4o != null;
    stack4i := $Length(stack4o);
    // ----- unary operator  ----- BagFixed.ssc(13,5)
    stack4i := $IntToInt(stack4i, System.UIntPtr, System.Int32);
    // ----- call  ----- BagFixed.ssc(13,5)
    call System.Array.Copy$System.Array$notnull$System.Int32$System.Array$notnull$System.Int32$System.Int32(stack0o, stack1i, stack2o, stack3i, stack4i);
    // ----- store field  ----- BagFixed.ssc(14,5)
    assert this != null;
    assert $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
    assert ($Heap[e, $ownerRef] == this && $Heap[e, $ownerFrame] == BagFixed) || $Heap[e, $ownerFrame] == $PeerGroupPlaceholder;
    assert $Heap[e, $ownerFrame] == $PeerGroupPlaceholder && $Heap[this, $inv] <: BagFixed && $Heap[this, $localinv] != $BaseClass(BagFixed) ==> (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[e, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[e, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
    assert $Heap[e, $ownerFrame] == $PeerGroupPlaceholder && $Heap[this, $inv] <: BagFixed && $Heap[this, $localinv] != $BaseClass(BagFixed) ==> $Heap[this, $ownerRef] != $Heap[e, $ownerRef] || $Heap[this, $ownerFrame] != $Heap[e, $ownerFrame];
    call $UpdateOwnersForRep(this, BagFixed, e);
    havoc temp2;
    $Heap[this, $exposeVersion] := temp2;
    $Heap[this, BagFixed.elems] := e;
    assert !($Heap[this, $inv] <: BagFixed && $Heap[this, $localinv] != $BaseClass(BagFixed)) || 0 <= $Heap[this, BagFixed.count];
    assert !($Heap[this, $inv] <: BagFixed && $Heap[this, $localinv] != $BaseClass(BagFixed)) || $Heap[this, BagFixed.count] <= $Length($Heap[this, BagFixed.elems]);
    assume IsHeap($Heap);
    // ----- call  ----- BagFixed.ssc(15,5)
    assert this != null;
    call System.Object..ctor(this);
    goto block3434;

  block3434:
    // ----- FrameGuard processing  ----- BagFixed.ssc(16,3)
    temp3 := this;
    // ----- classic pack  ----- BagFixed.ssc(16,3)
    assert temp3 != null;
    assert $Heap[temp3, $inv] == System.Object && $Heap[temp3, $localinv] == $typeof(temp3);
    assert 0 <= $Heap[temp3, BagFixed.count];
    assert $Heap[temp3, BagFixed.count] <= $Length($Heap[temp3, BagFixed.elems]);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == temp3 && $Heap[$p, $ownerFrame] == BagFixed ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp3, $inv] := BagFixed;
    assume IsHeap($Heap);
    // ----- return
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



procedure BagFixed..ctor$System.Int32.array$notnull$System.Int32$System.Int32(this: ref where $IsNotNull(this, BagFixed) && $Heap[this, $allocated], initialElements$in: ref where $IsNotNull(initialElements$in, IntArray(System.Int32, 1)) && $Heap[initialElements$in, $allocated], start$in: int where InRange(start$in, System.Int32), howMany$in: int where InRange(howMany$in, System.Int32));
  // object is fully unpacked:  this.inv == Object
  free requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
  // user-declared preconditions
  requires 0 <= start$in;
  requires 0 <= howMany$in;
  requires start$in + howMany$in <= $Length(initialElements$in);
  // initialElements is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[initialElements$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[initialElements$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // initialElements is peer consistent (owner must not be valid)
  requires $Heap[initialElements$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[initialElements$in, $ownerRef], $inv] <: $Heap[initialElements$in, $ownerFrame]) || $Heap[$Heap[initialElements$in, $ownerRef], $localinv] == $BaseClass($Heap[initialElements$in, $ownerFrame]);
  // nothing is owned by [this,*] and 'this' is alone in its own peer group
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this) && $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires $BeingConstructed == this;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // target object is allocated upon return
  free ensures $Heap[this, $allocated];
  // target object is additively exposable for BagFixed
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == BagFixed && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(BagFixed <: DeclType($f))) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] && $o != this ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation BagFixed..ctor$System.Int32.array$notnull$System.Int32$System.Int32(this: ref, initialElements$in: ref, start$in: int, howMany$in: int)
{
  var initialElements: ref where $IsNotNull(initialElements, IntArray(System.Int32, 1)) && $Heap[initialElements, $allocated], start: int where InRange(start, System.Int32), howMany: int where InRange(howMany, System.Int32), temp0: exposeVersionType, stack0i: int, e: ref where $Is(e, IntArray(System.Int32, 1)) && $Heap[e, $allocated], temp1: ref, stack0o: ref, stack1i: int, stack2o: ref, stack3i: int, stack4i: int, temp2: exposeVersionType, temp3: ref;

  entry:
    initialElements := initialElements$in;
    start := start$in;
    howMany := howMany$in;
    assume $Heap[this, BagFixed.count] == 0;
    goto block4352;

  block4352:
    goto block4658;

  block4658:
    // ----- nop
    // ----- store field  ----- BagFixed.ssc(22,5)
    assert this != null;
    assert $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
    havoc temp0;
    $Heap[this, $exposeVersion] := temp0;
    $Heap[this, BagFixed.count] := howMany;
    assert !($Heap[this, $inv] <: BagFixed && $Heap[this, $localinv] != $BaseClass(BagFixed)) || 0 <= $Heap[this, BagFixed.count];
    assert !($Heap[this, $inv] <: BagFixed && $Heap[this, $localinv] != $BaseClass(BagFixed)) || $Heap[this, BagFixed.count] <= $Length($Heap[this, BagFixed.elems]);
    assume IsHeap($Heap);
    // ----- copy  ----- BagFixed.ssc(23,11)
    stack0i := howMany;
    // ----- new array  ----- BagFixed.ssc(23,11)
    assert 0 <= stack0i;
    havoc temp1;
    assume $Heap[temp1, $allocated] == false && $Length(temp1) == stack0i;
    assume $Heap[$ElementProxy(temp1, -1), $allocated] == false && $ElementProxy(temp1, -1) != temp1 && $ElementProxy(temp1, -1) != null;
    assume temp1 != null;
    assume $typeof(temp1) == IntArray(System.Int32, 1);
    assume $Heap[temp1, $ownerRef] == temp1 && $Heap[temp1, $ownerFrame] == $PeerGroupPlaceholder;
    assume $Heap[$ElementProxy(temp1, -1), $ownerRef] == $ElementProxy(temp1, -1) && $Heap[$ElementProxy(temp1, -1), $ownerFrame] == $PeerGroupPlaceholder;
    assume $Heap[temp1, $inv] == $typeof(temp1) && $Heap[temp1, $localinv] == $typeof(temp1);
    assume (forall $i: int :: IntArrayGet($Heap[temp1, $elements], $i) == 0);
    $Heap[temp1, $allocated] := true;
    call System.Object..ctor($ElementProxy(temp1, -1));
    e := temp1;
    assume IsHeap($Heap);
    // ----- copy  ----- BagFixed.ssc(24,5)
    stack0o := initialElements;
    // ----- copy  ----- BagFixed.ssc(24,5)
    stack1i := start;
    // ----- copy  ----- BagFixed.ssc(24,5)
    stack2o := e;
    // ----- load constant 0  ----- BagFixed.ssc(24,5)
    stack3i := 0;
    // ----- copy  ----- BagFixed.ssc(24,5)
    stack4i := howMany;
    // ----- call  ----- BagFixed.ssc(24,5)
    call System.Array.Copy$System.Array$notnull$System.Int32$System.Array$notnull$System.Int32$System.Int32(stack0o, stack1i, stack2o, stack3i, stack4i);
    // ----- store field  ----- BagFixed.ssc(25,5)
    assert this != null;
    assert $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
    assert ($Heap[e, $ownerRef] == this && $Heap[e, $ownerFrame] == BagFixed) || $Heap[e, $ownerFrame] == $PeerGroupPlaceholder;
    assert $Heap[e, $ownerFrame] == $PeerGroupPlaceholder && $Heap[this, $inv] <: BagFixed && $Heap[this, $localinv] != $BaseClass(BagFixed) ==> (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[e, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[e, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
    assert $Heap[e, $ownerFrame] == $PeerGroupPlaceholder && $Heap[this, $inv] <: BagFixed && $Heap[this, $localinv] != $BaseClass(BagFixed) ==> $Heap[this, $ownerRef] != $Heap[e, $ownerRef] || $Heap[this, $ownerFrame] != $Heap[e, $ownerFrame];
    call $UpdateOwnersForRep(this, BagFixed, e);
    havoc temp2;
    $Heap[this, $exposeVersion] := temp2;
    $Heap[this, BagFixed.elems] := e;
    assert !($Heap[this, $inv] <: BagFixed && $Heap[this, $localinv] != $BaseClass(BagFixed)) || 0 <= $Heap[this, BagFixed.count];
    assert !($Heap[this, $inv] <: BagFixed && $Heap[this, $localinv] != $BaseClass(BagFixed)) || $Heap[this, BagFixed.count] <= $Length($Heap[this, BagFixed.elems]);
    assume IsHeap($Heap);
    // ----- call  ----- BagFixed.ssc(26,5)
    assert this != null;
    call System.Object..ctor(this);
    goto block4488;

  block4488:
    // ----- FrameGuard processing  ----- BagFixed.ssc(27,3)
    temp3 := this;
    // ----- classic pack  ----- BagFixed.ssc(27,3)
    assert temp3 != null;
    assert $Heap[temp3, $inv] == System.Object && $Heap[temp3, $localinv] == $typeof(temp3);
    assert 0 <= $Heap[temp3, BagFixed.count];
    assert $Heap[temp3, BagFixed.count] <= $Length($Heap[temp3, BagFixed.elems]);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == temp3 && $Heap[$p, $ownerFrame] == BagFixed ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp3, $inv] := BagFixed;
    assume IsHeap($Heap);
    // ----- return
    return;
}



procedure BagFixed.RemoveMin(this: ref where $IsNotNull(this, BagFixed) && $Heap[this, $allocated]) returns ($result: int where InRange($result, System.Int32));
  // user-declared preconditions
  requires 0 < $Heap[this, BagFixed.count];
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



implementation BagFixed.RemoveMin(this: ref) returns ($result: int)
{
  var temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception) && $Heap[local2, $allocated], m: int where InRange(m, System.Int32), mindex: int where InRange(mindex, System.Int32), i: int where InRange(i, System.Int32), stack0o: ref, stack0i: int, stack0b: bool, stack1i: int, local8: int where InRange(local8, System.Int32), temp2: exposeVersionType, stack2o: ref, stack3i: int, stack2i: int, return.value: int where InRange(return.value, System.Int32), local7: int where InRange(local7, System.Int32), stack0s: struct, SS$Display.Return.Local: int where InRange(SS$Display.Return.Local, System.Int32), $Heap$block5950$LoopPreheader: [ref,<x>name]x;

  entry:
    goto block5712;

  block5712:
    goto block5916;

  block5916:
    // ----- nop
    // ----- FrameGuard processing  ----- BagFixed.ssc(32,13)
    temp0 := this;
    // ----- load token  ----- BagFixed.ssc(32,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, BagFixed);
    // ----- statically resolved GetTypeFromHandle call  ----- BagFixed.ssc(32,13)
    stack1o := TypeObject(BagFixed);
    // ----- local unpack  ----- BagFixed.ssc(32,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: BagFixed && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block5933;

  block5933:
    // ----- load constant 2147483647  ----- BagFixed.ssc(33,11)
    m := int#2147483647;
    // ----- load constant 0  ----- BagFixed.ssc(34,11)
    mindex := 0;
    // ----- load constant 0  ----- BagFixed.ssc(35,16)
    i := 0;
    goto block5950$LoopPreheader;

  block5950:
    // ----- serialized LoopInvariant  ----- BagFixed.ssc(36,19)
    assert 0 <= i;
    // ----- serialized LoopInvariant  ----- BagFixed.ssc(36,19)
    assert i <= $Heap[this, BagFixed.count];
    // ----- serialized LoopInvariant  ----- BagFixed.ssc(36,19)
    assert 0 <= mindex;
    // ----- serialized LoopInvariant  ----- BagFixed.ssc(36,19)
    assert mindex < $Heap[this, BagFixed.count];
    // ----- default loop invariant: allocation and ownership are stable  ----- BagFixed.ssc(36,19)
    assume (forall $o: ref :: { $Heap[$o, $allocated] } $Heap$block5950$LoopPreheader[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } $Heap$block5950$LoopPreheader[$ot, $allocated] && $Heap$block5950$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block5950$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block5950$LoopPreheader[$ot, $ownerFrame]) && $Heap$block5950$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: exposure  ----- BagFixed.ssc(36,19)
    assume (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $Heap$block5950$LoopPreheader[$o, $allocated] ==> $Heap$block5950$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block5950$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]);
    assume (forall $o: ref :: !$Heap$block5950$LoopPreheader[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: modifies  ----- BagFixed.ssc(36,19)
    assert (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || !($typeof(this) <: DeclType($f)) || !$IncludedInModifiesStar($f)) && old(true) ==> $Heap$block5950$LoopPreheader[$o, $f] == $Heap[$o, $f]);
    assume $HeapSucc($Heap$block5950$LoopPreheader, $Heap);
    // ----- default loop invariant: owner fields  ----- BagFixed.ssc(36,19)
    assert (forall $o: ref :: { $Heap[$o, $ownerFrame] } { $Heap[$o, $ownerRef] } $o != null && $Heap$block5950$LoopPreheader[$o, $allocated] ==> $Heap[$o, $ownerRef] == $Heap$block5950$LoopPreheader[$o, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap$block5950$LoopPreheader[$o, $ownerFrame]);
    // ----- advance activity
    havoc $ActivityIndicator;
    goto block6103;

  block6103:
    // ----- nop
    // ----- load field  ----- BagFixed.ssc(35,23)
    assert this != null;
    stack0i := $Heap[this, BagFixed.count];
    // ----- binary operator  ----- BagFixed.ssc(35,23)
    // ----- branch  ----- BagFixed.ssc(35,23)
    goto true6103to6171, false6103to6120;

  true6103to6171:
    assume i >= stack0i;
    goto block6171;

  false6103to6120:
    assume i < stack0i;
    goto block6120;

  block6171:
    // ----- load field  ----- BagFixed.ssc(43,7)
    assert this != null;
    local8 := $Heap[this, BagFixed.count];
    // ----- load constant 1  ----- BagFixed.ssc(43,7)
    stack0i := 1;
    // ----- binary operator  ----- BagFixed.ssc(43,7)
    stack0i := local8 - stack0i;
    // ----- store field  ----- BagFixed.ssc(43,7)
    assert this != null;
    assert $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
    havoc temp2;
    $Heap[this, $exposeVersion] := temp2;
    $Heap[this, BagFixed.count] := stack0i;
    assert !($Heap[this, $inv] <: BagFixed && $Heap[this, $localinv] != $BaseClass(BagFixed)) || 0 <= $Heap[this, BagFixed.count];
    assert !($Heap[this, $inv] <: BagFixed && $Heap[this, $localinv] != $BaseClass(BagFixed)) || $Heap[this, BagFixed.count] <= $Length($Heap[this, BagFixed.elems]);
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local8;
    // ----- load field  ----- BagFixed.ssc(44,7)
    assert this != null;
    stack0o := $Heap[this, BagFixed.elems];
    // ----- copy  ----- BagFixed.ssc(44,7)
    stack1i := mindex;
    // ----- load field  ----- BagFixed.ssc(44,7)
    assert this != null;
    stack2o := $Heap[this, BagFixed.elems];
    // ----- load field  ----- BagFixed.ssc(44,7)
    assert this != null;
    stack3i := $Heap[this, BagFixed.count];
    // ----- load element  ----- BagFixed.ssc(44,7)
    assert stack2o != null;
    assert 0 <= stack3i;
    assert stack3i < $Length(stack2o);
    stack2i := IntArrayGet($Heap[stack2o, $elements], stack3i);
    // ----- store element  ----- BagFixed.ssc(44,7)
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]);
    $Heap[stack0o, $elements] := IntArraySet($Heap[stack0o, $elements], stack1i, stack2i);
    assume IsHeap($Heap);
    // ----- copy  ----- BagFixed.ssc(45,7)
    return.value := m;
    // ----- branch
    goto block6290;

  block6120:
    // ----- load field  ----- BagFixed.ssc(38,9)
    assert this != null;
    stack0o := $Heap[this, BagFixed.elems];
    // ----- copy  ----- BagFixed.ssc(38,9)
    stack1i := i;
    // ----- load element  ----- BagFixed.ssc(38,9)
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    stack0i := IntArrayGet($Heap[stack0o, $elements], stack1i);
    // ----- binary operator  ----- BagFixed.ssc(38,9)
    // ----- branch  ----- BagFixed.ssc(38,9)
    goto true6120to6154, false6120to6137;

  true6120to6154:
    assume stack0i >= m;
    goto block6154;

  false6120to6137:
    assume stack0i < m;
    goto block6137;

  block6154:
    // ----- copy  ----- BagFixed.ssc(35,34)
    local7 := i;
    // ----- load constant 1  ----- BagFixed.ssc(35,34)
    stack0i := 1;
    // ----- binary operator  ----- BagFixed.ssc(35,34)
    stack0i := local7 + stack0i;
    // ----- copy  ----- BagFixed.ssc(35,34)
    i := stack0i;
    // ----- copy
    stack0i := local7;
    // ----- branch
    goto block5950;

  block6137:
    // ----- copy  ----- BagFixed.ssc(39,11)
    mindex := i;
    // ----- load field  ----- BagFixed.ssc(40,11)
    assert this != null;
    stack0o := $Heap[this, BagFixed.elems];
    // ----- copy  ----- BagFixed.ssc(40,11)
    stack1i := i;
    // ----- load element  ----- BagFixed.ssc(40,11)
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    m := IntArrayGet($Heap[stack0o, $elements], stack1i);
    goto block6154;

  block6290:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true6290to6358, false6290to6375;

  true6290to6358:
    assume local2 == stack0o;
    goto block6358;

  false6290to6375:
    assume local2 != stack0o;
    goto block6375;

  block6358:
    // ----- load token  ----- BagFixed.ssc(46,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, BagFixed);
    // ----- statically resolved GetTypeFromHandle call  ----- BagFixed.ssc(46,5)
    stack0o := TypeObject(BagFixed);
    // ----- local pack  ----- BagFixed.ssc(46,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, BagFixed.count];
    assert $Heap[temp0, BagFixed.count] <= $Length($Heap[temp0, BagFixed.elems]);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == BagFixed ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block6273;

  block6375:
    // ----- is instance
    // ----- branch
    goto true6375to6358, false6375to6409;

  true6375to6358:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block6358;

  false6375to6409:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block6409;

  block6409:
    // ----- branch
    goto block6273;

  block6273:
    // ----- nop
    // ----- branch
    goto block6239;

  block6239:
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0i := return.value;
    // ----- return
    $result := stack0i;
    return;

  block5950$LoopPreheader:
    $Heap$block5950$LoopPreheader := $Heap;
    goto block5950;
}



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

axiom Microsoft.Contracts.ICheckedException <: Microsoft.Contracts.ICheckedException;

axiom Microsoft.Contracts.ICheckedException <: System.Object;

axiom $IsMemberlessType(Microsoft.Contracts.ICheckedException);

axiom $AsInterface(Microsoft.Contracts.ICheckedException) == Microsoft.Contracts.ICheckedException;

procedure BagFixed.Add$System.Int32(this: ref where $IsNotNull(this, BagFixed) && $Heap[this, $allocated], x$in: int where InRange(x$in, System.Int32));
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



implementation BagFixed.Add$System.Int32(this: ref, x$in: int)
{
  var x: int where InRange(x, System.Int32), temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception) && $Heap[local2, $allocated], stack0i: int, stack1i: int, stack0b: bool, stack0o: ref, local4: int where InRange(local4, System.Int32), temp2: exposeVersionType, b: ref where $Is(b, IntArray(System.Int32, 1)) && $Heap[b, $allocated], temp3: ref, stack2o: ref, stack3i: int, stack4o: ref, stack4i: int, temp4: exposeVersionType, stack0s: struct;

  entry:
    x := x$in;
    goto block9078;

  block9078:
    goto block9231;

  block9231:
    // ----- nop
    // ----- FrameGuard processing  ----- BagFixed.ssc(51,13)
    temp0 := this;
    // ----- load token  ----- BagFixed.ssc(51,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, BagFixed);
    // ----- statically resolved GetTypeFromHandle call  ----- BagFixed.ssc(51,13)
    stack1o := TypeObject(BagFixed);
    // ----- local unpack  ----- BagFixed.ssc(51,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: BagFixed && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block9248;

  block9248:
    // ----- load field  ----- BagFixed.ssc(52,7)
    assert this != null;
    stack0i := $Heap[this, BagFixed.count];
    // ----- load field  ----- BagFixed.ssc(52,7)
    assert this != null;
    stack1o := $Heap[this, BagFixed.elems];
    // ----- unary operator  ----- BagFixed.ssc(52,7)
    assert stack1o != null;
    stack1i := $Length(stack1o);
    // ----- unary operator  ----- BagFixed.ssc(52,7)
    stack1i := $IntToInt(stack1i, System.UIntPtr, System.Int32);
    // ----- binary operator  ----- BagFixed.ssc(52,7)
    // ----- branch  ----- BagFixed.ssc(52,7)
    goto true9248to9282, false9248to9265;

  true9248to9282:
    assume stack0i != stack1i;
    goto block9282;

  false9248to9265:
    assume stack0i == stack1i;
    goto block9265;

  block9282:
    // ----- load field  ----- BagFixed.ssc(58,7)
    assert this != null;
    stack0o := $Heap[this, BagFixed.elems];
    // ----- load field  ----- BagFixed.ssc(58,7)
    assert this != null;
    stack1i := $Heap[this, BagFixed.count];
    // ----- store element  ----- BagFixed.ssc(58,7)
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]);
    $Heap[stack0o, $elements] := IntArraySet($Heap[stack0o, $elements], stack1i, x);
    assume IsHeap($Heap);
    // ----- load field  ----- BagFixed.ssc(59,7)
    assert this != null;
    local4 := $Heap[this, BagFixed.count];
    // ----- load constant 1  ----- BagFixed.ssc(59,7)
    stack0i := 1;
    // ----- binary operator  ----- BagFixed.ssc(59,7)
    stack0i := local4 + stack0i;
    // ----- store field  ----- BagFixed.ssc(59,7)
    assert this != null;
    assert $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
    havoc temp2;
    $Heap[this, $exposeVersion] := temp2;
    $Heap[this, BagFixed.count] := stack0i;
    assert !($Heap[this, $inv] <: BagFixed && $Heap[this, $localinv] != $BaseClass(BagFixed)) || 0 <= $Heap[this, BagFixed.count];
    assert !($Heap[this, $inv] <: BagFixed && $Heap[this, $localinv] != $BaseClass(BagFixed)) || $Heap[this, BagFixed.count] <= $Length($Heap[this, BagFixed.elems]);
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local4;
    // ----- branch
    goto block9469;

  block9265:
    // ----- load constant 2  ----- BagFixed.ssc(54,16)
    stack0i := 2;
    // ----- load field  ----- BagFixed.ssc(54,16)
    assert this != null;
    stack1o := $Heap[this, BagFixed.elems];
    // ----- unary operator  ----- BagFixed.ssc(54,16)
    assert stack1o != null;
    stack1i := $Length(stack1o);
    // ----- unary operator  ----- BagFixed.ssc(54,16)
    stack1i := $IntToInt(stack1i, System.UIntPtr, System.Int32);
    // ----- binary operator  ----- BagFixed.ssc(54,16)
    stack0i := stack0i * stack1i;
    // ----- load constant 1  ----- BagFixed.ssc(54,16)
    stack1i := 1;
    // ----- binary operator  ----- BagFixed.ssc(54,16)
    stack0i := stack0i + stack1i;
    // ----- new array  ----- BagFixed.ssc(54,16)
    assert 0 <= stack0i;
    havoc temp3;
    assume $Heap[temp3, $allocated] == false && $Length(temp3) == stack0i;
    assume $Heap[$ElementProxy(temp3, -1), $allocated] == false && $ElementProxy(temp3, -1) != temp3 && $ElementProxy(temp3, -1) != null;
    assume temp3 != null;
    assume $typeof(temp3) == IntArray(System.Int32, 1);
    assume $Heap[temp3, $ownerRef] == temp3 && $Heap[temp3, $ownerFrame] == $PeerGroupPlaceholder;
    assume $Heap[$ElementProxy(temp3, -1), $ownerRef] == $ElementProxy(temp3, -1) && $Heap[$ElementProxy(temp3, -1), $ownerFrame] == $PeerGroupPlaceholder;
    assume $Heap[temp3, $inv] == $typeof(temp3) && $Heap[temp3, $localinv] == $typeof(temp3);
    assume (forall $i: int :: IntArrayGet($Heap[temp3, $elements], $i) == 0);
    $Heap[temp3, $allocated] := true;
    call System.Object..ctor($ElementProxy(temp3, -1));
    b := temp3;
    assume IsHeap($Heap);
    // ----- load field  ----- BagFixed.ssc(55,9)
    assert this != null;
    stack0o := $Heap[this, BagFixed.elems];
    // ----- load constant 0  ----- BagFixed.ssc(55,9)
    stack1i := 0;
    // ----- copy  ----- BagFixed.ssc(55,9)
    stack2o := b;
    // ----- load constant 0  ----- BagFixed.ssc(55,9)
    stack3i := 0;
    // ----- load field  ----- BagFixed.ssc(55,9)
    assert this != null;
    stack4o := $Heap[this, BagFixed.elems];
    // ----- unary operator  ----- BagFixed.ssc(55,9)
    assert stack4o != null;
    stack4i := $Length(stack4o);
    // ----- unary operator  ----- BagFixed.ssc(55,9)
    stack4i := $IntToInt(stack4i, System.UIntPtr, System.Int32);
    // ----- call  ----- BagFixed.ssc(55,9)
    call System.Array.Copy$System.Array$notnull$System.Int32$System.Array$notnull$System.Int32$System.Int32(stack0o, stack1i, stack2o, stack3i, stack4i);
    // ----- store field  ----- BagFixed.ssc(56,9)
    assert this != null;
    assert $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
    assert ($Heap[b, $ownerRef] == this && $Heap[b, $ownerFrame] == BagFixed) || $Heap[b, $ownerFrame] == $PeerGroupPlaceholder;
    assert $Heap[b, $ownerFrame] == $PeerGroupPlaceholder && $Heap[this, $inv] <: BagFixed && $Heap[this, $localinv] != $BaseClass(BagFixed) ==> (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[b, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[b, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
    assert $Heap[b, $ownerFrame] == $PeerGroupPlaceholder && $Heap[this, $inv] <: BagFixed && $Heap[this, $localinv] != $BaseClass(BagFixed) ==> $Heap[this, $ownerRef] != $Heap[b, $ownerRef] || $Heap[this, $ownerFrame] != $Heap[b, $ownerFrame];
    call $UpdateOwnersForRep(this, BagFixed, b);
    havoc temp4;
    $Heap[this, $exposeVersion] := temp4;
    $Heap[this, BagFixed.elems] := b;
    assert !($Heap[this, $inv] <: BagFixed && $Heap[this, $localinv] != $BaseClass(BagFixed)) || 0 <= $Heap[this, BagFixed.count];
    assert !($Heap[this, $inv] <: BagFixed && $Heap[this, $localinv] != $BaseClass(BagFixed)) || $Heap[this, BagFixed.count] <= $Length($Heap[this, BagFixed.elems]);
    assume IsHeap($Heap);
    goto block9282;

  block9469:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true9469to9486, false9469to9401;

  true9469to9486:
    assume local2 == stack0o;
    goto block9486;

  false9469to9401:
    assume local2 != stack0o;
    goto block9401;

  block9486:
    // ----- load token  ----- BagFixed.ssc(60,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, BagFixed);
    // ----- statically resolved GetTypeFromHandle call  ----- BagFixed.ssc(60,5)
    stack0o := TypeObject(BagFixed);
    // ----- local pack  ----- BagFixed.ssc(60,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, BagFixed.count];
    assert $Heap[temp0, BagFixed.count] <= $Length($Heap[temp0, BagFixed.elems]);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == BagFixed ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block9435;

  block9401:
    // ----- is instance
    // ----- branch
    goto true9401to9486, false9401to9367;

  true9401to9486:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block9486;

  false9401to9367:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block9367;

  block9367:
    // ----- branch
    goto block9435;

  block9435:
    // ----- nop
    // ----- branch
    goto block9333;

  block9333:
    // ----- return
    return;
}



procedure BagFixed..cctor();
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



implementation BagFixed..cctor()
{

  entry:
    goto block10608;

  block10608:
    goto block10625;

  block10625:
    // ----- nop
    // ----- return
    return;
}


