// Spec# program verifier version 0.90, Copyright (c) 2003-2008, Microsoft.
// Command Line Options: /print:SubclassWithInvariant.bpl main.exe

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

const unique N.B.x: <int>name;

const unique N.C.y: <int>name;

const unique System.Reflection.ICustomAttributeProvider: name;

const unique System.Reflection.IReflect: name;

const unique System.ICloneable: name;

const unique System.Collections.Generic.IEnumerable`1...System.Char: name;

const unique N.M: name;

const unique System.Runtime.Serialization.ISerializable: name;

const unique System.IConvertible: name;

const unique System.Reflection.MemberInfo: name;

const unique Microsoft.Contracts.GuardException: name;

const unique System.Collections.IEnumerable: name;

const unique System.Exception: name;

const unique System.Runtime.InteropServices._MemberInfo: name;

const unique System.Runtime.InteropServices._Exception: name;

const unique System.IComparable`1...System.String: name;

const unique System.Runtime.InteropServices._Type: name;

const unique Microsoft.Contracts.ObjectInvariantException: name;

const unique Microsoft.Contracts.ICheckedException: name;

const unique N.B: name;

const unique N.C: name;

const unique System.IEquatable`1...System.String: name;

const unique System.IComparable: name;

axiom !IsStaticField(N.B.x);

axiom IncludeInMainFrameCondition(N.B.x);

axiom $IncludedInModifiesStar(N.B.x);

axiom DeclType(N.B.x) == N.B;

axiom AsRangeField(N.B.x, System.Int32) == N.B.x;

axiom !IsStaticField(N.C.y);

axiom IncludeInMainFrameCondition(N.C.y);

axiom $IncludedInModifiesStar(N.C.y);

axiom DeclType(N.C.y) == N.C;

axiom AsRangeField(N.C.y, System.Int32) == N.C.y;

axiom N.B <: N.B;

axiom $BaseClass(N.B) == System.Object && AsDirectSubClass(N.B, $BaseClass(N.B)) == N.B;

axiom !$IsImmutable(N.B) && $AsMutable(N.B) == N.B;

// N.B object invariant
axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: N.B } IsHeap($h) && $h[$oi, $inv] <: N.B && $h[$oi, $localinv] != $BaseClass(N.B) ==> $h[$oi, N.B.x] >= 0);

procedure N.B.SpecSharp.CheckInvariant$System.Boolean(this: ref where $IsNotNull(this, N.B) && $Heap[this, $allocated], throwException$in: bool where true) returns ($result: bool where true);
  // user-declared preconditions
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this) && (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == N.B ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
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



implementation N.B.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool) returns ($result: bool)
{
  var throwException: bool where true, stack0i: int, stack1i: int, stack0b: bool, return.value: bool where true, stack50000o: ref, stack0o: ref, SS$Display.Return.Local: bool where true;

  entry:
    throwException := throwException$in;
    goto block1751;

  block1751:
    goto block1887;

  block1887:
    // ----- nop
    // ----- load field
    assert this != null;
    stack0i := $Heap[this, N.B.x];
    // ----- load constant 0
    stack1i := 0;
    // ----- binary operator
    // ----- branch
    goto true1887to1938, false1887to1955;

  true1887to1938:
    assume stack0i >= stack1i;
    goto block1938;

  false1887to1955:
    assume stack0i < stack1i;
    goto block1955;

  block1938:
    // ----- load constant 1
    return.value := true;
    // ----- branch
    goto block1768;

  block1955:
    // ----- copy
    stack0b := throwException;
    // ----- unary operator
    // ----- branch
    goto true1955to1921, false1955to1853;

  true1955to1921:
    assume !stack0b;
    goto block1921;

  false1955to1853:
    assume stack0b;
    goto block1853;

  block1921:
    // ----- load constant 0
    return.value := false;
    // ----- branch
    goto block1768;

  block1853:
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

  block1768:
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



procedure N.B.F$System.Int32(this: ref where $IsNotNull(this, N.B) && $Heap[this, $allocated], i$in: int where InRange(i$in, System.Int32)) returns ($result: int where InRange($result, System.Int32));
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



implementation N.B.F$System.Int32(this: ref, i$in: int) returns ($result: int)
{
  var i: int where InRange(i, System.Int32), temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception) && $Heap[local2, $allocated], temp2: exposeVersionType, stack0o: ref, stack0b: bool, stack0s: struct, return.value: int where InRange(return.value, System.Int32), SS$Display.Return.Local: int where InRange(SS$Display.Return.Local, System.Int32), stack0i: int;

  entry:
    i := i$in;
    goto block2754;

  block2754:
    goto block2907;

  block2907:
    // ----- nop
    // ----- FrameGuard processing  ----- main.ssc(10,15)
    temp0 := this;
    // ----- load token  ----- main.ssc(10,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, N.B);
    // ----- statically resolved GetTypeFromHandle call  ----- main.ssc(10,15)
    stack1o := TypeObject(N.B);
    // ----- local unpack  ----- main.ssc(10,15)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: N.B && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block2924;

  block2924:
    // ----- store field  ----- main.ssc(11,9)
    assert this != null;
    assert $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
    havoc temp2;
    $Heap[this, $exposeVersion] := temp2;
    $Heap[this, N.B.x] := i;
    assert !($Heap[this, $inv] <: N.B);
    assume IsHeap($Heap);
    // ----- branch
    goto block3077;

  block3077:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true3077to3111, false3077to3145;

  true3077to3111:
    assume local2 == stack0o;
    goto block3111;

  false3077to3145:
    assume local2 != stack0o;
    goto block3145;

  block3111:
    // ----- load token  ----- main.ssc(12,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, N.B);
    // ----- statically resolved GetTypeFromHandle call  ----- main.ssc(12,7)
    stack0o := TypeObject(N.B);
    // ----- local pack  ----- main.ssc(12,7)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert $Heap[temp0, N.B.x] >= 0;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == N.B ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block3060;

  block3145:
    // ----- is instance
    // ----- branch
    goto true3145to3111, false3145to3043;

  true3145to3111:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block3111;

  false3145to3043:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block3043;

  block3043:
    // ----- branch
    goto block3060;

  block3060:
    // ----- nop
    // ----- branch
    goto block2975;

  block2975:
    // ----- load field  ----- main.ssc(13,7)
    assert this != null;
    return.value := $Heap[this, N.B.x];
    // ----- branch
    goto block2992;

  block2992:
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0i := return.value;
    // ----- return
    $result := stack0i;
    return;
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

axiom Microsoft.Contracts.ICheckedException <: Microsoft.Contracts.ICheckedException;

axiom Microsoft.Contracts.ICheckedException <: System.Object;

axiom $IsMemberlessType(Microsoft.Contracts.ICheckedException);

axiom $AsInterface(Microsoft.Contracts.ICheckedException) == Microsoft.Contracts.ICheckedException;

procedure N.B..ctor(this: ref where $IsNotNull(this, N.B) && $Heap[this, $allocated]);
  // object is fully unpacked:  this.inv == Object
  free requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
  // nothing is owned by [this,*] and 'this' is alone in its own peer group
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this) && $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires $BeingConstructed == this;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // target object is allocated upon return
  free ensures $Heap[this, $allocated];
  // target object is additively exposable for N.B
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == N.B && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(N.B <: DeclType($f))) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] && $o != this ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation N.B..ctor(this: ref)
{
  var temp0: ref;

  entry:
    assume $Heap[this, N.B.x] == 0;
    goto block3859;

  block3859:
    goto block3893;

  block3893:
    // ----- call  ----- main.ssc(6,16)
    assert this != null;
    call System.Object..ctor(this);
    goto block3944;

  block3944:
    // ----- FrameGuard processing  ----- main.ssc(6,16)
    temp0 := this;
    // ----- classic pack  ----- main.ssc(6,16)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert $Heap[temp0, N.B.x] >= 0;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == N.B ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := N.B;
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



procedure N.B..cctor();
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



implementation N.B..cctor()
{

  entry:
    goto block4199;

  block4199:
    goto block4267;

  block4267:
    // ----- nop
    // ----- return
    return;
}



axiom N.C <: N.C;

axiom $BaseClass(N.C) == N.B && AsDirectSubClass(N.C, $BaseClass(N.C)) == N.C;

axiom !$IsImmutable(N.C) && $AsMutable(N.C) == N.C;

// N.C object invariant
axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: N.C } IsHeap($h) && $h[$oi, $inv] <: N.C && $h[$oi, $localinv] != $BaseClass(N.C) ==> $h[$oi, N.B.x] < $h[$oi, N.C.y]);

procedure N.C.SpecSharp.CheckInvariant$System.Boolean(this: ref where $IsNotNull(this, N.C) && $Heap[this, $allocated], throwException$in: bool where true) returns ($result: bool where true);
  // user-declared preconditions
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == N.B && $Heap[this, $localinv] == $typeof(this) && (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == N.C ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
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



implementation N.C.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool) returns ($result: bool)
{
  var throwException: bool where true, stack0i: int, stack1i: int, stack0b: bool, return.value: bool where true, stack50000o: ref, stack0o: ref, SS$Display.Return.Local: bool where true;

  entry:
    throwException := throwException$in;
    goto block4641;

  block4641:
    goto block4692;

  block4692:
    // ----- nop
    // ----- load field
    assert this != null;
    stack0i := $Heap[this, N.B.x];
    // ----- load field
    assert this != null;
    stack1i := $Heap[this, N.C.y];
    // ----- binary operator
    // ----- branch
    goto true4692to4794, false4692to4675;

  true4692to4794:
    assume stack0i < stack1i;
    goto block4794;

  false4692to4675:
    assume stack0i >= stack1i;
    goto block4675;

  block4794:
    // ----- load constant 1
    return.value := true;
    // ----- branch
    goto block4709;

  block4675:
    // ----- copy
    stack0b := throwException;
    // ----- unary operator
    // ----- branch
    goto true4675to4811, false4675to4845;

  true4675to4811:
    assume !stack0b;
    goto block4811;

  false4675to4845:
    assume stack0b;
    goto block4845;

  block4811:
    // ----- load constant 0
    return.value := false;
    // ----- branch
    goto block4709;

  block4845:
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

  block4709:
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0b := return.value;
    // ----- return
    $result := stack0b;
    return;
}



procedure N.C..ctor(this: ref where $IsNotNull(this, N.C) && $Heap[this, $allocated]);
  // object is fully unpacked:  this.inv == Object
  free requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
  // nothing is owned by [this,*] and 'this' is alone in its own peer group
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this) && $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires $BeingConstructed == this;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // target object is allocated upon return
  free ensures $Heap[this, $allocated];
  // target object is additively exposable for N.C
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == N.C && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(N.C <: DeclType($f))) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] && $o != this ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation N.C..ctor(this: ref)
{
  var stack0i: int, stack1i: int, temp0: exposeVersionType, temp1: ref;

  entry:
    assume $Heap[this, N.C.y] == 0;
    goto block5355;

  block5355:
    goto block5423;

  block5423:
    // ----- call  ----- main.ssc(20,16)
    assert this != null;
    call N.B..ctor(this);
    goto block5440;

  block5440:
    // ----- load field  ----- main.ssc(20,18)
    assert this != null;
    stack0i := $Heap[this, N.B.x];
    // ----- load constant 1  ----- main.ssc(20,18)
    stack1i := 1;
    // ----- binary operator  ----- main.ssc(20,18)
    stack0i := stack0i + stack1i;
    // ----- store field  ----- main.ssc(20,18)
    assert this != null;
    assert $Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]);
    havoc temp0;
    $Heap[this, $exposeVersion] := temp0;
    $Heap[this, N.C.y] := stack0i;
    assert !($Heap[this, $inv] <: N.C && $Heap[this, $localinv] != $BaseClass(N.C)) || $Heap[this, N.B.x] < $Heap[this, N.C.y];
    assume IsHeap($Heap);
    // ----- FrameGuard processing  ----- main.ssc(20,28)
    temp1 := this;
    // ----- classic pack  ----- main.ssc(20,28)
    assert temp1 != null;
    assert $Heap[temp1, $inv] == N.B && $Heap[temp1, $localinv] == $typeof(temp1);
    assert $Heap[temp1, N.B.x] < $Heap[temp1, N.C.y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == temp1 && $Heap[$p, $ownerFrame] == N.C ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp1, $inv] := N.C;
    assume IsHeap($Heap);
    // ----- return  ----- main.ssc(20,28)
    return;
}



procedure N.C.F$System.Int32(this: ref where $IsNotNull(this, N.C) && $Heap[this, $allocated], i$in: int where InRange(i$in, System.Int32)) returns ($result: int where InRange($result, System.Int32));
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



implementation N.C.F$System.Int32(this: ref, i$in: int) returns ($result: int)
{
  var i: int where InRange(i, System.Int32), temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception) && $Heap[local2, $allocated], stack0i: int, stack0o: ref, stack1i: int, stack2i: int, stack1b: bool, temp2: exposeVersionType, stack0b: bool, stack0s: struct, return.value: int where InRange(return.value, System.Int32), SS$Display.Return.Local: int where InRange(SS$Display.Return.Local, System.Int32);

  entry:
    i := i$in;
    goto block6120;

  block6120:
    goto block6273;

  block6273:
    // ----- nop
    // ----- FrameGuard processing  ----- main.ssc(22,15)
    temp0 := this;
    // ----- load token  ----- main.ssc(22,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, N.C);
    // ----- statically resolved GetTypeFromHandle call  ----- main.ssc(22,15)
    stack1o := TypeObject(N.C);
    // ----- local unpack  ----- main.ssc(22,15)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: N.C && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := N.B;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block6290;

  block6290:
    // ----- copy  ----- main.ssc(23,9)
    stack0i := i;
    // ----- call  ----- main.ssc(23,9)
    assert this != null;
    call stack0i := N.B.F$System.Int32(this, stack0i);
    // ----- copy
    stack0o := this;
    // ----- load field  ----- main.ssc(24,9)
    assert this != null;
    stack1i := $Heap[this, N.B.x];
    // ----- load constant 2  ----- main.ssc(24,9)
    stack2i := 2;
    // ----- binary operator  ----- main.ssc(24,9)
    assert stack2i != 0;
    stack1i := stack1i % stack2i;
    // ----- load constant 0  ----- main.ssc(24,9)
    stack2i := 0;
    // ----- binary operator  ----- main.ssc(24,9)
    // ----- branch  ----- main.ssc(24,9)
    goto true6290to6324, false6290to6307;

  true6290to6324:
    assume stack1i != stack2i;
    goto block6324;

  false6290to6307:
    assume stack1i == stack2i;
    goto block6307;

  block6324:
    // ----- copy
    stack1i := i;
    goto block6341;

  block6307:
    // ----- load constant 1
    stack1i := 1;
    // ----- binary operator
    stack1i := i + stack1i;
    // ----- branch
    goto block6341;

  block6341:
    // ----- store field
    assert stack0o != null;
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]);
    havoc temp2;
    $Heap[stack0o, $exposeVersion] := temp2;
    $Heap[stack0o, N.C.y] := stack1i;
    assert !($Heap[stack0o, $inv] <: N.C && $Heap[stack0o, $localinv] != $BaseClass(N.C)) || $Heap[stack0o, N.B.x] < $Heap[stack0o, N.C.y];
    assume IsHeap($Heap);
    // ----- branch
    goto block6477;

  block6477:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true6477to6528, false6477to6511;

  true6477to6528:
    assume local2 == stack0o;
    goto block6528;

  false6477to6511:
    assume local2 != stack0o;
    goto block6511;

  block6528:
    // ----- load token  ----- main.ssc(25,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, N.C);
    // ----- statically resolved GetTypeFromHandle call  ----- main.ssc(25,7)
    stack0o := TypeObject(N.C);
    // ----- local pack  ----- main.ssc(25,7)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == N.B;
    assert $Heap[temp0, N.B.x] < $Heap[temp0, N.C.y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == N.C ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block6494;

  block6511:
    // ----- is instance
    // ----- branch
    goto true6511to6528, false6511to6562;

  true6511to6528:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block6528;

  false6511to6562:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block6562;

  block6562:
    // ----- branch
    goto block6494;

  block6494:
    // ----- nop
    // ----- branch
    goto block6392;

  block6392:
    // ----- load field  ----- main.ssc(26,7)
    assert this != null;
    return.value := $Heap[this, N.C.y];
    // ----- branch
    goto block6409;

  block6409:
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0i := return.value;
    // ----- return
    $result := stack0i;
    return;
}



procedure N.C..cctor();
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



implementation N.C..cctor()
{

  entry:
    goto block7463;

  block7463:
    goto block7514;

  block7514:
    // ----- nop
    // ----- return
    return;
}



axiom N.M <: N.M;

axiom $BaseClass(N.M) == System.Object && AsDirectSubClass(N.M, $BaseClass(N.M)) == N.M;

axiom !$IsImmutable(N.M) && $AsMutable(N.M) == N.M;

// N.M object invariant
axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: N.M } IsHeap($h) && $h[$oi, $inv] <: N.M && $h[$oi, $localinv] != $BaseClass(N.M) ==> true);

procedure N.M.ApplyFtoB$N.B$notnull$System.Int32(b$in: ref where $IsNotNull(b$in, N.B) && $Heap[b$in, $allocated], i$in: int where InRange(i$in, System.Int32));
  // b is peer consistent
  requires (forall $pc: ref :: { $typeof($pc) } { $Heap[$pc, $localinv] } { $Heap[$pc, $inv] } { $Heap[$pc, $ownerFrame] } { $Heap[$pc, $ownerRef] } $pc != null && $Heap[$pc, $allocated] && $Heap[$pc, $ownerRef] == $Heap[b$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[b$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // b is peer consistent (owner must not be valid)
  requires $Heap[b$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[b$in, $ownerRef], $inv] <: $Heap[b$in, $ownerFrame]) || $Heap[$Heap[b$in, $ownerRef], $localinv] == $BaseClass($Heap[b$in, $ownerFrame]);
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



implementation N.M.ApplyFtoB$N.B$notnull$System.Int32(b$in: ref, i$in: int)
{
  var b: ref where $IsNotNull(b, N.B) && $Heap[b, $allocated], i: int where InRange(i, System.Int32), stack0i: int;

  entry:
    b := b$in;
    i := i$in;
    goto block7701;

  block7701:
    goto block7718;

  block7718:
    // ----- copy  ----- main.ssc(31,41)
    stack0i := i;
    // ----- call  ----- main.ssc(31,41)
    assert b != null;
    call stack0i := N.B.F$System.Int32$.Virtual.$(b, stack0i);
    // ----- call  ----- main.ssc(31,41)
    call System.Console.WriteLine$System.Int32(stack0i);
    // ----- return  ----- main.ssc(31,75)
    return;
}



procedure N.B.F$System.Int32$.Virtual.$(this: ref where $IsNotNull(this, N.B) && $Heap[this, $allocated], i$in: int where InRange(i$in, System.Int32)) returns ($result: int where InRange($result, System.Int32));
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



procedure System.Console.WriteLine$System.Int32(value$in: int where InRange(value$in, System.Int32));
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



procedure N.M.ApplyFtoC$N.C$notnull$System.Int32(c$in: ref where $IsNotNull(c$in, N.C) && $Heap[c$in, $allocated], i$in: int where InRange(i$in, System.Int32));
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
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation N.M.ApplyFtoC$N.C$notnull$System.Int32(c$in: ref, i$in: int)
{
  var c: ref where $IsNotNull(c, N.C) && $Heap[c, $allocated], i: int where InRange(i, System.Int32), stack0i: int;

  entry:
    c := c$in;
    i := i$in;
    goto block7905;

  block7905:
    goto block7922;

  block7922:
    // ----- copy  ----- main.ssc(32,41)
    stack0i := i;
    // ----- call  ----- main.ssc(32,41)
    assert c != null;
    call stack0i := N.C.F$System.Int32$.Virtual.$(c, stack0i);
    // ----- call  ----- main.ssc(32,41)
    call System.Console.WriteLine$System.Int32(stack0i);
    // ----- return  ----- main.ssc(32,75)
    return;
}



procedure N.C.F$System.Int32$.Virtual.$(this: ref where $IsNotNull(this, N.C) && $Heap[this, $allocated], i$in: int where InRange(i$in, System.Int32)) returns ($result: int where InRange($result, System.Int32));
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



procedure N.M.Main();
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



implementation N.M.Main()
{
  var stack50000o: ref, stack0o: ref, b: ref where $Is(b, N.B) && $Heap[b, $allocated], c: ref where $Is(c, N.C) && $Heap[c, $allocated], arg: int where InRange(arg, System.Int32), stack1i: int;

  entry:
    goto block8160;

  block8160:
    goto block8211;

  block8211:
    // ----- new object  ----- main.ssc(34,10)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == N.B;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    // ----- call  ----- main.ssc(34,10)
    assert stack50000o != null;
    call N.B..ctor(stack50000o);
    // ----- copy  ----- main.ssc(34,10)
    stack0o := stack50000o;
    // ----- copy  ----- main.ssc(34,10)
    b := stack0o;
    // ----- new object  ----- main.ssc(35,10)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == N.C;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    // ----- call  ----- main.ssc(35,10)
    assert stack50000o != null;
    call N.C..ctor(stack50000o);
    // ----- copy  ----- main.ssc(35,10)
    stack0o := stack50000o;
    // ----- copy  ----- main.ssc(35,10)
    c := stack0o;
    // ----- load constant 3  ----- main.ssc(38,11)
    arg := 3;
    goto block8228;

  block8228:
    // ----- copy  ----- main.ssc(40,9)
    stack0o := b;
    // ----- copy  ----- main.ssc(40,9)
    stack1i := arg;
    // ----- call  ----- main.ssc(40,9)
    call N.M.ApplyFtoB$N.B$notnull$System.Int32(stack0o, stack1i);
    // ----- load constant "A"  ----- main.ssc(41,9)
    stack0o := $stringLiteral0;
    // ----- call  ----- main.ssc(41,9)
    call System.Console.WriteLine$System.String(stack0o);
    // ----- copy  ----- main.ssc(42,9)
    stack0o := c;
    // ----- copy  ----- main.ssc(42,9)
    stack1i := arg;
    // ----- call  ----- main.ssc(42,9)
    call N.M.ApplyFtoB$N.B$notnull$System.Int32(stack0o, stack1i);
    // ----- load constant "B"  ----- main.ssc(43,9)
    stack0o := $stringLiteral1;
    // ----- call  ----- main.ssc(43,9)
    call System.Console.WriteLine$System.String(stack0o);
    // ----- copy  ----- main.ssc(44,9)
    stack0o := c;
    // ----- copy  ----- main.ssc(44,9)
    stack1i := arg;
    // ----- call  ----- main.ssc(44,9)
    call N.M.ApplyFtoC$N.C$notnull$System.Int32(stack0o, stack1i);
    // ----- load constant "C"  ----- main.ssc(45,9)
    stack0o := $stringLiteral2;
    // ----- call  ----- main.ssc(45,9)
    call System.Console.WriteLine$System.String(stack0o);
    // ----- branch
    goto block8194;

  block8194:
    // ----- return  ----- main.ssc(49,5)
    return;
}



axiom System.String <: System.String;

axiom $BaseClass(System.String) == System.Object && AsDirectSubClass(System.String, $BaseClass(System.String)) == System.String;

axiom $IsImmutable(System.String) && $AsImmutable(System.String) == System.String;

axiom System.IComparable <: System.IComparable;

axiom System.IComparable <: System.Object;

axiom $IsMemberlessType(System.IComparable);

axiom $AsInterface(System.IComparable) == System.IComparable;

axiom System.String <: System.IComparable;

axiom System.ICloneable <: System.ICloneable;

axiom System.ICloneable <: System.Object;

axiom $IsMemberlessType(System.ICloneable);

axiom $AsInterface(System.ICloneable) == System.ICloneable;

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

axiom System.Collections.IEnumerable <: System.Collections.IEnumerable;

axiom System.Collections.IEnumerable <: System.Object;

axiom $IsMemberlessType(System.Collections.IEnumerable);

axiom $AsInterface(System.Collections.IEnumerable) == System.Collections.IEnumerable;

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

procedure System.Console.WriteLine$System.String(value$in: ref where $Is(value$in, System.String) && $Heap[value$in, $allocated]);
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
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



procedure N.M..ctor(this: ref where $IsNotNull(this, N.M) && $Heap[this, $allocated]);
  // object is fully unpacked:  this.inv == Object
  free requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
  // nothing is owned by [this,*] and 'this' is alone in its own peer group
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this) && $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires $BeingConstructed == this;
  free requires $PurityAxiomsCanBeAssumed;
  modifies $Heap, $ActivityIndicator;
  // target object is allocated upon return
  free ensures $Heap[this, $allocated];
  // target object is additively exposable for N.M
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == N.M && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } $o != null && !old($Heap)[$o, $allocated] && $Heap[$o, $allocated] ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // frame condition
  ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } IncludeInMainFrameCondition($f) && $o != null && old($Heap)[$o, $allocated] && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(N.M <: DeclType($f))) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures $HeapSucc(old($Heap), $Heap);
  // inv/localinv change only in blocks
  free ensures (forall $o: ref :: { $Heap[$o, $localinv] } { $Heap[$o, $inv] } old($Heap)[$o, $allocated] && $o != this ==> old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]);
  free ensures (forall $o: ref :: { $Heap[$o, $allocated] } old($Heap)[$o, $allocated] ==> $Heap[$o, $allocated]) && (forall $ot: ref :: { $Heap[$ot, $ownerFrame] } { $Heap[$ot, $ownerRef] } old($Heap)[$ot, $allocated] && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: { $Heap[$o, $sharingMode] } $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation N.M..ctor(this: ref)
{

  entry:
    goto block9775;

  block9775:
    goto block9792;

  block9792:
    // ----- call  ----- main.ssc(30,16)
    assert this != null;
    call System.Object..ctor(this);
    // ----- return
    // ----- translation-inserted post-constructor pack
    assert this != null;
    assert $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == N.M ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[this, $inv] := N.M;
    assume IsHeap($Heap);
    return;
}



const unique $stringLiteral0: ref;

// $stringLiteral0 is allocated, interned, and has the appropriate type and length
axiom $IsNotNull($stringLiteral0, System.String) && $StringLength($stringLiteral0) == 1 && (forall heap: [ref,<x>name]x :: { heap[$stringLiteral0, $allocated] } IsHeap(heap) ==> heap[$stringLiteral0, $allocated]) && (forall heap: [ref,<x>name]x :: { #System.String.IsInterned$System.String$notnull(heap, $stringLiteral0) } IsHeap(heap) ==> #System.String.IsInterned$System.String$notnull(heap, $stringLiteral0) == $stringLiteral0);

const unique $stringLiteral1: ref;

// $stringLiteral1 is allocated, interned, and has the appropriate type and length
axiom $IsNotNull($stringLiteral1, System.String) && $StringLength($stringLiteral1) == 1 && (forall heap: [ref,<x>name]x :: { heap[$stringLiteral1, $allocated] } IsHeap(heap) ==> heap[$stringLiteral1, $allocated]) && (forall heap: [ref,<x>name]x :: { #System.String.IsInterned$System.String$notnull(heap, $stringLiteral1) } IsHeap(heap) ==> #System.String.IsInterned$System.String$notnull(heap, $stringLiteral1) == $stringLiteral1);

const unique $stringLiteral2: ref;

// $stringLiteral2 is allocated, interned, and has the appropriate type and length
axiom $IsNotNull($stringLiteral2, System.String) && $StringLength($stringLiteral2) == 1 && (forall heap: [ref,<x>name]x :: { heap[$stringLiteral2, $allocated] } IsHeap(heap) ==> heap[$stringLiteral2, $allocated]) && (forall heap: [ref,<x>name]x :: { #System.String.IsInterned$System.String$notnull(heap, $stringLiteral2) } IsHeap(heap) ==> #System.String.IsInterned$System.String$notnull(heap, $stringLiteral2) == $stringLiteral2);
