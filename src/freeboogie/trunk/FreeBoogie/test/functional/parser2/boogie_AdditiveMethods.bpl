type name;
type ref;
const unique null : ref;
type real;
type elements;
type struct;
type exposeVersionType;
var $Heap : <x>[ref, name]x where IsHeap($Heap);
function IsHeap(h : <x>[ref, name]x) returns ($$unnamed~a : bool);
const $allocated : name;
const $elements : name;
const $inv : name;
const $localinv : name;
const $exposeVersion : name;
axiom (DeclType($exposeVersion) == System.Object);
const $sharingMode : name;
const $SharingMode_Unshared : name;
const $SharingMode_LockProtected : name;
const $ownerRef : name;
const $ownerFrame : name;
const $PeerGroupPlaceholder : name;
function ClassRepr(class : name) returns ($$unnamed~b : ref);
axiom (forall c0 : name, c1 : name :: {ClassRepr(c0), ClassRepr(c1)} ((c0 != c1) ==> (ClassRepr(c0) != ClassRepr(c1))));
axiom (forall T : name :: !($typeof(ClassRepr(T)) <: System.Object));
axiom (forall T : name :: (ClassRepr(T) != null));
axiom (forall T : name, h : <x>[ref, name]x :: {h[ClassRepr(T), $ownerFrame]} (IsHeap(h) ==> (h[ClassRepr(T), $ownerFrame] == $PeerGroupPlaceholder)));
function IsDirectlyModifiableField(f : name) returns ($$unnamed~c : bool);
axiom !IsDirectlyModifiableField($allocated);
axiom IsDirectlyModifiableField($elements);
axiom !IsDirectlyModifiableField($inv);
axiom !IsDirectlyModifiableField($localinv);
axiom !IsDirectlyModifiableField($ownerRef);
axiom !IsDirectlyModifiableField($ownerFrame);
axiom !IsDirectlyModifiableField($exposeVersion);
function IsStaticField(f : name) returns ($$unnamed~d : bool);
axiom !IsStaticField($allocated);
axiom !IsStaticField($elements);
axiom !IsStaticField($inv);
axiom !IsStaticField($localinv);
axiom !IsStaticField($exposeVersion);
function ValueArrayGet<any>($$unnamed~f : elements, $$unnamed~e : int) returns ($$unnamed~g : any);
function ValueArraySet<any>($$unnamed~j : elements, $$unnamed~i : int, $$unnamed~h : any) returns ($$unnamed~k : elements);
function RefArrayGet($$unnamed~m : elements, $$unnamed~l : int) returns ($$unnamed~n : ref);
function RefArraySet($$unnamed~q : elements, $$unnamed~p : int, $$unnamed~o : ref) returns ($$unnamed~r : elements);
axiom (forall<any> A : elements, i : int, x : any :: (ValueArrayGet(ValueArraySet(A, i, x), i) == x));
axiom (forall<any> A : elements, i : int, j : int, x : any :: ((i != j) ==> (ValueArrayGet(ValueArraySet(A, i, x), j) == ValueArrayGet(A, j))));
axiom (forall A : elements, i : int, x : ref :: (RefArrayGet(RefArraySet(A, i, x), i) == x));
axiom (forall A : elements, i : int, j : int, x : ref :: ((i != j) ==> (RefArrayGet(RefArraySet(A, i, x), j) == RefArrayGet(A, j))));
function ArrayIndex(arr : ref, dim : int, indexAtDim : int, remainingIndexContribution : int) returns ($$unnamed~s : int);
axiom (forall a : ref, d : int, x : int, y : int, x' : int, y' : int :: {ArrayIndex(a, d, x, y), ArrayIndex(a, d, x', y')} ((ArrayIndex(a, d, x, y) == ArrayIndex(a, d, x', y')) ==> ((x == x') && (y == y'))));
axiom (forall a : ref, T : name, i : int, r : int, heap : <x>[ref, name]x :: {($typeof(a) <: RefArray(T, r)), RefArrayGet(heap[a, $elements], i)} ((IsHeap(heap) && ($typeof(a) <: RefArray(T, r))) ==> $Is(RefArrayGet(heap[a, $elements], i), T)));
axiom (forall a : ref, T : name, i : int, r : int, heap : <x>[ref, name]x :: {($typeof(a) <: NonNullRefArray(T, r)), RefArrayGet(heap[a, $elements], i)} ((IsHeap(heap) && ($typeof(a) <: NonNullRefArray(T, r))) ==> $IsNotNull(RefArrayGet(heap[a, $elements], i), T)));
function $Rank($$unnamed~t : ref) returns ($$unnamed~u : int);
axiom (forall a : ref :: (1 <= $Rank(a)));
axiom (forall a : ref, T : name, r : int :: {($typeof(a) <: RefArray(T, r))} (((a != null) && ($typeof(a) <: RefArray(T, r))) ==> ($Rank(a) == r)));
axiom (forall a : ref, T : name, r : int :: {($typeof(a) <: NonNullRefArray(T, r))} (((a != null) && ($typeof(a) <: NonNullRefArray(T, r))) ==> ($Rank(a) == r)));
axiom (forall a : ref, T : name, r : int :: {($typeof(a) <: ValueArray(T, r))} (((a != null) && ($typeof(a) <: ValueArray(T, r))) ==> ($Rank(a) == r)));
function $Length($$unnamed~v : ref) returns ($$unnamed~w : int);
axiom (forall a : ref :: {$Length(a)} (0 <= $Length(a)));
function $DimLength($$unnamed~y : ref, $$unnamed~x : int) returns ($$unnamed~z : int);
axiom (forall a : ref, i : int :: (0 <= $DimLength(a, i)));
axiom (forall a : ref :: {$DimLength(a, 0)} (($Rank(a) == 1) ==> ($DimLength(a, 0) == $Length(a))));
function $LBound($$unnamed~ab : ref, $$unnamed~aa : int) returns ($$unnamed~ac : int);
function $UBound($$unnamed~ae : ref, $$unnamed~ad : int) returns ($$unnamed~af : int);
axiom (forall a : ref, i : int :: {$LBound(a, i)} ($LBound(a, i) == 0));
axiom (forall a : ref, i : int :: {$UBound(a, i)} ($UBound(a, i) == ($DimLength(a, i) - 1)));
const $ArrayCategoryValue : name;
const $ArrayCategoryRef : name;
const $ArrayCategoryNonNullRef : name;
function $ArrayCategory(arrayType : name) returns (arrayCategory : name);
axiom (forall T : name, ET : name, r : int :: {(T <: ValueArray(ET, r))} ((T <: ValueArray(ET, r)) ==> ($ArrayCategory(T) == $ArrayCategoryValue)));
axiom (forall T : name, ET : name, r : int :: {(T <: RefArray(ET, r))} ((T <: RefArray(ET, r)) ==> ($ArrayCategory(T) == $ArrayCategoryRef)));
axiom (forall T : name, ET : name, r : int :: {(T <: NonNullRefArray(ET, r))} ((T <: NonNullRefArray(ET, r)) ==> ($ArrayCategory(T) == $ArrayCategoryNonNullRef)));
const System.Array : name;
axiom (System.Array <: System.Object);
function $ElementType($$unnamed~ag : name) returns ($$unnamed~ah : name);
function ValueArray(elementType : name, rank : int) returns ($$unnamed~ai : name);
axiom (forall T : name, r : int :: {ValueArray(T, r)} (ValueArray(T, r) <: System.Array));
function RefArray(elementType : name, rank : int) returns ($$unnamed~aj : name);
axiom (forall T : name, r : int :: {RefArray(T, r)} (RefArray(T, r) <: System.Array));
function NonNullRefArray(elementType : name, rank : int) returns ($$unnamed~ak : name);
axiom (forall T : name, r : int :: {NonNullRefArray(T, r)} (NonNullRefArray(T, r) <: System.Array));
axiom (forall T : name, U : name, r : int :: ((U <: T) ==> (RefArray(U, r) <: RefArray(T, r))));
axiom (forall T : name, U : name, r : int :: ((U <: T) ==> (NonNullRefArray(U, r) <: NonNullRefArray(T, r))));
axiom (forall A : name, r : int :: ($ElementType(ValueArray(A, r)) == A));
axiom (forall A : name, r : int :: ($ElementType(RefArray(A, r)) == A));
axiom (forall A : name, r : int :: ($ElementType(NonNullRefArray(A, r)) == A));
axiom (forall A : name, r : int, T : name :: {(T <: RefArray(A, r))} ((T <: RefArray(A, r)) ==> ((T == RefArray($ElementType(T), r)) && ($ElementType(T) <: A))));
axiom (forall A : name, r : int, T : name :: {(T <: NonNullRefArray(A, r))} ((T <: NonNullRefArray(A, r)) ==> ((T == NonNullRefArray($ElementType(T), r)) && ($ElementType(T) <: A))));
axiom (forall A : name, r : int, T : name :: {(T <: ValueArray(A, r))} ((T <: ValueArray(A, r)) ==> (T == ValueArray(A, r))));
axiom (forall A : name, r : int, T : name :: ((RefArray(A, r) <: T) ==> ((System.Array <: T) || ((T == RefArray($ElementType(T), r)) && (A <: $ElementType(T))))));
axiom (forall A : name, r : int, T : name :: ((NonNullRefArray(A, r) <: T) ==> ((System.Array <: T) || ((T == NonNullRefArray($ElementType(T), r)) && (A <: $ElementType(T))))));
axiom (forall A : name, r : int, T : name :: ((ValueArray(A, r) <: T) ==> ((System.Array <: T) || (T == ValueArray(A, r)))));
function $ArrayPtr(elementType : name) returns ($$unnamed~al : name);
function $StructGet<any>($$unnamed~an : struct, $$unnamed~am : name) returns ($$unnamed~ao : any);
function $StructSet<any>($$unnamed~ar : struct, $$unnamed~aq : name, $$unnamed~ap : any) returns ($$unnamed~as : struct);
axiom (forall<any> s : struct, f : name, x : any :: ($StructGet($StructSet(s, f, x), f) == x));
axiom (forall<any> s : struct, f : name, f' : name, x : any :: ((f != f') ==> ($StructGet($StructSet(s, f, x), f') == $StructGet(s, f'))));
function ZeroInit(s : struct, typ : name) returns ($$unnamed~at : bool);
function $typeof($$unnamed~au : ref) returns ($$unnamed~av : name);
function $BaseClass(sub : name) returns (base : name);
function AsDirectSubClass(sub : name, base : name) returns (sub' : name);
function OneClassDown(sub : name, base : name) returns (directSub : name);
axiom (forall A : name, B : name, C : name :: {(C <: AsDirectSubClass(B, A))} ((C <: AsDirectSubClass(B, A)) ==> (OneClassDown(C, A) == B)));
function $IsValueType($$unnamed~aw : name) returns ($$unnamed~ax : bool);
axiom (forall T : name :: ($IsValueType(T) ==> ((forall U : name :: ((T <: U) ==> (T == U))) && (forall U : name :: ((U <: T) ==> (T == U))))));
const System.Object : name;
function $IsTokenForType($$unnamed~az : struct, $$unnamed~ay : name) returns ($$unnamed~ba : bool);
function TypeObject($$unnamed~bb : name) returns ($$unnamed~bc : ref);
const System.Type : name;
axiom (System.Type <: System.Object);
axiom (forall T : name :: {TypeObject(T)} $IsNotNull(TypeObject(T), System.Type));
function TypeName($$unnamed~bd : ref) returns ($$unnamed~be : name);
axiom (forall T : name :: {TypeObject(T)} (TypeName(TypeObject(T)) == T));
function $Is($$unnamed~bg : ref, $$unnamed~bf : name) returns ($$unnamed~bh : bool);
axiom (forall o : ref, T : name :: {$Is(o, T)} ($Is(o, T) <==> ((o == null) || ($typeof(o) <: T))));
function $IsNotNull($$unnamed~bj : ref, $$unnamed~bi : name) returns ($$unnamed~bk : bool);
axiom (forall o : ref, T : name :: {$IsNotNull(o, T)} ($IsNotNull(o, T) <==> ((o != null) && $Is(o, T))));
function $As($$unnamed~bm : ref, $$unnamed~bl : name) returns ($$unnamed~bn : ref);
axiom (forall o : ref, T : name :: ($Is(o, T) ==> ($As(o, T) == o)));
axiom (forall o : ref, T : name :: (!$Is(o, T) ==> ($As(o, T) == null)));
axiom (forall h : <x>[ref, name]x, o : ref :: {($typeof(o) <: System.Array), h[o, $inv]} (((IsHeap(h) && (o != null)) && ($typeof(o) <: System.Array)) ==> ((h[o, $inv] == $typeof(o)) && (h[o, $localinv] == $typeof(o)))));
function IsAllocated<any>(h : <x>[ref, name]x, o : any) returns ($$unnamed~bo : bool);
axiom (forall h : <x>[ref, name]x, o : ref, f : name :: {IsAllocated(h, h[o, f])} ((IsHeap(h) && h[o, $allocated]) ==> IsAllocated(h, h[o, f])));
axiom (forall h : <x>[ref, name]x, o : ref, f : name :: {h[h[o, f], $allocated]} ((IsHeap(h) && h[o, $allocated]) ==> h[h[o, f], $allocated]));
axiom (forall h : <x>[ref, name]x, s : struct, f : name :: {IsAllocated(h, $StructGet(s, f))} (IsAllocated(h, s) ==> IsAllocated(h, $StructGet(s, f))));
axiom (forall h : <x>[ref, name]x, e : elements, i : int :: {IsAllocated(h, RefArrayGet(e, i))} (IsAllocated(h, e) ==> IsAllocated(h, RefArrayGet(e, i))));
axiom (forall h : <x>[ref, name]x, e : elements, i : int :: {IsAllocated(h, ValueArrayGet(e, i))} (IsAllocated(h, e) ==> IsAllocated(h, ValueArrayGet(e, i))));
axiom (forall h : <x>[ref, name]x, o : ref :: {h[o, $allocated]} (IsAllocated(h, o) ==> h[o, $allocated]));
axiom (forall h : <x>[ref, name]x, c : name :: {h[ClassRepr(c), $allocated]} (IsHeap(h) ==> h[ClassRepr(c), $allocated]));
const $BeingConstructed : ref;
const $NonNullFieldsAreInitialized : name;
function DeclType(field : name) returns (class : name);
function AsNonNullRefField(field : name, T : name) returns (f : name);
function AsRefField(field : name, T : name) returns (f : name);
function AsRangeField(field : name, T : name) returns (f : name);
axiom (forall f : name, T : name :: {AsNonNullRefField(f, T)} ((AsNonNullRefField(f, T) == f) ==> (AsRefField(f, T) == f)));
axiom (forall h : <x>[ref, name]x, o : ref, f : name, T : name :: {h[o, AsRefField(f, T)]} (IsHeap(h) ==> $Is(h[o, AsRefField(f, T)], T)));
axiom (forall h : <x>[ref, name]x, o : ref, f : name, T : name :: {h[o, AsNonNullRefField(f, T)]} (((IsHeap(h) && (o != null)) && ((o != $BeingConstructed) || (h[$BeingConstructed, $NonNullFieldsAreInitialized] == true))) ==> (h[o, AsNonNullRefField(f, T)] != null)));
axiom (forall h : <x>[ref, name]x, o : ref, f : name, T : name :: {h[o, AsRangeField(f, T)]} (IsHeap(h) ==> InRange(h[o, AsRangeField(f, T)], T)));
function $IsMemberlessType($$unnamed~bp : name) returns ($$unnamed~bq : bool);
axiom (forall o : ref :: {$IsMemberlessType($typeof(o))} !$IsMemberlessType($typeof(o)));
function $IsImmutable(T : name) returns ($$unnamed~br : bool);
axiom !$IsImmutable(System.Object);
function $AsImmutable(T : name) returns (theType : name);
function $AsMutable(T : name) returns (theType : name);
axiom (forall T : name, U : name :: {(U <: $AsImmutable(T))} ((U <: $AsImmutable(T)) ==> ($IsImmutable(U) && ($AsImmutable(U) == U))));
axiom (forall T : name, U : name :: {(U <: $AsMutable(T))} ((U <: $AsMutable(T)) ==> (!$IsImmutable(U) && ($AsMutable(U) == U))));
function AsOwner(string : ref, owner : ref) returns (theString : ref);
axiom (forall o : ref, T : name :: {($typeof(o) <: $AsImmutable(T))} ((((o != null) && (o != $BeingConstructed)) && ($typeof(o) <: $AsImmutable(T))) ==> (forall h : <x>[ref, name]x :: {IsHeap(h)} (IsHeap(h) ==> (((((h[o, $inv] == $typeof(o)) && (h[o, $localinv] == $typeof(o))) && (h[o, $ownerFrame] == $PeerGroupPlaceholder)) && (AsOwner(o, h[o, $ownerRef]) == o)) && (forall t : ref :: {AsOwner(o, h[t, $ownerRef])} ((AsOwner(o, h[t, $ownerRef]) == o) ==> ((t == o) || (h[t, $ownerFrame] != $PeerGroupPlaceholder)))))))));
const System.String : name;
function $StringLength($$unnamed~bs : ref) returns ($$unnamed~bt : int);
axiom (forall s : ref :: {$StringLength(s)} (0 <= $StringLength(s)));
function AsRepField(f : name, declaringType : name) returns (theField : name);
axiom (forall h : <x>[ref, name]x, o : ref, f : name, T : name :: {h[o, AsRepField(f, T)]} ((IsHeap(h) && (h[o, AsRepField(f, T)] != null)) ==> ((h[h[o, AsRepField(f, T)], $ownerRef] == o) && (h[h[o, AsRepField(f, T)], $ownerFrame] == T))));
function AsPeerField(f : name) returns (theField : name);
axiom (forall h : <x>[ref, name]x, o : ref, f : name :: {h[o, AsPeerField(f)]} ((IsHeap(h) && (h[o, AsPeerField(f)] != null)) ==> ((h[h[o, AsPeerField(f)], $ownerRef] == h[o, $ownerRef]) && (h[h[o, AsPeerField(f)], $ownerFrame] == h[o, $ownerFrame]))));
axiom (forall h : <x>[ref, name]x, o : ref :: {(h[h[o, $ownerRef], $inv] <: h[o, $ownerFrame])} ((((IsHeap(h) && (h[o, $ownerFrame] != $PeerGroupPlaceholder)) && (h[h[o, $ownerRef], $inv] <: h[o, $ownerFrame])) && (h[h[o, $ownerRef], $localinv] != $BaseClass(h[o, $ownerFrame]))) ==> ((h[o, $inv] == $typeof(o)) && (h[o, $localinv] == $typeof(o)))));
procedure $SetOwner(o : ref, ow : ref, fr : name);
  modifies $Heap;
  ensures (forall p : ref, F : name :: {$Heap[p, F]} (((((F != $ownerRef) && (F != $ownerFrame)) || old(($Heap[p, $ownerRef] != $Heap[o, $ownerRef]))) || old(($Heap[p, $ownerFrame] != $Heap[o, $ownerFrame]))) ==> (old($Heap[p, F]) == $Heap[p, F])));
  ensures (forall p : ref :: {$Heap[p, $ownerRef]} {$Heap[p, $ownerFrame]} ((old(($Heap[p, $ownerRef] == $Heap[o, $ownerRef])) && old(($Heap[p, $ownerFrame] == $Heap[o, $ownerFrame]))) ==> (($Heap[p, $ownerRef] == ow) && ($Heap[p, $ownerFrame] == fr))));
  

procedure $UpdateOwnersForRep(o : ref, T : name, e : ref);
  modifies $Heap;
  ensures (forall p : ref, F : name :: {$Heap[p, F]} (((((F != $ownerRef) && (F != $ownerFrame)) || old(($Heap[p, $ownerRef] != $Heap[e, $ownerRef]))) || old(($Heap[p, $ownerFrame] != $Heap[e, $ownerFrame]))) ==> (old($Heap[p, F]) == $Heap[p, F])));
  ensures ((e == null) ==> ($Heap == old($Heap)));
  ensures ((e != null) ==> (forall p : ref :: {$Heap[p, $ownerRef]} {$Heap[p, $ownerFrame]} ((old(($Heap[p, $ownerRef] == $Heap[e, $ownerRef])) && old(($Heap[p, $ownerFrame] == $Heap[e, $ownerFrame]))) ==> (($Heap[p, $ownerRef] == o) && ($Heap[p, $ownerFrame] == T)))));
  

procedure $UpdateOwnersForPeer(c : ref, d : ref);
  modifies $Heap;
  ensures (forall p : ref, F : name :: {$Heap[p, F]} ((((F != $ownerRef) && (F != $ownerFrame)) || old(((($Heap[p, $ownerRef] != $Heap[c, $ownerRef]) || ($Heap[p, $ownerFrame] != $Heap[c, $ownerFrame])) && (($Heap[p, $ownerRef] != $Heap[d, $ownerRef]) || ($Heap[p, $ownerFrame] != $Heap[d, $ownerFrame]))))) ==> (old($Heap[p, F]) == $Heap[p, F])));
  ensures ((d == null) ==> ($Heap == old($Heap)));
  ensures ((d != null) ==> (forall p : ref :: {$Heap[p, $ownerRef]} {$Heap[p, $ownerFrame]} (((old(($Heap[p, $ownerRef] == $Heap[c, $ownerRef])) && old(($Heap[p, $ownerFrame] == $Heap[c, $ownerFrame]))) || (old(($Heap[p, $ownerRef] == $Heap[d, $ownerRef])) && old(($Heap[p, $ownerFrame] == $Heap[d, $ownerFrame])))) ==> ((((old($Heap)[d, $ownerFrame] == $PeerGroupPlaceholder) && ($Heap[p, $ownerRef] == old($Heap)[c, $ownerRef])) && ($Heap[p, $ownerFrame] == old($Heap)[c, $ownerFrame])) || (((old($Heap)[d, $ownerFrame] != $PeerGroupPlaceholder) && ($Heap[p, $ownerRef] == old($Heap)[d, $ownerRef])) && ($Heap[p, $ownerFrame] == old($Heap)[d, $ownerFrame]))))));
  

const $FirstConsistentOwner : name;
function $AsPureObject($$unnamed~bu : ref) returns ($$unnamed~bv : ref);
function ##FieldDependsOnFCO<any>(o : ref, f : name, ev : exposeVersionType) returns (value : any);
axiom (forall o : ref, f : name, h : <x>[ref, name]x :: {h[$AsPureObject(o), f]} ((((((IsHeap(h) && (o != null)) && (h[o, $allocated] == true)) && (h[o, $ownerFrame] != $PeerGroupPlaceholder)) && (h[h[o, $ownerRef], $inv] <: h[o, $ownerFrame])) && (h[h[o, $ownerRef], $localinv] != $BaseClass(h[o, $ownerFrame]))) ==> (h[o, f] == ##FieldDependsOnFCO(o, f, h[h[o, $FirstConsistentOwner], $exposeVersion]))));
axiom (forall o : ref, h : <x>[ref, name]x :: {h[o, $FirstConsistentOwner]} ((((((IsHeap(h) && (o != null)) && (h[o, $allocated] == true)) && (h[o, $ownerFrame] != $PeerGroupPlaceholder)) && (h[h[o, $ownerRef], $inv] <: h[o, $ownerFrame])) && (h[h[o, $ownerRef], $localinv] != $BaseClass(h[o, $ownerFrame]))) ==> (((h[o, $FirstConsistentOwner] != null) && (h[h[o, $FirstConsistentOwner], $allocated] == true)) && (((h[h[o, $FirstConsistentOwner], $ownerFrame] == $PeerGroupPlaceholder) || !(h[h[h[o, $FirstConsistentOwner], $ownerRef], $inv] <: h[h[o, $FirstConsistentOwner], $ownerFrame])) || (h[h[h[o, $FirstConsistentOwner], $ownerRef], $localinv] == $BaseClass(h[h[o, $FirstConsistentOwner], $ownerFrame]))))));
function Box<any>($$unnamed~bx : any, $$unnamed~bw : ref) returns ($$unnamed~by : ref);
function Unbox<any>($$unnamed~bz : ref) returns ($$unnamed~ca : any);
axiom (forall<any> x : any, p : ref :: {Unbox(Box(x, p))} (Unbox(Box(x, p)) == x));
function UnboxedType($$unnamed~cb : ref) returns ($$unnamed~cc : name);
axiom (forall p : ref :: {$IsValueType(UnboxedType(p))} ($IsValueType(UnboxedType(p)) ==> (forall<any> heap : <x>[ref, name]x, x : any :: {heap[Box(x, p), $inv]} (IsHeap(heap) ==> ((heap[Box(x, p), $inv] == $typeof(Box(x, p))) && (heap[Box(x, p), $localinv] == $typeof(Box(x, p))))))));
axiom (forall<any> x : any, p : ref :: {(UnboxedType(Box(x, p)) <: System.Object)} (((UnboxedType(Box(x, p)) <: System.Object) && (Box(x, p) == p)) ==> (x == p)));
function BoxTester(p : ref, typ : name) returns ($$unnamed~cd : ref);
axiom (forall p : ref, typ : name :: {BoxTester(p, typ)} ((UnboxedType(p) == typ) <==> (BoxTester(p, typ) != null)));
const System.SByte : name;
axiom $IsValueType(System.SByte);
const System.Byte : name;
axiom $IsValueType(System.Byte);
const System.Int16 : name;
axiom $IsValueType(System.Int16);
const System.UInt16 : name;
axiom $IsValueType(System.UInt16);
const System.Int32 : name;
axiom $IsValueType(System.Int32);
const System.UInt32 : name;
axiom $IsValueType(System.UInt32);
const System.Int64 : name;
axiom $IsValueType(System.Int64);
const System.UInt64 : name;
axiom $IsValueType(System.UInt64);
const System.Char : name;
axiom $IsValueType(System.Char);
const int#m2147483648 : int;
const int#2147483647 : int;
const int#4294967295 : int;
const int#m9223372036854775808 : int;
const int#9223372036854775807 : int;
const int#18446744073709551615 : int;
axiom (int#m9223372036854775808 < int#m2147483648);
axiom (int#m2147483648 < (0 - 100000));
axiom (100000 < int#2147483647);
axiom (int#2147483647 < int#4294967295);
axiom (int#4294967295 < int#9223372036854775807);
axiom (int#9223372036854775807 < int#18446744073709551615);
function InRange(i : int, T : name) returns ($$unnamed~ce : bool);
axiom (forall i : int :: (InRange(i, System.SByte) <==> (((0 - 128) <= i) && (i < 128))));
axiom (forall i : int :: (InRange(i, System.Byte) <==> ((0 <= i) && (i < 256))));
axiom (forall i : int :: (InRange(i, System.Int16) <==> (((0 - 32768) <= i) && (i < 32768))));
axiom (forall i : int :: (InRange(i, System.UInt16) <==> ((0 <= i) && (i < 65536))));
axiom (forall i : int :: (InRange(i, System.Int32) <==> ((int#m2147483648 <= i) && (i <= int#2147483647))));
axiom (forall i : int :: (InRange(i, System.UInt32) <==> ((0 <= i) && (i <= int#4294967295))));
axiom (forall i : int :: (InRange(i, System.Int64) <==> ((int#m9223372036854775808 <= i) && (i <= int#9223372036854775807))));
axiom (forall i : int :: (InRange(i, System.UInt64) <==> ((0 <= i) && (i <= int#18446744073709551615))));
axiom (forall i : int :: (InRange(i, System.Char) <==> ((0 <= i) && (i < 65536))));
function $IntToInt(val : int, fromType : name, toType : name) returns ($$unnamed~cf : int);
function $IntToReal($$unnamed~cg : int, fromType : name, toType : name) returns ($$unnamed~ch : real);
function $RealToInt($$unnamed~ci : real, fromType : name, toType : name) returns ($$unnamed~cj : int);
function $RealToReal(val : real, fromType : name, toType : name) returns ($$unnamed~ck : real);
function $SizeIs($$unnamed~cm : name, $$unnamed~cl : int) returns ($$unnamed~cn : bool);
function $IfThenElse<any>($$unnamed~cq : bool, $$unnamed~cp : any, $$unnamed~co : any) returns ($$unnamed~cr : any);
axiom (forall<any> b : bool, x : any, y : any :: {$IfThenElse(b, x, y)} (b ==> ($IfThenElse(b, x, y) == x)));
axiom (forall<any> b : bool, x : any, y : any :: {$IfThenElse(b, x, y)} (!b ==> ($IfThenElse(b, x, y) == y)));
function #neg($$unnamed~cs : int) returns ($$unnamed~ct : int);
function #and($$unnamed~cv : int, $$unnamed~cu : int) returns ($$unnamed~cw : int);
function #or($$unnamed~cy : int, $$unnamed~cx : int) returns ($$unnamed~cz : int);
function #xor($$unnamed~db : int, $$unnamed~da : int) returns ($$unnamed~dc : int);
function #shl($$unnamed~de : int, $$unnamed~dd : int) returns ($$unnamed~df : int);
function #shr($$unnamed~dh : int, $$unnamed~dg : int) returns ($$unnamed~di : int);
function #rneg($$unnamed~dj : real) returns ($$unnamed~dk : real);
function #radd($$unnamed~dm : real, $$unnamed~dl : real) returns ($$unnamed~dn : real);
function #rsub($$unnamed~dp : real, $$unnamed~do : real) returns ($$unnamed~dq : real);
function #rmul($$unnamed~ds : real, $$unnamed~dr : real) returns ($$unnamed~dt : real);
function #rdiv($$unnamed~dv : real, $$unnamed~du : real) returns ($$unnamed~dw : real);
function #rmod($$unnamed~dy : real, $$unnamed~dx : real) returns ($$unnamed~dz : real);
function #rLess($$unnamed~eb : real, $$unnamed~ea : real) returns ($$unnamed~ec : bool);
function #rAtmost($$unnamed~ee : real, $$unnamed~ed : real) returns ($$unnamed~ef : bool);
function #rEq($$unnamed~eh : real, $$unnamed~eg : real) returns ($$unnamed~ei : bool);
function #rNeq($$unnamed~ek : real, $$unnamed~ej : real) returns ($$unnamed~el : bool);
function #rAtleast($$unnamed~en : real, $$unnamed~em : real) returns ($$unnamed~eo : bool);
function #rGreater($$unnamed~eq : real, $$unnamed~ep : real) returns ($$unnamed~er : bool);
axiom (forall x : int, y : int :: {(x % y)} {(x / y)} ((x % y) == (x - ((x / y) * y))));
axiom (forall x : int, y : int :: {(x % y)} (((0 <= x) && (0 < y)) ==> ((0 <= (x % y)) && ((x % y) < y))));
axiom (forall x : int, y : int :: {(x % y)} (((0 <= x) && (y < 0)) ==> ((0 <= (x % y)) && ((x % y) < (0 - y)))));
axiom (forall x : int, y : int :: {(x % y)} (((x <= 0) && (0 < y)) ==> (((0 - y) < (x % y)) && ((x % y) <= 0))));
axiom (forall x : int, y : int :: {(x % y)} (((x <= 0) && (y < 0)) ==> ((y < (x % y)) && ((x % y) <= 0))));
axiom (forall x : int, y : int :: {((x + y) % y)} (((0 <= x) && (0 <= y)) ==> (((x + y) % y) == (x % y))));
axiom (forall x : int, y : int :: {((y + x) % y)} (((0 <= x) && (0 <= y)) ==> (((y + x) % y) == (x % y))));
axiom (forall x : int, y : int :: {((x - y) % y)} (((0 <= (x - y)) && (0 <= y)) ==> (((x - y) % y) == (x % y))));
axiom (forall a : int, b : int, d : int :: {(a % d), (b % d)} ((((2 <= d) && ((a % d) == (b % d))) && (a < b)) ==> ((a + d) <= b)));
axiom (forall x : int, y : int :: {#and(x, y)} (((0 <= x) || (0 <= y)) ==> (0 <= #and(x, y))));
axiom (forall x : int, y : int :: {#or(x, y)} (((0 <= x) && (0 <= y)) ==> ((0 <= #or(x, y)) && (#or(x, y) <= (x + y)))));
axiom (forall i : int :: {#shl(i, 0)} (#shl(i, 0) == i));
axiom (forall i : int, j : int :: ((0 <= j) ==> (#shl(i, (j + 1)) == (#shl(i, j) * 2))));
axiom (forall i : int :: {#shr(i, 0)} (#shr(i, 0) == i));
axiom (forall i : int, j : int :: ((0 <= j) ==> (#shr(i, (j + 1)) == (#shr(i, j) / 2))));
function #System.String.IsInterned$System.String$notnull($$unnamed~es : ref) returns ($$unnamed~et : ref);
function #System.String.Equals$System.String($$unnamed~ev : ref, $$unnamed~eu : ref) returns ($$unnamed~ew : bool);
function #System.String.Equals$System.String$System.String($$unnamed~ey : ref, $$unnamed~ex : ref) returns ($$unnamed~ez : bool);
axiom (forall a : ref, b : ref :: {#System.String.Equals$System.String(a, b)} (#System.String.Equals$System.String(a, b) == #System.String.Equals$System.String$System.String(a, b)));
axiom (forall a : ref, b : ref :: {#System.String.Equals$System.String$System.String(a, b)} (#System.String.Equals$System.String$System.String(a, b) == #System.String.Equals$System.String$System.String(b, a)));
axiom (forall a : ref, b : ref :: {#System.String.Equals$System.String$System.String(a, b)} ((((a != null) && (b != null)) && #System.String.Equals$System.String$System.String(a, b)) ==> (#System.String.IsInterned$System.String$notnull(a) == #System.String.IsInterned$System.String$notnull(b))));
const $UnknownRef : ref;
const OwnedResults.x : name;
const AdditiveMethods.amPeer : name;
const AdditiveMethods.amRep : name;
const OwnedResults.y : name;
const OwnedResults : name;
const System.Runtime.InteropServices._Type : name;
const System.Runtime.InteropServices._MemberInfo : name;
const System.Reflection.IReflect : name;
const Sub : name;
const System.Reflection.ICustomAttributeProvider : name;
const System.Boolean : name;
const AdditiveMethods : name;
const T : name;
const System.Reflection.MemberInfo : name;
axiom !IsStaticField(AdditiveMethods.amPeer);
axiom IsDirectlyModifiableField(AdditiveMethods.amPeer);
axiom (AsPeerField(AdditiveMethods.amPeer) == AdditiveMethods.amPeer);
axiom (DeclType(AdditiveMethods.amPeer) == AdditiveMethods);
axiom (AsRefField(AdditiveMethods.amPeer, AdditiveMethods) == AdditiveMethods.amPeer);
axiom !IsStaticField(AdditiveMethods.amRep);
axiom IsDirectlyModifiableField(AdditiveMethods.amRep);
axiom (AsRepField(AdditiveMethods.amRep, AdditiveMethods) == AdditiveMethods.amRep);
axiom (DeclType(AdditiveMethods.amRep) == AdditiveMethods);
axiom (AsRefField(AdditiveMethods.amRep, AdditiveMethods) == AdditiveMethods.amRep);
function #OwnedResults.Mz($$unnamed~fb : <x>[ref, name]x, $$unnamed~fa : ref) returns ($$unnamed~fc : ref);
axiom !IsStaticField(OwnedResults.x);
axiom IsDirectlyModifiableField(OwnedResults.x);
axiom (AsRepField(OwnedResults.x, OwnedResults) == OwnedResults.x);
axiom (DeclType(OwnedResults.x) == OwnedResults);
axiom (AsRefField(OwnedResults.x, T) == OwnedResults.x);
function #OwnedResults.Pz($$unnamed~fe : <x>[ref, name]x, $$unnamed~fd : ref) returns ($$unnamed~ff : ref);
function ##OwnedResults.Pz($$unnamed~fg : exposeVersionType) returns ($$unnamed~fh : ref);
function #OwnedResults.Pw($$unnamed~fj : <x>[ref, name]x, $$unnamed~fi : ref) returns ($$unnamed~fk : ref);
function ##OwnedResults.Pw($$unnamed~fl : exposeVersionType) returns ($$unnamed~fm : ref);
axiom !IsStaticField(OwnedResults.y);
axiom IsDirectlyModifiableField(OwnedResults.y);
axiom (AsPeerField(OwnedResults.y) == OwnedResults.y);
axiom (DeclType(OwnedResults.y) == OwnedResults);
axiom (AsRefField(OwnedResults.y, T) == OwnedResults.y);
function #OwnedResults.Qz$System.Int32($$unnamed~fp : <x>[ref, name]x, $$unnamed~fo : ref, $$unnamed~fn : int) returns ($$unnamed~fq : ref);
function ##OwnedResults.Qz$System.Int32($$unnamed~fs : exposeVersionType, $$unnamed~fr : int) returns ($$unnamed~ft : ref);
function #OwnedResults.Static0($$unnamed~fu : <x>[ref, name]x) returns ($$unnamed~fv : ref);
function #OwnedResults.Static1($$unnamed~fw : <x>[ref, name]x) returns ($$unnamed~fx : ref);
function #OwnedResults.Static2() returns ($$unnamed~fy : ref);
axiom (AdditiveMethods <: AdditiveMethods);
axiom ($BaseClass(AdditiveMethods) == System.Object);
axiom ((AdditiveMethods <: $BaseClass(AdditiveMethods)) && (AsDirectSubClass(AdditiveMethods, $BaseClass(AdditiveMethods)) == AdditiveMethods));
axiom (!$IsImmutable(AdditiveMethods) && ($AsMutable(AdditiveMethods) == AdditiveMethods));
procedure AdditiveMethods.M(this : ref);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation AdditiveMethods.M(this : ref) {
  var stack0o : ref;
  var stack1o : ref;
  var stack0b : bool;
  entry: assume $IsNotNull(this, AdditiveMethods); goto $$entry~a;
  $$entry~a: assume ($Heap[this, $allocated] == true); goto block1734;
  block1734: goto block1751;
  block1751: assert (this != null); goto $$block1751~b;
  $$block1751~b: stack0o := $Heap[this, AdditiveMethods.amPeer]; goto $$block1751~a;
  $$block1751~a: stack1o := null; goto true1751to1785, false1751to1768;
  true1751to1785: assume (stack0o == stack1o); goto block1785;
  false1751to1768: assume (stack0o != stack1o); goto block1768;
  block1785: return;
  block1768: assert (this != null); goto $$block1768~k;
  $$block1768~k: stack0o := $Heap[this, AdditiveMethods.amPeer]; goto $$block1768~j;
  $$block1768~j: assert (stack0o != null); goto $$block1768~i;
  $$block1768~i: call AdditiveMethods.M(stack0o); goto $$block1768~h;
  $$block1768~h: assert (this != null); goto $$block1768~g;
  $$block1768~g: stack0o := $Heap[this, AdditiveMethods.amPeer]; goto $$block1768~f;
  $$block1768~f: assert (stack0o != null); goto $$block1768~e;
  $$block1768~e: call AdditiveMethods.Y$.Virtual.$(stack0o); goto $$block1768~d;
  $$block1768~d: assert (this != null); goto $$block1768~c;
  $$block1768~c: stack0o := $Heap[this, AdditiveMethods.amPeer]; goto $$block1768~b;
  $$block1768~b: assert (stack0o != null); goto $$block1768~a;
  $$block1768~a: call AdditiveMethods.Z$.Virtual.$(stack0o); goto block1785;
  
}

procedure AdditiveMethods.Y$.Virtual.$(this : ref);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

procedure AdditiveMethods.Z$.Virtual.$(this : ref);
  requires ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == $typeof(this))) && ($Heap[this, $localinv] == $typeof(this)));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

procedure AdditiveMethods.N(this : ref);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation AdditiveMethods.N(this : ref) {
  var stack0o : ref;
  var stack1o : ref;
  var stack0b : bool;
  var local0 : ref where $Is(local0, AdditiveMethods);
  var stack1s : struct;
  var temp0 : exposeVersionType;
  entry: assume $IsNotNull(this, AdditiveMethods); goto $$entry~b;
  $$entry~b: assume ($Heap[this, $allocated] == true); goto block2465;
  block2465: goto block2533;
  block2533: assert (this != null); goto $$block2533~b;
  $$block2533~b: stack0o := $Heap[this, AdditiveMethods.amRep]; goto $$block2533~a;
  $$block2533~a: stack1o := null; goto true2533to2584, false2533to2550;
  true2533to2584: assume (stack0o == stack1o); goto block2584;
  false2533to2550: assume (stack0o != stack1o); goto block2550;
  block2584: return;
  block2550: local0 := this; goto $$block2550~j;
  $$block2550~j: stack0o := local0; goto $$block2550~i;
  $$block2550~i: havoc stack1s; goto $$block2550~h;
  $$block2550~h: assume $IsTokenForType(stack1s, AdditiveMethods); goto $$block2550~g;
  $$block2550~g: stack1o := TypeObject(AdditiveMethods); goto $$block2550~f;
  $$block2550~f: assert (stack0o != null); goto $$block2550~e;
  $$block2550~e: assert ((((($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame])) || ($Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]))) && ($Heap[stack0o, $inv] <: AdditiveMethods)) && ($Heap[stack0o, $localinv] == $typeof(stack0o))); goto $$block2550~d;
  $$block2550~d: $Heap := $Heap[stack0o, $localinv := System.Object]; goto $$block2550~c;
  $$block2550~c: havoc temp0; goto $$block2550~b;
  $$block2550~b: $Heap := $Heap[stack0o, $exposeVersion := temp0]; goto $$block2550~a;
  $$block2550~a: assume IsHeap($Heap); goto block2567;
  block2567: assert (this != null); goto $$block2567~k;
  $$block2567~k: stack0o := $Heap[this, AdditiveMethods.amRep]; goto $$block2567~j;
  $$block2567~j: assert (stack0o != null); goto $$block2567~i;
  $$block2567~i: call AdditiveMethods.M(stack0o); goto $$block2567~h;
  $$block2567~h: assert (this != null); goto $$block2567~g;
  $$block2567~g: stack0o := $Heap[this, AdditiveMethods.amRep]; goto $$block2567~f;
  $$block2567~f: assert (stack0o != null); goto $$block2567~e;
  $$block2567~e: call AdditiveMethods.Y$.Virtual.$(stack0o); goto $$block2567~d;
  $$block2567~d: assert (this != null); goto $$block2567~c;
  $$block2567~c: stack0o := $Heap[this, AdditiveMethods.amRep]; goto $$block2567~b;
  $$block2567~b: assert (stack0o != null); goto $$block2567~a;
  $$block2567~a: call AdditiveMethods.Z$.Virtual.$(stack0o); goto block2618;
  block2618: stack0o := local0; goto $$block2618~h;
  $$block2618~h: havoc stack1s; goto $$block2618~g;
  $$block2618~g: assume $IsTokenForType(stack1s, AdditiveMethods); goto $$block2618~f;
  $$block2618~f: stack1o := TypeObject(AdditiveMethods); goto $$block2618~e;
  $$block2618~e: assert (stack0o != null); goto $$block2618~d;
  $$block2618~d: assert ($Heap[stack0o, $localinv] == System.Object); goto $$block2618~c;
  $$block2618~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == stack0o)) && ($Heap[$p, $ownerFrame] == AdditiveMethods)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block2618~b;
  $$block2618~b: $Heap := $Heap[stack0o, $localinv := $typeof(stack0o)]; goto $$block2618~a;
  $$block2618~a: assume IsHeap($Heap); goto block2584;
  
}

axiom (System.Type <: System.Type);
axiom (System.Reflection.MemberInfo <: System.Reflection.MemberInfo);
axiom ($BaseClass(System.Reflection.MemberInfo) == System.Object);
axiom ((System.Reflection.MemberInfo <: $BaseClass(System.Reflection.MemberInfo)) && (AsDirectSubClass(System.Reflection.MemberInfo, $BaseClass(System.Reflection.MemberInfo)) == System.Reflection.MemberInfo));
axiom ($IsImmutable(System.Reflection.MemberInfo) && ($AsImmutable(System.Reflection.MemberInfo) == System.Reflection.MemberInfo));
axiom (System.Reflection.ICustomAttributeProvider <: System.Object);
axiom $IsMemberlessType(System.Reflection.ICustomAttributeProvider);
axiom (System.Reflection.MemberInfo <: System.Reflection.ICustomAttributeProvider);
axiom (System.Runtime.InteropServices._MemberInfo <: System.Object);
axiom $IsMemberlessType(System.Runtime.InteropServices._MemberInfo);
axiom (System.Reflection.MemberInfo <: System.Runtime.InteropServices._MemberInfo);
axiom $IsMemberlessType(System.Reflection.MemberInfo);
axiom ($BaseClass(System.Type) == System.Reflection.MemberInfo);
axiom ((System.Type <: $BaseClass(System.Type)) && (AsDirectSubClass(System.Type, $BaseClass(System.Type)) == System.Type));
axiom ($IsImmutable(System.Type) && ($AsImmutable(System.Type) == System.Type));
axiom (System.Runtime.InteropServices._Type <: System.Object);
axiom $IsMemberlessType(System.Runtime.InteropServices._Type);
axiom (System.Type <: System.Runtime.InteropServices._Type);
axiom (System.Reflection.IReflect <: System.Object);
axiom $IsMemberlessType(System.Reflection.IReflect);
axiom (System.Type <: System.Reflection.IReflect);
axiom $IsMemberlessType(System.Type);
procedure AdditiveMethods.Y(this : ref);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation AdditiveMethods.Y(this : ref) {
  entry: assume $IsNotNull(this, AdditiveMethods); goto $$entry~c;
  $$entry~c: assume ($Heap[this, $allocated] == true); goto block3145;
  block3145: goto block3162;
  block3162: assert (this != null); goto $$block3162~c;
  $$block3162~c: call AdditiveMethods.M(this); goto $$block3162~b;
  $$block3162~b: assert (this != null); goto $$block3162~a;
  $$block3162~a: call AdditiveMethods.Z$.Virtual.$(this); return;
  
}

procedure AdditiveMethods.Z(this : ref);
  requires ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == AdditiveMethods)) && ($Heap[this, $localinv] == $typeof(this)));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation AdditiveMethods.Z(this : ref) {
  entry: assume $IsNotNull(this, AdditiveMethods); goto $$entry~d;
  $$entry~d: assume ($Heap[this, $allocated] == true); goto block3349;
  block3349: goto block3366;
  block3366: assert (this != null); goto $$block3366~a;
  $$block3366~a: call AdditiveMethods.M(this); return;
  
}

procedure AdditiveMethods.X0(this : ref);
  requires ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == AdditiveMethods)) && ($Heap[this, $localinv] == $typeof(this)));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation AdditiveMethods.X0(this : ref) {
  entry: assume $IsNotNull(this, AdditiveMethods); goto $$entry~e;
  $$entry~e: assume ($Heap[this, $allocated] == true); goto block3536;
  block3536: goto block3553;
  block3553: assert (this != null); goto $$block3553~a;
  $$block3553~a: call AdditiveMethods.Y$.Virtual.$(this); return;
  
}

procedure AdditiveMethods.X1(this : ref);
  requires ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == AdditiveMethods)) && ($Heap[this, $localinv] == $typeof(this)));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation AdditiveMethods.X1(this : ref) {
  entry: assume $IsNotNull(this, AdditiveMethods); goto $$entry~f;
  $$entry~f: assume ($Heap[this, $allocated] == true); goto block3723;
  block3723: goto block3740;
  block3740: assert (this != null); goto $$block3740~a;
  $$block3740~a: call AdditiveMethods.Z$.Virtual.$(this); return;
  
}

procedure AdditiveMethods..ctor(this : ref);
  free requires (forall $o : ref :: (($o != this) ==> ($Heap[$o, $ownerRef] != this)));
  free requires (($Heap[this, $ownerRef] == this) && ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder));
  free requires (forall $o : ref :: ((($Heap[$o, $ownerRef] == $Heap[this, $ownerRef]) && ($Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame])) ==> ($o == this)));
  free requires ($BeingConstructed == this);
  modifies $Heap;
  ensures ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == AdditiveMethods)) && ($Heap[this, $localinv] == $typeof(this)));
  ensures (($Heap[this, $ownerRef] == old($Heap)[this, $ownerRef]) && ($Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame]));
  ensures ($Heap[this, $sharingMode] == $SharingMode_Unshared);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(AdditiveMethods <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

implementation AdditiveMethods..ctor(this : ref) {
  entry: assume $IsNotNull(this, AdditiveMethods); goto $$entry~j;
  $$entry~j: assume ($Heap[this, $allocated] == true); goto $$entry~i;
  $$entry~i: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto $$entry~h;
  $$entry~h: assume ($Heap[this, AdditiveMethods.amPeer] == null); goto $$entry~g;
  $$entry~g: assume ($Heap[this, AdditiveMethods.amRep] == null); goto block3910;
  block3910: goto block3927;
  block3927: assert (this != null); goto $$block3927~f;
  $$block3927~f: call System.Object..ctor(this); goto $$block3927~e;
  $$block3927~e: assert (this != null); goto $$block3927~d;
  $$block3927~d: assert (($Heap[this, $inv] == System.Object) && ($Heap[this, $localinv] == $typeof(this))); goto $$block3927~c;
  $$block3927~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == AdditiveMethods)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block3927~b;
  $$block3927~b: $Heap := $Heap[this, $inv := AdditiveMethods]; goto $$block3927~a;
  $$block3927~a: assume IsHeap($Heap); return;
  
}

procedure System.Object..ctor(this : ref);
  free requires (forall $o : ref :: (($o != this) ==> ($Heap[$o, $ownerRef] != this)));
  free requires (($Heap[this, $ownerRef] == this) && ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder));
  free requires (forall $o : ref :: ((($Heap[$o, $ownerRef] == $Heap[this, $ownerRef]) && ($Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame])) ==> ($o == this)));
  free requires ($BeingConstructed == this);
  modifies $Heap;
  ensures ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this)));
  ensures (($Heap[this, $ownerRef] == old($Heap)[this, $ownerRef]) && ($Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame]));
  ensures ($Heap[this, $sharingMode] == $SharingMode_Unshared);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(System.Object <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

axiom (Sub <: Sub);
axiom ($BaseClass(Sub) == AdditiveMethods);
axiom ((Sub <: $BaseClass(Sub)) && (AsDirectSubClass(Sub, $BaseClass(Sub)) == Sub));
axiom (!$IsImmutable(Sub) && ($AsMutable(Sub) == Sub));
procedure Sub.Y(this : ref);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Sub.Y(this : ref) {
  var local0 : ref where $Is(local0, Sub);
  var stack0o : ref;
  var stack1s : struct;
  var stack1o : ref;
  var temp0 : exposeVersionType;
  entry: assume $IsNotNull(this, Sub); goto $$entry~k;
  $$entry~k: assume ($Heap[this, $allocated] == true); goto block4165;
  block4165: goto block4233;
  block4233: assert (this != null); goto $$block4233~n;
  $$block4233~n: call AdditiveMethods.M(this); goto $$block4233~m;
  $$block4233~m: assert (this != null); goto $$block4233~l;
  $$block4233~l: call AdditiveMethods.Y(this); goto $$block4233~k;
  $$block4233~k: local0 := this; goto $$block4233~j;
  $$block4233~j: stack0o := local0; goto $$block4233~i;
  $$block4233~i: havoc stack1s; goto $$block4233~h;
  $$block4233~h: assume $IsTokenForType(stack1s, Sub); goto $$block4233~g;
  $$block4233~g: stack1o := TypeObject(Sub); goto $$block4233~f;
  $$block4233~f: assert (stack0o != null); goto $$block4233~e;
  $$block4233~e: assert ((((($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame])) || ($Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]))) && ($Heap[stack0o, $inv] == Sub)) && ($Heap[stack0o, $localinv] == $typeof(stack0o))); goto $$block4233~d;
  $$block4233~d: $Heap := $Heap[stack0o, $inv := AdditiveMethods]; goto $$block4233~c;
  $$block4233~c: havoc temp0; goto $$block4233~b;
  $$block4233~b: $Heap := $Heap[stack0o, $exposeVersion := temp0]; goto $$block4233~a;
  $$block4233~a: assume IsHeap($Heap); goto block4250;
  block4250: goto block4301;
  block4301: stack0o := local0; goto $$block4301~h;
  $$block4301~h: havoc stack1s; goto $$block4301~g;
  $$block4301~g: assume $IsTokenForType(stack1s, Sub); goto $$block4301~f;
  $$block4301~f: stack1o := TypeObject(Sub); goto $$block4301~e;
  $$block4301~e: assert (stack0o != null); goto $$block4301~d;
  $$block4301~d: assert (($Heap[stack0o, $inv] == AdditiveMethods) && ($Heap[stack0o, $localinv] == $typeof(stack0o))); goto $$block4301~c;
  $$block4301~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == stack0o)) && ($Heap[$p, $ownerFrame] == Sub)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block4301~b;
  $$block4301~b: $Heap := $Heap[stack0o, $inv := Sub]; goto $$block4301~a;
  $$block4301~a: assume IsHeap($Heap); goto block4267;
  block4267: return;
  
}

procedure Sub.P(this : ref);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Sub.P(this : ref) {
  var local0 : ref where $Is(local0, Sub);
  var stack0o : ref;
  var stack1s : struct;
  var stack1o : ref;
  var temp0 : exposeVersionType;
  entry: assume $IsNotNull(this, Sub); goto $$entry~l;
  $$entry~l: assume ($Heap[this, $allocated] == true); goto block4760;
  block4760: goto block4828;
  block4828: local0 := this; goto $$block4828~j;
  $$block4828~j: stack0o := local0; goto $$block4828~i;
  $$block4828~i: havoc stack1s; goto $$block4828~h;
  $$block4828~h: assume $IsTokenForType(stack1s, Sub); goto $$block4828~g;
  $$block4828~g: stack1o := TypeObject(Sub); goto $$block4828~f;
  $$block4828~f: assert (stack0o != null); goto $$block4828~e;
  $$block4828~e: assert ((((($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame])) || ($Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]))) && ($Heap[stack0o, $inv] <: Sub)) && ($Heap[stack0o, $localinv] == $typeof(stack0o))); goto $$block4828~d;
  $$block4828~d: $Heap := $Heap[stack0o, $localinv := AdditiveMethods]; goto $$block4828~c;
  $$block4828~c: havoc temp0; goto $$block4828~b;
  $$block4828~b: $Heap := $Heap[stack0o, $exposeVersion := temp0]; goto $$block4828~a;
  $$block4828~a: assume IsHeap($Heap); goto block4845;
  block4845: assert (this != null); goto $$block4845~a;
  $$block4845~a: call AdditiveMethods.M(this); goto block4896;
  block4896: stack0o := local0; goto $$block4896~h;
  $$block4896~h: havoc stack1s; goto $$block4896~g;
  $$block4896~g: assume $IsTokenForType(stack1s, Sub); goto $$block4896~f;
  $$block4896~f: stack1o := TypeObject(Sub); goto $$block4896~e;
  $$block4896~e: assert (stack0o != null); goto $$block4896~d;
  $$block4896~d: assert ($Heap[stack0o, $localinv] == AdditiveMethods); goto $$block4896~c;
  $$block4896~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == stack0o)) && ($Heap[$p, $ownerFrame] == Sub)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block4896~b;
  $$block4896~b: $Heap := $Heap[stack0o, $localinv := $typeof(stack0o)]; goto $$block4896~a;
  $$block4896~a: assume IsHeap($Heap); goto block4862;
  block4862: return;
  
}

procedure Sub.Q(this : ref);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Sub.Q(this : ref) {
  var local0 : ref where $Is(local0, Sub);
  var stack0o : ref;
  var stack1s : struct;
  var stack1o : ref;
  var temp0 : exposeVersionType;
  entry: assume $IsNotNull(this, Sub); goto $$entry~m;
  $$entry~m: assume ($Heap[this, $allocated] == true); goto block5338;
  block5338: goto block5406;
  block5406: local0 := this; goto $$block5406~j;
  $$block5406~j: stack0o := local0; goto $$block5406~i;
  $$block5406~i: havoc stack1s; goto $$block5406~h;
  $$block5406~h: assume $IsTokenForType(stack1s, Sub); goto $$block5406~g;
  $$block5406~g: stack1o := TypeObject(Sub); goto $$block5406~f;
  $$block5406~f: assert (stack0o != null); goto $$block5406~e;
  $$block5406~e: assert ((((($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame])) || ($Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]))) && ($Heap[stack0o, $inv] <: Sub)) && ($Heap[stack0o, $localinv] == $typeof(stack0o))); goto $$block5406~d;
  $$block5406~d: $Heap := $Heap[stack0o, $localinv := AdditiveMethods]; goto $$block5406~c;
  $$block5406~c: havoc temp0; goto $$block5406~b;
  $$block5406~b: $Heap := $Heap[stack0o, $exposeVersion := temp0]; goto $$block5406~a;
  $$block5406~a: assume IsHeap($Heap); goto block5423;
  block5423: assert (this != null); goto $$block5423~a;
  $$block5423~a: call AdditiveMethods.Y(this); goto block5474;
  block5474: stack0o := local0; goto $$block5474~h;
  $$block5474~h: havoc stack1s; goto $$block5474~g;
  $$block5474~g: assume $IsTokenForType(stack1s, Sub); goto $$block5474~f;
  $$block5474~f: stack1o := TypeObject(Sub); goto $$block5474~e;
  $$block5474~e: assert (stack0o != null); goto $$block5474~d;
  $$block5474~d: assert ($Heap[stack0o, $localinv] == AdditiveMethods); goto $$block5474~c;
  $$block5474~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == stack0o)) && ($Heap[$p, $ownerFrame] == Sub)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block5474~b;
  $$block5474~b: $Heap := $Heap[stack0o, $localinv := $typeof(stack0o)]; goto $$block5474~a;
  $$block5474~a: assume IsHeap($Heap); goto block5440;
  block5440: return;
  
}

procedure Sub.Z(this : ref);
  requires ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == Sub)) && ($Heap[this, $localinv] == $typeof(this)));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Sub.Z(this : ref) {
  var local0 : ref where $Is(local0, Sub);
  var stack0o : ref;
  var stack1s : struct;
  var stack1o : ref;
  var temp0 : exposeVersionType;
  entry: assume $IsNotNull(this, Sub); goto $$entry~n;
  $$entry~n: assume ($Heap[this, $allocated] == true); goto block5916;
  block5916: goto block5984;
  block5984: local0 := this; goto $$block5984~j;
  $$block5984~j: stack0o := local0; goto $$block5984~i;
  $$block5984~i: havoc stack1s; goto $$block5984~h;
  $$block5984~h: assume $IsTokenForType(stack1s, Sub); goto $$block5984~g;
  $$block5984~g: stack1o := TypeObject(Sub); goto $$block5984~f;
  $$block5984~f: assert (stack0o != null); goto $$block5984~e;
  $$block5984~e: assert ((((($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame])) || ($Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]))) && ($Heap[stack0o, $inv] == Sub)) && ($Heap[stack0o, $localinv] == $typeof(stack0o))); goto $$block5984~d;
  $$block5984~d: $Heap := $Heap[stack0o, $inv := AdditiveMethods]; goto $$block5984~c;
  $$block5984~c: havoc temp0; goto $$block5984~b;
  $$block5984~b: $Heap := $Heap[stack0o, $exposeVersion := temp0]; goto $$block5984~a;
  $$block5984~a: assume IsHeap($Heap); goto block6001;
  block6001: assert (this != null); goto $$block6001~a;
  $$block6001~a: call AdditiveMethods.Z(this); goto block6052;
  block6052: stack0o := local0; goto $$block6052~h;
  $$block6052~h: havoc stack1s; goto $$block6052~g;
  $$block6052~g: assume $IsTokenForType(stack1s, Sub); goto $$block6052~f;
  $$block6052~f: stack1o := TypeObject(Sub); goto $$block6052~e;
  $$block6052~e: assert (stack0o != null); goto $$block6052~d;
  $$block6052~d: assert (($Heap[stack0o, $inv] == AdditiveMethods) && ($Heap[stack0o, $localinv] == $typeof(stack0o))); goto $$block6052~c;
  $$block6052~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == stack0o)) && ($Heap[$p, $ownerFrame] == Sub)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block6052~b;
  $$block6052~b: $Heap := $Heap[stack0o, $inv := Sub]; goto $$block6052~a;
  $$block6052~a: assume IsHeap($Heap); goto block6018;
  block6018: assert (this != null); goto $$block6018~a;
  $$block6018~a: call AdditiveMethods.Z(this); return;
  
}

procedure Sub.X0(this : ref);
  requires ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == Sub)) && ($Heap[this, $localinv] == $typeof(this)));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Sub.X0(this : ref) {
  var local0 : ref where $Is(local0, Sub);
  var stack0o : ref;
  var stack1s : struct;
  var stack1o : ref;
  var temp0 : exposeVersionType;
  entry: assume $IsNotNull(this, Sub); goto $$entry~o;
  $$entry~o: assume ($Heap[this, $allocated] == true); goto block6511;
  block6511: goto block6579;
  block6579: local0 := this; goto $$block6579~j;
  $$block6579~j: stack0o := local0; goto $$block6579~i;
  $$block6579~i: havoc stack1s; goto $$block6579~h;
  $$block6579~h: assume $IsTokenForType(stack1s, Sub); goto $$block6579~g;
  $$block6579~g: stack1o := TypeObject(Sub); goto $$block6579~f;
  $$block6579~f: assert (stack0o != null); goto $$block6579~e;
  $$block6579~e: assert ((((($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame])) || ($Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]))) && ($Heap[stack0o, $inv] <: Sub)) && ($Heap[stack0o, $localinv] == $typeof(stack0o))); goto $$block6579~d;
  $$block6579~d: $Heap := $Heap[stack0o, $localinv := AdditiveMethods]; goto $$block6579~c;
  $$block6579~c: havoc temp0; goto $$block6579~b;
  $$block6579~b: $Heap := $Heap[stack0o, $exposeVersion := temp0]; goto $$block6579~a;
  $$block6579~a: assume IsHeap($Heap); goto block6596;
  block6596: assert (this != null); goto $$block6596~a;
  $$block6596~a: call AdditiveMethods.X0(this); goto block6647;
  block6647: stack0o := local0; goto $$block6647~h;
  $$block6647~h: havoc stack1s; goto $$block6647~g;
  $$block6647~g: assume $IsTokenForType(stack1s, Sub); goto $$block6647~f;
  $$block6647~f: stack1o := TypeObject(Sub); goto $$block6647~e;
  $$block6647~e: assert (stack0o != null); goto $$block6647~d;
  $$block6647~d: assert ($Heap[stack0o, $localinv] == AdditiveMethods); goto $$block6647~c;
  $$block6647~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == stack0o)) && ($Heap[$p, $ownerFrame] == Sub)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block6647~b;
  $$block6647~b: $Heap := $Heap[stack0o, $localinv := $typeof(stack0o)]; goto $$block6647~a;
  $$block6647~a: assume IsHeap($Heap); goto block6613;
  block6613: return;
  
}

procedure Sub.StartHere0$AdditiveMethods$notnull(a$in : ref where $IsNotNull(a$in, AdditiveMethods));
  free requires ($Heap[a$in, $allocated] == true);
  requires (((($Heap[a$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[a$in, $ownerRef], $inv] <: $Heap[a$in, $ownerFrame])) || ($Heap[$Heap[a$in, $ownerRef], $localinv] == $BaseClass($Heap[a$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[a$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[a$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Sub.StartHere0$AdditiveMethods$notnull(a$in : ref) {
  var a : ref where $IsNotNull(a, AdditiveMethods);
  entry: a := a$in; goto block7157;
  block7157: goto block7310;
  block7310: assert (a != null); goto $$block7310~e;
  $$block7310~e: call AdditiveMethods.M(a); goto $$block7310~d;
  $$block7310~d: assert (a != null); goto $$block7310~c;
  $$block7310~c: call AdditiveMethods.Y$.Virtual.$(a); goto $$block7310~b;
  $$block7310~b: assert (a != null); goto $$block7310~a;
  $$block7310~a: call AdditiveMethods.Z$.Virtual.$(a); return;
  
}

procedure Sub.StartHere1$AdditiveMethods$notnull(a$in : ref where $IsNotNull(a$in, AdditiveMethods));
  free requires ($Heap[a$in, $allocated] == true);
  requires ((((($Heap[a$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[a$in, $ownerRef], $inv] <: $Heap[a$in, $ownerFrame])) || ($Heap[$Heap[a$in, $ownerRef], $localinv] == $BaseClass($Heap[a$in, $ownerFrame]))) && ($Heap[a$in, $inv] == $typeof(a$in))) && ($Heap[a$in, $localinv] == $typeof(a$in)));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Sub.StartHere1$AdditiveMethods$notnull(a$in : ref) {
  var a : ref where $IsNotNull(a, AdditiveMethods);
  entry: a := a$in; goto block7701;
  block7701: goto block7854;
  block7854: assert (a != null); goto $$block7854~c;
  $$block7854~c: call AdditiveMethods.Z$.Virtual.$(a); goto $$block7854~b;
  $$block7854~b: assert (a != null); goto $$block7854~a;
  $$block7854~a: call AdditiveMethods.M(a); return;
  
}

procedure Sub.StartHere2$AdditiveMethods$notnull(a$in : ref where $IsNotNull(a$in, AdditiveMethods));
  free requires ($Heap[a$in, $allocated] == true);
  requires ((((($Heap[a$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[a$in, $ownerRef], $inv] <: $Heap[a$in, $ownerFrame])) || ($Heap[$Heap[a$in, $ownerRef], $localinv] == $BaseClass($Heap[a$in, $ownerFrame]))) && ($Heap[a$in, $inv] == $typeof(a$in))) && ($Heap[a$in, $localinv] == $typeof(a$in)));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Sub.StartHere2$AdditiveMethods$notnull(a$in : ref) {
  var a : ref where $IsNotNull(a, AdditiveMethods);
  entry: a := a$in; goto block8228;
  block8228: goto block8381;
  block8381: assert (a != null); goto $$block8381~a;
  $$block8381~a: call AdditiveMethods.Y$.Virtual.$(a); return;
  
}

procedure Sub..ctor(this : ref);
  free requires (forall $o : ref :: (($o != this) ==> ($Heap[$o, $ownerRef] != this)));
  free requires (($Heap[this, $ownerRef] == this) && ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder));
  free requires (forall $o : ref :: ((($Heap[$o, $ownerRef] == $Heap[this, $ownerRef]) && ($Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame])) ==> ($o == this)));
  free requires ($BeingConstructed == this);
  modifies $Heap;
  ensures ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == Sub)) && ($Heap[this, $localinv] == $typeof(this)));
  ensures (($Heap[this, $ownerRef] == old($Heap)[this, $ownerRef]) && ($Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame]));
  ensures ($Heap[this, $sharingMode] == $SharingMode_Unshared);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(Sub <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

implementation Sub..ctor(this : ref) {
  entry: assume $IsNotNull(this, Sub); goto $$entry~q;
  $$entry~q: assume ($Heap[this, $allocated] == true); goto $$entry~p;
  $$entry~p: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto block8602;
  block8602: goto block8619;
  block8619: assert (this != null); goto $$block8619~f;
  $$block8619~f: call AdditiveMethods..ctor(this); goto $$block8619~e;
  $$block8619~e: assert (this != null); goto $$block8619~d;
  $$block8619~d: assert (($Heap[this, $inv] == AdditiveMethods) && ($Heap[this, $localinv] == $typeof(this))); goto $$block8619~c;
  $$block8619~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == Sub)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block8619~b;
  $$block8619~b: $Heap := $Heap[this, $inv := Sub]; goto $$block8619~a;
  $$block8619~a: assume IsHeap($Heap); return;
  
}

axiom (OwnedResults <: OwnedResults);
axiom ($BaseClass(OwnedResults) == System.Object);
axiom ((OwnedResults <: $BaseClass(OwnedResults)) && (AsDirectSubClass(OwnedResults, $BaseClass(OwnedResults)) == OwnedResults));
axiom (!$IsImmutable(OwnedResults) && ($AsMutable(OwnedResults) == OwnedResults));
axiom (T <: T);
axiom ($BaseClass(T) == System.Object);
axiom ((T <: $BaseClass(T)) && (AsDirectSubClass(T, $BaseClass(T)) == T));
axiom (!$IsImmutable(T) && ($AsMutable(T) == T));
axiom (forall $Heap : <x>[ref, name]x, this : ref :: {#OwnedResults.Mz($Heap, this)} ((IsHeap($Heap) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))) ==> (((($Heap[#OwnedResults.Mz($Heap, this), $allocated] == true) && $Is(#OwnedResults.Mz($Heap, this), T)) && ((#OwnedResults.Mz($Heap, this) == null) || (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[#OwnedResults.Mz($Heap, this), $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[#OwnedResults.Mz($Heap, this), $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))))) && (#OwnedResults.Mz($Heap, this) == $Heap[this, OwnedResults.x]))));
procedure OwnedResults.Mz(this : ref) returns ($result : ref where $Is($result, T));
  requires (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))));
  free requires ($AsPureObject(this) == this);
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures ($Heap[$result, $allocated] == true);
  free ensures $Is($result, T);
  ensures (($result == null) || (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  ensures (($result == null) || (($Heap[$result, $ownerRef] == this) && ($Heap[$result, $ownerFrame] == OwnedResults)));
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures ($result == #OwnedResults.Mz($Heap, this));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} ((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation OwnedResults.Mz(this : ref) returns ($result : ref) {
  var return.value : ref where $Is(return.value, T);
  var SS$Display.Return.Local : ref where $Is(SS$Display.Return.Local, T);
  var stack0o : ref;
  entry: assume $IsNotNull(this, OwnedResults); goto $$entry~r;
  $$entry~r: assume ($Heap[this, $allocated] == true); goto block8806;
  block8806: goto block8823;
  block8823: assert (this != null); goto $$block8823~a;
  $$block8823~a: return.value := $Heap[this, OwnedResults.x]; goto block8840;
  block8840: SS$Display.Return.Local := return.value; goto $$block8840~b;
  $$block8840~b: stack0o := return.value; goto $$block8840~a;
  $$block8840~a: $result := stack0o; return;
  
}

axiom (forall $Heap : <x>[ref, name]x, this : ref :: {#OwnedResults.Pz($Heap, this)} ((IsHeap($Heap) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))) ==> (((($Heap[#OwnedResults.Pz($Heap, this), $allocated] == true) && $Is(#OwnedResults.Pz($Heap, this), T)) && ((#OwnedResults.Pz($Heap, this) == null) || (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[#OwnedResults.Pz($Heap, this), $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[#OwnedResults.Pz($Heap, this), $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))))) && (#OwnedResults.Pz($Heap, this) == $Heap[this, OwnedResults.x]))));
axiom (forall $Heap : <x>[ref, name]x, this : ref :: {#OwnedResults.Pz($Heap, this)} (((((((this != null) && ($typeof(this) <: OwnedResults)) && ($Heap[this, $inv] == $typeof(this))) && ($Heap[this, $localinv] == $typeof(this))) && IsHeap($Heap)) && ($Heap[this, $allocated] == true)) ==> (#OwnedResults.Pz($Heap, this) == ##OwnedResults.Pz($Heap[this, $exposeVersion]))));
procedure OwnedResults.Pz(this : ref) returns ($result : ref where $Is($result, T));
  requires (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))));
  free requires ($AsPureObject(this) == this);
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures ($Heap[$result, $allocated] == true);
  free ensures $Is($result, T);
  ensures (($result == null) || (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  ensures (($result == null) || (($Heap[$result, $ownerRef] == this) && ($Heap[$result, $ownerFrame] == OwnedResults)));
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures ($result == #OwnedResults.Pz($Heap, this));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} ((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation OwnedResults.Pz(this : ref) returns ($result : ref) {
  var return.value : ref where $Is(return.value, T);
  var SS$Display.Return.Local : ref where $Is(SS$Display.Return.Local, T);
  var stack0o : ref;
  entry: assume $IsNotNull(this, OwnedResults); goto $$entry~s;
  $$entry~s: assume ($Heap[this, $allocated] == true); goto block9078;
  block9078: goto block9095;
  block9095: assert (this != null); goto $$block9095~a;
  $$block9095~a: return.value := $Heap[this, OwnedResults.x]; goto block9112;
  block9112: SS$Display.Return.Local := return.value; goto $$block9112~b;
  $$block9112~b: stack0o := return.value; goto $$block9112~a;
  $$block9112~a: $result := stack0o; return;
  
}

axiom (forall $Heap : <x>[ref, name]x, this : ref :: {#OwnedResults.Pw($Heap, this)} ((IsHeap($Heap) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))) ==> (((($Heap[#OwnedResults.Pw($Heap, this), $allocated] == true) && $Is(#OwnedResults.Pw($Heap, this), T)) && ((#OwnedResults.Pw($Heap, this) == null) || (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[#OwnedResults.Pw($Heap, this), $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[#OwnedResults.Pw($Heap, this), $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))))) && (#OwnedResults.Pw($Heap, this) == $Heap[this, OwnedResults.y]))));
axiom (forall $Heap : <x>[ref, name]x, this : ref :: {#OwnedResults.Pw($Heap, this)} (((((((this != null) && ($typeof(this) <: OwnedResults)) && ($Heap[this, $inv] == $typeof(this))) && ($Heap[this, $localinv] == $typeof(this))) && IsHeap($Heap)) && ($Heap[this, $allocated] == true)) ==> (#OwnedResults.Pw($Heap, this) == ##OwnedResults.Pw($Heap[this, $exposeVersion]))));
procedure OwnedResults.Pw(this : ref) returns ($result : ref where $Is($result, T));
  requires (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))));
  free requires ($AsPureObject(this) == this);
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures ($Heap[$result, $allocated] == true);
  free ensures $Is($result, T);
  ensures (($result == null) || (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  ensures (($result == null) || (($Heap[$result, $ownerRef] == this) && ($Heap[$result, $ownerFrame] == OwnedResults)));
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures ($result == #OwnedResults.Pw($Heap, this));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} ((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation OwnedResults.Pw(this : ref) returns ($result : ref) {
  var return.value : ref where $Is(return.value, T);
  var SS$Display.Return.Local : ref where $Is(SS$Display.Return.Local, T);
  var stack0o : ref;
  entry: assume $IsNotNull(this, OwnedResults); goto $$entry~t;
  $$entry~t: assume ($Heap[this, $allocated] == true); goto block9350;
  block9350: goto block9367;
  block9367: assert (this != null); goto $$block9367~a;
  $$block9367~a: return.value := $Heap[this, OwnedResults.y]; goto block9384;
  block9384: SS$Display.Return.Local := return.value; goto $$block9384~b;
  $$block9384~b: stack0o := return.value; goto $$block9384~a;
  $$block9384~a: $result := stack0o; return;
  
}

axiom (forall $Heap : <x>[ref, name]x, this : ref, k$in : int :: {#OwnedResults.Qz$System.Int32($Heap, this, k$in)} (((IsHeap($Heap) && InRange(k$in, System.Int32)) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))) ==> ((($Heap[#OwnedResults.Qz$System.Int32($Heap, this, k$in), $allocated] == true) && $Is(#OwnedResults.Qz$System.Int32($Heap, this, k$in), T)) && ((#OwnedResults.Qz$System.Int32($Heap, this, k$in) == null) || (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[#OwnedResults.Qz$System.Int32($Heap, this, k$in), $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[#OwnedResults.Qz$System.Int32($Heap, this, k$in), $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))))));
axiom (forall $Heap : <x>[ref, name]x, this : ref, k$in : int :: {#OwnedResults.Qz$System.Int32($Heap, this, k$in)} (((((((this != null) && ($typeof(this) <: OwnedResults)) && ($Heap[this, $inv] == $typeof(this))) && ($Heap[this, $localinv] == $typeof(this))) && IsHeap($Heap)) && ($Heap[this, $allocated] == true)) ==> (#OwnedResults.Qz$System.Int32($Heap, this, k$in) == ##OwnedResults.Qz$System.Int32($Heap[this, $exposeVersion], k$in))));
procedure OwnedResults.Qz$System.Int32(this : ref, k$in : int where InRange(k$in, System.Int32)) returns ($result : ref where $Is($result, T));
  free requires true;
  requires (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))));
  free requires ($AsPureObject(this) == this);
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures ($Heap[$result, $allocated] == true);
  free ensures $Is($result, T);
  ensures (($result == null) || (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures ($result == #OwnedResults.Qz$System.Int32($Heap, this, k$in));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} ((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation OwnedResults.Qz$System.Int32(this : ref, k$in : int) returns ($result : ref) {
  var k : int where InRange(k, System.Int32);
  var local0 : int where InRange(local0, System.Int32);
  var stack0i : int;
  var stack0b : bool;
  var return.value : ref where $Is(return.value, T);
  var stack50000o : ref;
  var stack0o : ref;
  var SS$Display.Return.Local : ref where $Is(SS$Display.Return.Local, T);
  entry: assume $IsNotNull(this, OwnedResults); goto $$entry~v;
  $$entry~v: assume ($Heap[this, $allocated] == true); goto $$entry~u;
  $$entry~u: k := k$in; goto block9741;
  block9741: goto block9758;
  block9758: local0 := k; goto $$block9758~a;
  $$block9758~a: stack0i := 0; goto true9758to9826, false9758to9775;
  true9758to9826: assume (local0 == stack0i); goto block9826;
  false9758to9775: assume (local0 != stack0i); goto block9775;
  block9826: return.value := null; goto block9894;
  block9775: stack0i := 1; goto true9775to9843, false9775to9792;
  true9775to9843: assume (local0 == stack0i); goto block9843;
  false9775to9792: assume (local0 != stack0i); goto block9792;
  block9843: havoc stack50000o; goto $$block9843~g;
  $$block9843~g: assume ((($Heap[stack50000o, $allocated] == false) && (stack50000o != null)) && ($typeof(stack50000o) == T)); goto $$block9843~f;
  $$block9843~f: assume (($Heap[stack50000o, $ownerRef] == stack50000o) && ($Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder)); goto $$block9843~e;
  $$block9843~e: $Heap := $Heap[stack50000o, $allocated := true]; goto $$block9843~d;
  $$block9843~d: assert (stack50000o != null); goto $$block9843~c;
  $$block9843~c: call T..ctor(stack50000o); goto $$block9843~b;
  $$block9843~b: stack0o := stack50000o; goto $$block9843~a;
  $$block9843~a: return.value := stack0o; goto block9894;
  block9792: stack0i := 2; goto true9792to9860, false9792to9809;
  true9792to9860: assume (local0 == stack0i); goto block9860;
  false9792to9809: assume (local0 != stack0i); goto block9809;
  block9860: assert (this != null); goto $$block9860~a;
  $$block9860~a: return.value := $Heap[this, OwnedResults.x]; goto block9894;
  block9809: goto block9877;
  block9894: SS$Display.Return.Local := return.value; goto $$block9894~b;
  $$block9894~b: stack0o := return.value; goto $$block9894~a;
  $$block9894~a: $result := stack0o; return;
  block9877: assert (this != null); goto $$block9877~a;
  $$block9877~a: return.value := $Heap[this, OwnedResults.y]; goto block9894;
  
}

procedure T..ctor(this : ref);
  free requires (forall $o : ref :: (($o != this) ==> ($Heap[$o, $ownerRef] != this)));
  free requires (($Heap[this, $ownerRef] == this) && ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder));
  free requires (forall $o : ref :: ((($Heap[$o, $ownerRef] == $Heap[this, $ownerRef]) && ($Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame])) ==> ($o == this)));
  free requires ($BeingConstructed == this);
  modifies $Heap;
  ensures ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == T)) && ($Heap[this, $localinv] == $typeof(this)));
  ensures (($Heap[this, $ownerRef] == old($Heap)[this, $ownerRef]) && ($Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame]));
  ensures ($Heap[this, $sharingMode] == $SharingMode_Unshared);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(T <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

procedure OwnedResults.F0(this : ref) returns ($result : ref where $Is($result, T));
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures ($Heap[$result, $allocated] == true);
  free ensures $Is($result, T);
  ensures (($result == null) || (($Heap[$result, $ownerRef] == this) && ($Heap[$result, $ownerFrame] == OwnedResults)));
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation OwnedResults.F0(this : ref) returns ($result : ref) {
  var return.value : ref where $Is(return.value, T);
  var SS$Display.Return.Local : ref where $Is(SS$Display.Return.Local, T);
  var stack0o : ref;
  entry: assume $IsNotNull(this, OwnedResults); goto $$entry~w;
  $$entry~w: assume ($Heap[this, $allocated] == true); goto block10489;
  block10489: goto block10591;
  block10591: assert (this != null); goto $$block10591~a;
  $$block10591~a: return.value := $Heap[this, OwnedResults.x]; goto block10608;
  block10608: SS$Display.Return.Local := return.value; goto $$block10608~b;
  $$block10608~b: stack0o := return.value; goto $$block10608~a;
  $$block10608~a: $result := stack0o; return;
  
}

procedure OwnedResults.F1(this : ref) returns ($result : ref where $Is($result, T));
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures ($Heap[$result, $allocated] == true);
  free ensures $Is($result, T);
  ensures (($result == null) || (((($Heap[$result, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[$result, $ownerRef], $inv] <: $Heap[$result, $ownerFrame])) || ($Heap[$Heap[$result, $ownerRef], $localinv] == $BaseClass($Heap[$result, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))));
  ensures (($result == null) || (($Heap[$result, $ownerRef] == $Heap[this, $ownerRef]) && ($Heap[$result, $ownerFrame] == $Heap[this, $ownerFrame])));
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation OwnedResults.F1(this : ref) returns ($result : ref) {
  var stack50000o : ref;
  var stack0o : ref;
  var t : ref where $Is(t, T);
  var stack1o : ref;
  var return.value : ref where $Is(return.value, T);
  var SS$Display.Return.Local : ref where $Is(SS$Display.Return.Local, T);
  entry: assume $IsNotNull(this, OwnedResults); goto $$entry~x;
  $$entry~x: assume ($Heap[this, $allocated] == true); goto block11186;
  block11186: goto block11203;
  block11203: havoc stack50000o; goto $$block11203~q;
  $$block11203~q: assume ((($Heap[stack50000o, $allocated] == false) && (stack50000o != null)) && ($typeof(stack50000o) == T)); goto $$block11203~p;
  $$block11203~p: assume (($Heap[stack50000o, $ownerRef] == stack50000o) && ($Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder)); goto $$block11203~o;
  $$block11203~o: $Heap := $Heap[stack50000o, $allocated := true]; goto $$block11203~n;
  $$block11203~n: assert (stack50000o != null); goto $$block11203~m;
  $$block11203~m: call T..ctor(stack50000o); goto $$block11203~l;
  $$block11203~l: stack0o := stack50000o; goto $$block11203~k;
  $$block11203~k: t := stack0o; goto $$block11203~j;
  $$block11203~j: stack0o := t; goto $$block11203~i;
  $$block11203~i: assert (stack0o != null); goto $$block11203~h;
  $$block11203~h: stack0o := stack0o; goto $$block11203~g;
  $$block11203~g: stack1o := this; goto $$block11203~f;
  $$block11203~f: assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder); goto $$block11203~e;
  $$block11203~e: assert !$IsImmutable($typeof(stack0o)); goto $$block11203~d;
  $$block11203~d: assert !$IsImmutable($typeof(stack1o)); goto $$block11203~c;
  $$block11203~c: assert ((($Heap[stack1o, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[stack1o, $ownerRef], $inv] <: $Heap[stack1o, $ownerFrame])) || ($Heap[$Heap[stack1o, $ownerRef], $localinv] == $BaseClass($Heap[stack1o, $ownerFrame]))); goto $$block11203~b;
  $$block11203~b: call $SetOwner(stack0o, $Heap[stack1o, $ownerRef], $Heap[stack1o, $ownerFrame]); goto $$block11203~a;
  $$block11203~a: return.value := t; goto block11220;
  block11220: SS$Display.Return.Local := return.value; goto $$block11220~b;
  $$block11220~b: stack0o := return.value; goto $$block11220~a;
  $$block11220~a: $result := stack0o; return;
  
}

axiom (forall $U : name :: {($U <: System.Boolean)} (($U <: System.Boolean) ==> ($U == System.Boolean)));
procedure OwnedResults.F2$System.Boolean(this : ref, b$in : bool where true) returns ($result : ref where $Is($result, T));
  free requires true;
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures ($Heap[$result, $allocated] == true);
  free ensures $Is($result, T);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation OwnedResults.F2$System.Boolean(this : ref, b$in : bool) returns ($result : ref) {
  var b : bool where true;
  var stack0b : bool;
  var return.value : ref where $Is(return.value, T);
  var SS$Display.Return.Local : ref where $Is(SS$Display.Return.Local, T);
  var stack0o : ref;
  entry: assume $IsNotNull(this, OwnedResults); goto $$entry~z;
  $$entry~z: assume ($Heap[this, $allocated] == true); goto $$entry~y;
  $$entry~y: b := b$in; goto block11747;
  block11747: goto block11849;
  block11849: stack0b := b; goto true11849to11900, false11849to11866;
  true11849to11900: assume !stack0b; goto block11900;
  false11849to11866: assume stack0b; goto block11866;
  block11900: assert (this != null); goto $$block11900~a;
  $$block11900~a: return.value := $Heap[this, OwnedResults.y]; goto block11934;
  block11866: assert (this != null); goto $$block11866~a;
  $$block11866~a: return.value := $Heap[this, OwnedResults.x]; goto block11934;
  block11934: SS$Display.Return.Local := return.value; goto $$block11934~b;
  $$block11934~b: stack0o := return.value; goto $$block11934~a;
  $$block11934~a: $result := stack0o; return;
  
}

procedure OwnedResults.F3(this : ref) returns ($result : ref where $Is($result, T));
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures ($Heap[$result, $allocated] == true);
  free ensures $Is($result, T);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation OwnedResults.F3(this : ref) returns ($result : ref) {
  var stack0b : bool;
  var return.value : ref where $Is(return.value, T);
  var SS$Display.Return.Local : ref where $Is(SS$Display.Return.Local, T);
  var stack0o : ref;
  entry: assume $IsNotNull(this, OwnedResults); goto $$entry~aa;
  $$entry~aa: assume ($Heap[this, $allocated] == true); goto block12376;
  block12376: goto block12478;
  block12478: stack0b := false; goto $$block12478~b;
  $$block12478~b: assert (this != null); goto $$block12478~a;
  $$block12478~a: call return.value := OwnedResults.F2$System.Boolean(this, stack0b); goto block12495;
  block12495: SS$Display.Return.Local := return.value; goto $$block12495~b;
  $$block12495~b: stack0o := return.value; goto $$block12495~a;
  $$block12495~a: $result := stack0o; return;
  
}

procedure OwnedResults.F4(this : ref) returns ($result : ref where $Is($result, T));
  requires ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == OwnedResults)) && ($Heap[this, $localinv] == $typeof(this)));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures ($Heap[$result, $allocated] == true);
  free ensures $Is($result, T);
  ensures (($result == null) || (((($Heap[$result, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[$result, $ownerRef], $inv] <: $Heap[$result, $ownerFrame])) || ($Heap[$Heap[$result, $ownerRef], $localinv] == $BaseClass($Heap[$result, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))));
  ensures (($result == null) || (($Heap[$result, $ownerRef] == $Heap[this, $ownerRef]) && ($Heap[$result, $ownerFrame] == $Heap[this, $ownerFrame])));
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation OwnedResults.F4(this : ref) returns ($result : ref) {
  var return.value : ref where $Is(return.value, T);
  var SS$Display.Return.Local : ref where $Is(SS$Display.Return.Local, T);
  var stack0o : ref;
  entry: assume $IsNotNull(this, OwnedResults); goto $$entry~ab;
  $$entry~ab: assume ($Heap[this, $allocated] == true); goto block12801;
  block12801: goto block12818;
  block12818: assert (this != null); goto $$block12818~a;
  $$block12818~a: return.value := $Heap[this, OwnedResults.x]; goto block12835;
  block12835: SS$Display.Return.Local := return.value; goto $$block12835~b;
  $$block12835~b: stack0o := return.value; goto $$block12835~a;
  $$block12835~a: $result := stack0o; return;
  
}

axiom (forall $Heap : <x>[ref, name]x :: {#OwnedResults.Static0($Heap)} (IsHeap($Heap) ==> ((($Heap[#OwnedResults.Static0($Heap), $allocated] == true) && $IsNotNull(#OwnedResults.Static0($Heap), T)) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[#OwnedResults.Static0($Heap), $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[#OwnedResults.Static0($Heap), $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))))));
procedure OwnedResults.Static0() returns ($result : ref where $IsNotNull($result, T));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures ($Heap[$result, $allocated] == true);
  free ensures $IsNotNull($result, T);
  ensures (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))));
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures ($result == #OwnedResults.Static0($Heap));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} ((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation OwnedResults.Static0() returns ($result : ref) {
  var stack50000o : ref;
  var stack0o : ref;
  var return.value : ref where $Is(return.value, T);
  var SS$Display.Return.Local : ref where $Is(SS$Display.Return.Local, T);
  entry: goto block13073;
  block13073: goto block13090;
  block13090: havoc stack50000o; goto $$block13090~g;
  $$block13090~g: assume ((($Heap[stack50000o, $allocated] == false) && (stack50000o != null)) && ($typeof(stack50000o) == T)); goto $$block13090~f;
  $$block13090~f: assume (($Heap[stack50000o, $ownerRef] == stack50000o) && ($Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder)); goto $$block13090~e;
  $$block13090~e: $Heap := $Heap[stack50000o, $allocated := true]; goto $$block13090~d;
  $$block13090~d: assert (stack50000o != null); goto $$block13090~c;
  $$block13090~c: call T..ctor(stack50000o); goto $$block13090~b;
  $$block13090~b: stack0o := stack50000o; goto $$block13090~a;
  $$block13090~a: return.value := stack0o; goto block13107;
  block13107: SS$Display.Return.Local := return.value; goto $$block13107~b;
  $$block13107~b: stack0o := return.value; goto $$block13107~a;
  $$block13107~a: $result := stack0o; return;
  
}

axiom (forall $Heap : <x>[ref, name]x :: {#OwnedResults.Static1($Heap)} (IsHeap($Heap) ==> ((($Heap[#OwnedResults.Static1($Heap), $allocated] == true) && $IsNotNull(#OwnedResults.Static1($Heap), T)) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[#OwnedResults.Static1($Heap), $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[#OwnedResults.Static1($Heap), $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))))));
procedure OwnedResults.Static1() returns ($result : ref where $IsNotNull($result, T));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures ($Heap[$result, $allocated] == true);
  free ensures $IsNotNull($result, T);
  ensures (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))));
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures ($result == #OwnedResults.Static1($Heap));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} ((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation OwnedResults.Static1() returns ($result : ref) {
  var stack50000o : ref;
  var stack0o : ref;
  var return.value : ref where $Is(return.value, T);
  var SS$Display.Return.Local : ref where $Is(SS$Display.Return.Local, T);
  entry: goto block13396;
  block13396: goto block13413;
  block13413: havoc stack50000o; goto $$block13413~g;
  $$block13413~g: assume ((($Heap[stack50000o, $allocated] == false) && (stack50000o != null)) && ($typeof(stack50000o) == T)); goto $$block13413~f;
  $$block13413~f: assume (($Heap[stack50000o, $ownerRef] == stack50000o) && ($Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder)); goto $$block13413~e;
  $$block13413~e: $Heap := $Heap[stack50000o, $allocated := true]; goto $$block13413~d;
  $$block13413~d: assert (stack50000o != null); goto $$block13413~c;
  $$block13413~c: call T..ctor(stack50000o); goto $$block13413~b;
  $$block13413~b: stack0o := stack50000o; goto $$block13413~a;
  $$block13413~a: return.value := stack0o; goto block13430;
  block13430: SS$Display.Return.Local := return.value; goto $$block13430~b;
  $$block13430~b: stack0o := return.value; goto $$block13430~a;
  $$block13430~a: $result := stack0o; return;
  
}

axiom (true ==> $IsNotNull(#OwnedResults.Static2(), T));
procedure OwnedResults.Static2() returns ($result : ref where $IsNotNull($result, T));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures ($Heap[$result, $allocated] == true);
  free ensures $IsNotNull($result, T);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures ($result == #OwnedResults.Static2());
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} ((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation OwnedResults.Static2() returns ($result : ref) {
  var stack50000o : ref;
  var stack0o : ref;
  var return.value : ref where $Is(return.value, T);
  var SS$Display.Return.Local : ref where $Is(SS$Display.Return.Local, T);
  entry: goto block13719;
  block13719: goto block13736;
  block13736: havoc stack50000o; goto $$block13736~g;
  $$block13736~g: assume ((($Heap[stack50000o, $allocated] == false) && (stack50000o != null)) && ($typeof(stack50000o) == T)); goto $$block13736~f;
  $$block13736~f: assume (($Heap[stack50000o, $ownerRef] == stack50000o) && ($Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder)); goto $$block13736~e;
  $$block13736~e: $Heap := $Heap[stack50000o, $allocated := true]; goto $$block13736~d;
  $$block13736~d: assert (stack50000o != null); goto $$block13736~c;
  $$block13736~c: call T..ctor(stack50000o); goto $$block13736~b;
  $$block13736~b: stack0o := stack50000o; goto $$block13736~a;
  $$block13736~a: return.value := stack0o; goto block13753;
  block13753: SS$Display.Return.Local := return.value; goto $$block13753~b;
  $$block13753~b: stack0o := return.value; goto $$block13753~a;
  $$block13753~a: $result := stack0o; return;
  
}

procedure OwnedResults.F5(this : ref) returns ($result : ref where $Is($result, T));
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures ($Heap[$result, $allocated] == true);
  free ensures $Is($result, T);
  ensures (($result == null) || (($Heap[$result, $ownerRef] == this) && ($Heap[$result, $ownerFrame] == OwnedResults)));
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation OwnedResults.F5(this : ref) returns ($result : ref) {
  var return.value : ref where $Is(return.value, T);
  var SS$Display.Return.Local : ref where $Is(SS$Display.Return.Local, T);
  var stack0o : ref;
  entry: assume $IsNotNull(this, OwnedResults); goto $$entry~ac;
  $$entry~ac: assume ($Heap[this, $allocated] == true); goto block14127;
  block14127: goto block14229;
  block14229: assert (this != null); goto $$block14229~a;
  $$block14229~a: return.value := $Heap[this, OwnedResults.y]; goto block14246;
  block14246: SS$Display.Return.Local := return.value; goto $$block14246~b;
  $$block14246~b: stack0o := return.value; goto $$block14246~a;
  $$block14246~a: $result := stack0o; return;
  
}

procedure OwnedResults.Mm$System.Boolean(this : ref, b$in : bool where true) returns ($result : ref where $Is($result, T));
  free requires true;
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures ($Heap[$result, $allocated] == true);
  free ensures $Is($result, T);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation OwnedResults.Mm$System.Boolean(this : ref, b$in : bool) returns ($result : ref) {
  var b : bool where true;
  var stack0b : bool;
  var return.value : ref where $Is(return.value, T);
  var SS$Display.Return.Local : ref where $Is(SS$Display.Return.Local, T);
  var stack0o : ref;
  entry: assume $IsNotNull(this, OwnedResults); goto $$entry~ae;
  $$entry~ae: assume ($Heap[this, $allocated] == true); goto $$entry~ad;
  $$entry~ad: b := b$in; goto block14603;
  block14603: goto block14620;
  block14620: stack0b := b; goto true14620to14671, false14620to14637;
  true14620to14671: assume !stack0b; goto block14671;
  false14620to14637: assume stack0b; goto block14637;
  block14671: assert (this != null); goto $$block14671~a;
  $$block14671~a: return.value := $Heap[this, OwnedResults.y]; goto block14705;
  block14637: assert (this != null); goto $$block14637~a;
  $$block14637~a: return.value := $Heap[this, OwnedResults.x]; goto block14705;
  block14705: SS$Display.Return.Local := return.value; goto $$block14705~b;
  $$block14705~b: stack0o := return.value; goto $$block14705~a;
  $$block14705~a: $result := stack0o; return;
  
}

procedure OwnedResults..ctor(this : ref);
  free requires (forall $o : ref :: (($o != this) ==> ($Heap[$o, $ownerRef] != this)));
  free requires (($Heap[this, $ownerRef] == this) && ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder));
  free requires (forall $o : ref :: ((($Heap[$o, $ownerRef] == $Heap[this, $ownerRef]) && ($Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame])) ==> ($o == this)));
  free requires ($BeingConstructed == this);
  modifies $Heap;
  ensures ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == OwnedResults)) && ($Heap[this, $localinv] == $typeof(this)));
  ensures (($Heap[this, $ownerRef] == old($Heap)[this, $ownerRef]) && ($Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame]));
  ensures ($Heap[this, $sharingMode] == $SharingMode_Unshared);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(OwnedResults <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

implementation OwnedResults..ctor(this : ref) {
  entry: assume $IsNotNull(this, OwnedResults); goto $$entry~ai;
  $$entry~ai: assume ($Heap[this, $allocated] == true); goto $$entry~ah;
  $$entry~ah: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto $$entry~ag;
  $$entry~ag: assume ($Heap[this, OwnedResults.x] == null); goto $$entry~af;
  $$entry~af: assume ($Heap[this, OwnedResults.y] == null); goto block14994;
  block14994: goto block15011;
  block15011: assert (this != null); goto $$block15011~f;
  $$block15011~f: call System.Object..ctor(this); goto $$block15011~e;
  $$block15011~e: assert (this != null); goto $$block15011~d;
  $$block15011~d: assert (($Heap[this, $inv] == System.Object) && ($Heap[this, $localinv] == $typeof(this))); goto $$block15011~c;
  $$block15011~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == OwnedResults)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block15011~b;
  $$block15011~b: $Heap := $Heap[this, $inv := OwnedResults]; goto $$block15011~a;
  $$block15011~a: assume IsHeap($Heap); return;
  
}

implementation T..ctor(this : ref) {
  entry: assume $IsNotNull(this, T); goto $$entry~ak;
  $$entry~ak: assume ($Heap[this, $allocated] == true); goto $$entry~aj;
  $$entry~aj: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto block15181;
  block15181: goto block15198;
  block15198: assert (this != null); goto $$block15198~f;
  $$block15198~f: call System.Object..ctor(this); goto $$block15198~e;
  $$block15198~e: assert (this != null); goto $$block15198~d;
  $$block15198~d: assert (($Heap[this, $inv] == System.Object) && ($Heap[this, $localinv] == $typeof(this))); goto $$block15198~c;
  $$block15198~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == T)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block15198~b;
  $$block15198~b: $Heap := $Heap[this, $inv := T]; goto $$block15198~a;
  $$block15198~a: assume IsHeap($Heap); return;
  
}

