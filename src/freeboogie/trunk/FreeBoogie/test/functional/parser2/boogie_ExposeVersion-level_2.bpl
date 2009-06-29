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
const S.b : name;
const QClient.qclient : name;
const D.c : name;
const T.s : name;
const T.b : name;
const QClient.q : name;
const D.x : name;
const X.f : name;
const QClient.f : name;
const A.value : name;
const X.a : name;
const X.value : name;
const Q.f : name;
const T.value : name;
const C.x : name;
const A.f : name;
const X : name;
const System.IComparable : name;
const System.Runtime.InteropServices._Type : name;
const Q : name;
const System.ICloneable : name;
const System.IConvertible : name;
const System.Reflection.MemberInfo : name;
const C : name;
const System.Boolean : name;
const D : name;
const System.IEquatable`1...System.String : name;
const System.Reflection.ICustomAttributeProvider : name;
const System.IComparable`1...System.String : name;
const A : name;
const QClient : name;
const System.Runtime.InteropServices._MemberInfo : name;
const System.Reflection.IReflect : name;
const System.Collections.IEnumerable : name;
const T : name;
const S : name;
const System.Collections.Generic.IEnumerable`1...System.Char : name;
function #A.get_Value($$unnamed~fb : <x>[ref, name]x, $$unnamed~fa : ref) returns ($$unnamed~fc : int);
function ##A.get_Value($$unnamed~fd : exposeVersionType) returns ($$unnamed~fe : int);
axiom !IsStaticField(A.value);
axiom IsDirectlyModifiableField(A.value);
axiom (DeclType(A.value) == A);
axiom (AsRangeField(A.value, System.Int32) == A.value);
function #A.getValue$System.Int32($$unnamed~fh : <x>[ref, name]x, $$unnamed~fg : ref, $$unnamed~ff : int) returns ($$unnamed~fi : int);
function ##A.getValue$System.Int32($$unnamed~fk : exposeVersionType, $$unnamed~fj : int) returns ($$unnamed~fl : int);
axiom !IsStaticField(A.f);
axiom IsDirectlyModifiableField(A.f);
axiom (DeclType(A.f) == A);
axiom (AsRangeField(A.f, System.Int32) == A.f);
function #A.DummyPure$System.Int32$System.Int32($$unnamed~fp : <x>[ref, name]x, $$unnamed~fo : ref, $$unnamed~fn : int, $$unnamed~fm : int) returns ($$unnamed~fq : int);
axiom !IsStaticField(S.b);
axiom IsDirectlyModifiableField(S.b);
axiom (DeclType(S.b) == S);
function #T.get_Value($$unnamed~fs : <x>[ref, name]x, $$unnamed~fr : ref) returns ($$unnamed~ft : int);
function ##T.get_Value($$unnamed~fu : exposeVersionType) returns ($$unnamed~fv : int);
axiom !IsStaticField(T.value);
axiom IsDirectlyModifiableField(T.value);
axiom (DeclType(T.value) == T);
axiom (AsRangeField(T.value, System.Int32) == T.value);
axiom !IsStaticField(T.s);
axiom IsDirectlyModifiableField(T.s);
axiom (DeclType(T.s) == T);
axiom (AsRefField(T.s, S) == T.s);
axiom !IsStaticField(T.b);
axiom IsDirectlyModifiableField(T.b);
axiom (DeclType(T.b) == T);
axiom !IsStaticField(C.x);
axiom IsDirectlyModifiableField(C.x);
axiom (DeclType(C.x) == C);
axiom (AsRangeField(C.x, System.Int32) == C.x);
function #C.foo($$unnamed~fx : <x>[ref, name]x, $$unnamed~fw : ref) returns ($$unnamed~fy : int);
function ##C.foo($$unnamed~fz : exposeVersionType) returns ($$unnamed~ga : int);
axiom !IsStaticField(D.c);
axiom IsDirectlyModifiableField(D.c);
axiom (AsRepField(D.c, D) == D.c);
axiom (DeclType(D.c) == D);
axiom (AsRefField(D.c, C) == D.c);
axiom !IsStaticField(D.x);
axiom IsDirectlyModifiableField(D.x);
axiom (DeclType(D.x) == D);
axiom (AsRangeField(D.x, System.Int32) == D.x);
axiom !IsStaticField(QClient.q);
axiom IsDirectlyModifiableField(QClient.q);
axiom (DeclType(QClient.q) == QClient);
axiom (AsNonNullRefField(QClient.q, Q) == QClient.q);
axiom !IsStaticField(QClient.qclient);
axiom IsDirectlyModifiableField(QClient.qclient);
axiom (DeclType(QClient.qclient) == QClient);
axiom (AsNonNullRefField(QClient.qclient, QClient) == QClient.qclient);
function #Q.blah$QClient($$unnamed~gc : ref, $$unnamed~gb : ref) returns ($$unnamed~gd : int);
axiom !IsStaticField(Q.f);
axiom IsDirectlyModifiableField(Q.f);
axiom (DeclType(Q.f) == Q);
axiom (AsRangeField(Q.f, System.Int32) == Q.f);
axiom !IsStaticField(QClient.f);
axiom IsDirectlyModifiableField(QClient.f);
axiom (DeclType(QClient.f) == QClient);
axiom (AsRangeField(QClient.f, System.Int32) == QClient.f);
function #X.getValue$System.Int32($$unnamed~gg : <x>[ref, name]x, $$unnamed~gf : ref, $$unnamed~ge : int) returns ($$unnamed~gh : int);
function ##X.getValue$System.Int32($$unnamed~gj : exposeVersionType, $$unnamed~gi : int) returns ($$unnamed~gk : int);
axiom !IsStaticField(X.value);
axiom IsDirectlyModifiableField(X.value);
axiom (DeclType(X.value) == X);
axiom (AsRangeField(X.value, System.Int32) == X.value);
axiom !IsStaticField(X.a);
axiom IsDirectlyModifiableField(X.a);
axiom (DeclType(X.a) == X);
axiom (AsRefField(X.a, X) == X.a);
axiom !IsStaticField(X.f);
axiom IsDirectlyModifiableField(X.f);
axiom (DeclType(X.f) == X);
axiom (AsRangeField(X.f, System.Int32) == X.f);
axiom (A <: A);
axiom ($BaseClass(A) == System.Object);
axiom ((A <: $BaseClass(A)) && (AsDirectSubClass(A, $BaseClass(A)) == A));
axiom (!$IsImmutable(A) && ($AsMutable(A) == A));
axiom (forall $U : name :: {($U <: A)} (($U <: A) ==> ($U == A)));
axiom (forall $Heap : <x>[ref, name]x, this : ref :: {#A.get_Value($Heap, this)} ((IsHeap($Heap) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))) ==> InRange(#A.get_Value($Heap, this), System.Int32)));
axiom (forall $Heap : <x>[ref, name]x, this : ref :: {#A.get_Value($Heap, this)} (((((((this != null) && ($typeof(this) <: A)) && ($Heap[this, $inv] == $typeof(this))) && ($Heap[this, $localinv] == $typeof(this))) && IsHeap($Heap)) && ($Heap[this, $allocated] == true)) ==> (#A.get_Value($Heap, this) == ##A.get_Value($Heap[this, $exposeVersion]))));
procedure A.get_Value(this : ref) returns ($result : int where InRange($result, System.Int32));
  requires (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))));
  free requires ($AsPureObject(this) == this);
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures true;
  free ensures InRange($result, System.Int32);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures ($Heap == old($Heap));
  free ensures ($result == #A.get_Value($Heap, this));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} ((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation A.get_Value(this : ref) returns ($result : int) {
  var return.value : int where InRange(return.value, System.Int32);
  var SS$Display.Return.Local : int where InRange(SS$Display.Return.Local, System.Int32);
  var stack0i : int;
  entry: assume $IsNotNull(this, A); goto $$entry~a;
  $$entry~a: assume ($Heap[this, $allocated] == true); goto block1751;
  block1751: goto block1768;
  block1768: assert (this != null); goto $$block1768~a;
  $$block1768~a: return.value := $Heap[this, A.value]; goto block1785;
  block1785: SS$Display.Return.Local := return.value; goto $$block1785~b;
  $$block1785~b: stack0i := return.value; goto $$block1785~a;
  $$block1785~a: $result := stack0i; return;
  
}

procedure A.set_Value$System.Int32(this : ref, value$in : int where InRange(value$in, System.Int32));
  free requires true;
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old((($o != this) || ($f != A.value)))) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation A.set_Value$System.Int32(this : ref, value$in : int) {
  var value : int where InRange(value, System.Int32);
  var local0 : ref where $Is(local0, A);
  var stack0o : ref;
  var stack1s : struct;
  var stack1o : ref;
  var temp0 : exposeVersionType;
  var temp1 : exposeVersionType;
  entry: assume $IsNotNull(this, A); goto $$entry~c;
  $$entry~c: assume ($Heap[this, $allocated] == true); goto $$entry~b;
  $$entry~b: value := value$in; goto block2346;
  block2346: goto block2414;
  block2414: local0 := this; goto $$block2414~j;
  $$block2414~j: stack0o := local0; goto $$block2414~i;
  $$block2414~i: havoc stack1s; goto $$block2414~h;
  $$block2414~h: assume $IsTokenForType(stack1s, A); goto $$block2414~g;
  $$block2414~g: stack1o := TypeObject(A); goto $$block2414~f;
  $$block2414~f: assert (stack0o != null); goto $$block2414~e;
  $$block2414~e: assert ((((($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame])) || ($Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]))) && ($Heap[stack0o, $inv] <: A)) && ($Heap[stack0o, $localinv] == $typeof(stack0o))); goto $$block2414~d;
  $$block2414~d: $Heap := $Heap[stack0o, $localinv := System.Object]; goto $$block2414~c;
  $$block2414~c: havoc temp0; goto $$block2414~b;
  $$block2414~b: $Heap := $Heap[stack0o, $exposeVersion := temp0]; goto $$block2414~a;
  $$block2414~a: assume IsHeap($Heap); goto block2431;
  block2431: assert (this != null); goto $$block2431~d;
  $$block2431~d: havoc temp1; goto $$block2431~c;
  $$block2431~c: $Heap := $Heap[this, $exposeVersion := temp1]; goto $$block2431~b;
  $$block2431~b: $Heap := $Heap[this, A.value := value]; goto $$block2431~a;
  $$block2431~a: assume IsHeap($Heap); goto block2482;
  block2482: stack0o := local0; goto $$block2482~h;
  $$block2482~h: havoc stack1s; goto $$block2482~g;
  $$block2482~g: assume $IsTokenForType(stack1s, A); goto $$block2482~f;
  $$block2482~f: stack1o := TypeObject(A); goto $$block2482~e;
  $$block2482~e: assert (stack0o != null); goto $$block2482~d;
  $$block2482~d: assert ($Heap[stack0o, $localinv] == System.Object); goto $$block2482~c;
  $$block2482~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == stack0o)) && ($Heap[$p, $ownerFrame] == A)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block2482~b;
  $$block2482~b: $Heap := $Heap[stack0o, $localinv := $typeof(stack0o)]; goto $$block2482~a;
  $$block2482~a: assume IsHeap($Heap); goto block2448;
  block2448: return;
  
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
axiom (forall $Heap : <x>[ref, name]x, this : ref, p$in : int :: {#A.getValue$System.Int32($Heap, this, p$in)} (((IsHeap($Heap) && InRange(p$in, System.Int32)) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))) ==> InRange(#A.getValue$System.Int32($Heap, this, p$in), System.Int32)));
axiom (forall $Heap : <x>[ref, name]x, this : ref, p$in : int :: {#A.getValue$System.Int32($Heap, this, p$in)} (((((((this != null) && ($typeof(this) <: A)) && ($Heap[this, $inv] == $typeof(this))) && ($Heap[this, $localinv] == $typeof(this))) && IsHeap($Heap)) && ($Heap[this, $allocated] == true)) ==> (#A.getValue$System.Int32($Heap, this, p$in) == ##A.getValue$System.Int32($Heap[this, $exposeVersion], p$in))));
procedure A.getValue$System.Int32(this : ref, p$in : int where InRange(p$in, System.Int32)) returns ($result : int where InRange($result, System.Int32));
  free requires true;
  requires (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))));
  free requires ($AsPureObject(this) == this);
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures true;
  free ensures InRange($result, System.Int32);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures ($Heap == old($Heap));
  free ensures ($result == #A.getValue$System.Int32($Heap, this, p$in));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} ((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation A.getValue$System.Int32(this : ref, p$in : int) returns ($result : int) {
  var p : int where InRange(p, System.Int32);
  var return.value : int where InRange(return.value, System.Int32);
  var SS$Display.Return.Local : int where InRange(SS$Display.Return.Local, System.Int32);
  var stack0i : int;
  entry: assume $IsNotNull(this, A); goto $$entry~e;
  $$entry~e: assume ($Heap[this, $allocated] == true); goto $$entry~d;
  $$entry~d: p := p$in; goto block2873;
  block2873: goto block2890;
  block2890: assert (this != null); goto $$block2890~a;
  $$block2890~a: return.value := $Heap[this, A.value]; goto block2907;
  block2907: SS$Display.Return.Local := return.value; goto $$block2907~b;
  $$block2907~b: stack0i := return.value; goto $$block2907~a;
  $$block2907~a: $result := stack0i; return;
  
}

procedure A.setValue$System.Int32(this : ref, p$in : int where InRange(p$in, System.Int32));
  free requires true;
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old((($o != this) || ($f != A.value)))) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation A.setValue$System.Int32(this : ref, p$in : int) {
  var p : int where InRange(p, System.Int32);
  var temp0 : exposeVersionType;
  entry: assume $IsNotNull(this, A); goto $$entry~g;
  $$entry~g: assume ($Heap[this, $allocated] == true); goto $$entry~f;
  $$entry~f: p := p$in; goto block3128;
  block3128: goto block3145;
  block3145: assert (this != null); goto $$block3145~d;
  $$block3145~d: havoc temp0; goto $$block3145~c;
  $$block3145~c: $Heap := $Heap[this, $exposeVersion := temp0]; goto $$block3145~b;
  $$block3145~b: $Heap := $Heap[this, A.value := p]; goto $$block3145~a;
  $$block3145~a: assume IsHeap($Heap); return;
  
}

procedure A.FieldUpdateWithMethodQuery$A$notnull(this : ref, o$in : ref where $IsNotNull(o$in, A));
  free requires ($Heap[o$in, $allocated] == true);
  requires (#A.getValue$System.Int32($Heap, o$in, 4) == 5);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[o$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[o$in, $ownerRef], $inv] <: $Heap[o$in, $ownerFrame])) || ($Heap[$Heap[o$in, $ownerRef], $localinv] == $BaseClass($Heap[o$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[o$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[o$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  ensures (#A.getValue$System.Int32($Heap, o$in, 4) == 5);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old((($o != o$in) || !($typeof(o$in) <: DeclType($f))))) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation A.FieldUpdateWithMethodQuery$A$notnull(this : ref, o$in : ref) {
  var o : ref where $IsNotNull(o, A);
  var local1 : ref where $Is(local1, A);
  var stack0o : ref;
  var stack1s : struct;
  var stack1o : ref;
  var temp0 : exposeVersionType;
  var stack0i : int;
  var temp1 : exposeVersionType;
  entry: assume $IsNotNull(this, A); goto $$entry~i;
  $$entry~i: assume ($Heap[this, $allocated] == true); goto $$entry~h;
  $$entry~h: o := o$in; goto block3553;
  block3553: goto block3706;
  block3706: local1 := o; goto $$block3706~j;
  $$block3706~j: stack0o := local1; goto $$block3706~i;
  $$block3706~i: havoc stack1s; goto $$block3706~h;
  $$block3706~h: assume $IsTokenForType(stack1s, A); goto $$block3706~g;
  $$block3706~g: stack1o := TypeObject(A); goto $$block3706~f;
  $$block3706~f: assert (stack0o != null); goto $$block3706~e;
  $$block3706~e: assert ((((($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame])) || ($Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]))) && ($Heap[stack0o, $inv] <: A)) && ($Heap[stack0o, $localinv] == $typeof(stack0o))); goto $$block3706~d;
  $$block3706~d: $Heap := $Heap[stack0o, $localinv := System.Object]; goto $$block3706~c;
  $$block3706~c: havoc temp0; goto $$block3706~b;
  $$block3706~b: $Heap := $Heap[stack0o, $exposeVersion := temp0]; goto $$block3706~a;
  $$block3706~a: assume IsHeap($Heap); goto block3723;
  block3723: stack0i := 0; goto $$block3723~e;
  $$block3723~e: assert (o != null); goto $$block3723~d;
  $$block3723~d: havoc temp1; goto $$block3723~c;
  $$block3723~c: $Heap := $Heap[o, $exposeVersion := temp1]; goto $$block3723~b;
  $$block3723~b: $Heap := $Heap[o, A.value := stack0i]; goto $$block3723~a;
  $$block3723~a: assume IsHeap($Heap); goto block3859;
  block3859: stack0o := local1; goto $$block3859~h;
  $$block3859~h: havoc stack1s; goto $$block3859~g;
  $$block3859~g: assume $IsTokenForType(stack1s, A); goto $$block3859~f;
  $$block3859~f: stack1o := TypeObject(A); goto $$block3859~e;
  $$block3859~e: assert (stack0o != null); goto $$block3859~d;
  $$block3859~d: assert ($Heap[stack0o, $localinv] == System.Object); goto $$block3859~c;
  $$block3859~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == stack0o)) && ($Heap[$p, $ownerFrame] == A)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block3859~b;
  $$block3859~b: $Heap := $Heap[stack0o, $localinv := $typeof(stack0o)]; goto $$block3859~a;
  $$block3859~a: assume IsHeap($Heap); goto block3825;
  block3825: return;
  
}

procedure A.FieldUpdateWithGetterQuery$A$notnull(this : ref, o$in : ref where $IsNotNull(o$in, A));
  free requires ($Heap[o$in, $allocated] == true);
  requires (#A.get_Value($Heap, o$in) == 5);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[o$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[o$in, $ownerRef], $inv] <: $Heap[o$in, $ownerFrame])) || ($Heap[$Heap[o$in, $ownerRef], $localinv] == $BaseClass($Heap[o$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[o$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[o$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  ensures (#A.get_Value($Heap, o$in) == 5);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old((($o != o$in) || !($typeof(o$in) <: DeclType($f))))) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation A.FieldUpdateWithGetterQuery$A$notnull(this : ref, o$in : ref) {
  var o : ref where $IsNotNull(o, A);
  var local1 : ref where $Is(local1, A);
  var stack0o : ref;
  var stack1s : struct;
  var stack1o : ref;
  var temp0 : exposeVersionType;
  var stack0i : int;
  var temp1 : exposeVersionType;
  entry: assume $IsNotNull(this, A); goto $$entry~k;
  $$entry~k: assume ($Heap[this, $allocated] == true); goto $$entry~j;
  $$entry~j: o := o$in; goto block4590;
  block4590: goto block4743;
  block4743: local1 := o; goto $$block4743~j;
  $$block4743~j: stack0o := local1; goto $$block4743~i;
  $$block4743~i: havoc stack1s; goto $$block4743~h;
  $$block4743~h: assume $IsTokenForType(stack1s, A); goto $$block4743~g;
  $$block4743~g: stack1o := TypeObject(A); goto $$block4743~f;
  $$block4743~f: assert (stack0o != null); goto $$block4743~e;
  $$block4743~e: assert ((((($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame])) || ($Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]))) && ($Heap[stack0o, $inv] <: A)) && ($Heap[stack0o, $localinv] == $typeof(stack0o))); goto $$block4743~d;
  $$block4743~d: $Heap := $Heap[stack0o, $localinv := System.Object]; goto $$block4743~c;
  $$block4743~c: havoc temp0; goto $$block4743~b;
  $$block4743~b: $Heap := $Heap[stack0o, $exposeVersion := temp0]; goto $$block4743~a;
  $$block4743~a: assume IsHeap($Heap); goto block4760;
  block4760: stack0i := 0; goto $$block4760~e;
  $$block4760~e: assert (o != null); goto $$block4760~d;
  $$block4760~d: havoc temp1; goto $$block4760~c;
  $$block4760~c: $Heap := $Heap[o, $exposeVersion := temp1]; goto $$block4760~b;
  $$block4760~b: $Heap := $Heap[o, A.value := stack0i]; goto $$block4760~a;
  $$block4760~a: assume IsHeap($Heap); goto block4896;
  block4896: stack0o := local1; goto $$block4896~h;
  $$block4896~h: havoc stack1s; goto $$block4896~g;
  $$block4896~g: assume $IsTokenForType(stack1s, A); goto $$block4896~f;
  $$block4896~f: stack1o := TypeObject(A); goto $$block4896~e;
  $$block4896~e: assert (stack0o != null); goto $$block4896~d;
  $$block4896~d: assert ($Heap[stack0o, $localinv] == System.Object); goto $$block4896~c;
  $$block4896~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == stack0o)) && ($Heap[$p, $ownerFrame] == A)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block4896~b;
  $$block4896~b: $Heap := $Heap[stack0o, $localinv := $typeof(stack0o)]; goto $$block4896~a;
  $$block4896~a: assume IsHeap($Heap); goto block4862;
  block4862: return;
  
}

procedure A.FieldUpdateOnOtherWithMethodQuery$A$notnull$A$notnull(this : ref, o$in : ref where $IsNotNull(o$in, A), oo$in : ref where $IsNotNull(oo$in, A));
  free requires ($Heap[o$in, $allocated] == true);
  free requires ($Heap[oo$in, $allocated] == true);
  requires (#A.getValue$System.Int32($Heap, o$in, 4) == 5);
  requires (o$in != oo$in);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[o$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[o$in, $ownerRef], $inv] <: $Heap[o$in, $ownerFrame])) || ($Heap[$Heap[o$in, $ownerRef], $localinv] == $BaseClass($Heap[o$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[o$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[o$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[oo$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[oo$in, $ownerRef], $inv] <: $Heap[oo$in, $ownerFrame])) || ($Heap[$Heap[oo$in, $ownerRef], $localinv] == $BaseClass($Heap[oo$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[oo$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[oo$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  ensures (#A.getValue$System.Int32($Heap, o$in, 4) == 5);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(((($o != o$in) || !($typeof(o$in) <: DeclType($f))) && (($o != oo$in) || !($typeof(oo$in) <: DeclType($f)))))) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation A.FieldUpdateOnOtherWithMethodQuery$A$notnull$A$notnull(this : ref, o$in : ref, oo$in : ref) {
  var o : ref where $IsNotNull(o, A);
  var oo : ref where $IsNotNull(oo, A);
  var local1 : ref where $Is(local1, A);
  var stack0o : ref;
  var stack1s : struct;
  var stack1o : ref;
  var temp0 : exposeVersionType;
  var stack0i : int;
  var temp1 : exposeVersionType;
  entry: assume $IsNotNull(this, A); goto $$entry~n;
  $$entry~n: assume ($Heap[this, $allocated] == true); goto $$entry~m;
  $$entry~m: o := o$in; goto $$entry~l;
  $$entry~l: oo := oo$in; goto block5678;
  block5678: goto block5882;
  block5882: local1 := oo; goto $$block5882~j;
  $$block5882~j: stack0o := local1; goto $$block5882~i;
  $$block5882~i: havoc stack1s; goto $$block5882~h;
  $$block5882~h: assume $IsTokenForType(stack1s, A); goto $$block5882~g;
  $$block5882~g: stack1o := TypeObject(A); goto $$block5882~f;
  $$block5882~f: assert (stack0o != null); goto $$block5882~e;
  $$block5882~e: assert ((((($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame])) || ($Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]))) && ($Heap[stack0o, $inv] <: A)) && ($Heap[stack0o, $localinv] == $typeof(stack0o))); goto $$block5882~d;
  $$block5882~d: $Heap := $Heap[stack0o, $localinv := System.Object]; goto $$block5882~c;
  $$block5882~c: havoc temp0; goto $$block5882~b;
  $$block5882~b: $Heap := $Heap[stack0o, $exposeVersion := temp0]; goto $$block5882~a;
  $$block5882~a: assume IsHeap($Heap); goto block5899;
  block5899: stack0i := 0; goto $$block5899~e;
  $$block5899~e: assert (oo != null); goto $$block5899~d;
  $$block5899~d: havoc temp1; goto $$block5899~c;
  $$block5899~c: $Heap := $Heap[oo, $exposeVersion := temp1]; goto $$block5899~b;
  $$block5899~b: $Heap := $Heap[oo, A.value := stack0i]; goto $$block5899~a;
  $$block5899~a: assume IsHeap($Heap); goto block6035;
  block6035: stack0o := local1; goto $$block6035~h;
  $$block6035~h: havoc stack1s; goto $$block6035~g;
  $$block6035~g: assume $IsTokenForType(stack1s, A); goto $$block6035~f;
  $$block6035~f: stack1o := TypeObject(A); goto $$block6035~e;
  $$block6035~e: assert (stack0o != null); goto $$block6035~d;
  $$block6035~d: assert ($Heap[stack0o, $localinv] == System.Object); goto $$block6035~c;
  $$block6035~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == stack0o)) && ($Heap[$p, $ownerFrame] == A)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block6035~b;
  $$block6035~b: $Heap := $Heap[stack0o, $localinv := $typeof(stack0o)]; goto $$block6035~a;
  $$block6035~a: assume IsHeap($Heap); goto block6001;
  block6001: return;
  
}

procedure A.FieldUpdateOnOtherWithGetterQuery$A$notnull$A$notnull(this : ref, o$in : ref where $IsNotNull(o$in, A), oo$in : ref where $IsNotNull(oo$in, A));
  free requires ($Heap[o$in, $allocated] == true);
  free requires ($Heap[oo$in, $allocated] == true);
  requires (#A.get_Value($Heap, o$in) == 5);
  requires (o$in != oo$in);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[o$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[o$in, $ownerRef], $inv] <: $Heap[o$in, $ownerFrame])) || ($Heap[$Heap[o$in, $ownerRef], $localinv] == $BaseClass($Heap[o$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[o$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[o$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[oo$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[oo$in, $ownerRef], $inv] <: $Heap[oo$in, $ownerFrame])) || ($Heap[$Heap[oo$in, $ownerRef], $localinv] == $BaseClass($Heap[oo$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[oo$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[oo$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  ensures (#A.get_Value($Heap, o$in) == 5);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(((($o != o$in) || !($typeof(o$in) <: DeclType($f))) && (($o != oo$in) || !($typeof(oo$in) <: DeclType($f)))))) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation A.FieldUpdateOnOtherWithGetterQuery$A$notnull$A$notnull(this : ref, o$in : ref, oo$in : ref) {
  var o : ref where $IsNotNull(o, A);
  var oo : ref where $IsNotNull(oo, A);
  var local1 : ref where $Is(local1, A);
  var stack0o : ref;
  var stack1s : struct;
  var stack1o : ref;
  var temp0 : exposeVersionType;
  var stack0i : int;
  var temp1 : exposeVersionType;
  entry: assume $IsNotNull(this, A); goto $$entry~q;
  $$entry~q: assume ($Heap[this, $allocated] == true); goto $$entry~p;
  $$entry~p: o := o$in; goto $$entry~o;
  $$entry~o: oo := oo$in; goto block6817;
  block6817: goto block7021;
  block7021: local1 := oo; goto $$block7021~j;
  $$block7021~j: stack0o := local1; goto $$block7021~i;
  $$block7021~i: havoc stack1s; goto $$block7021~h;
  $$block7021~h: assume $IsTokenForType(stack1s, A); goto $$block7021~g;
  $$block7021~g: stack1o := TypeObject(A); goto $$block7021~f;
  $$block7021~f: assert (stack0o != null); goto $$block7021~e;
  $$block7021~e: assert ((((($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame])) || ($Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]))) && ($Heap[stack0o, $inv] <: A)) && ($Heap[stack0o, $localinv] == $typeof(stack0o))); goto $$block7021~d;
  $$block7021~d: $Heap := $Heap[stack0o, $localinv := System.Object]; goto $$block7021~c;
  $$block7021~c: havoc temp0; goto $$block7021~b;
  $$block7021~b: $Heap := $Heap[stack0o, $exposeVersion := temp0]; goto $$block7021~a;
  $$block7021~a: assume IsHeap($Heap); goto block7038;
  block7038: stack0i := 0; goto $$block7038~e;
  $$block7038~e: assert (oo != null); goto $$block7038~d;
  $$block7038~d: havoc temp1; goto $$block7038~c;
  $$block7038~c: $Heap := $Heap[oo, $exposeVersion := temp1]; goto $$block7038~b;
  $$block7038~b: $Heap := $Heap[oo, A.value := stack0i]; goto $$block7038~a;
  $$block7038~a: assume IsHeap($Heap); goto block7174;
  block7174: stack0o := local1; goto $$block7174~h;
  $$block7174~h: havoc stack1s; goto $$block7174~g;
  $$block7174~g: assume $IsTokenForType(stack1s, A); goto $$block7174~f;
  $$block7174~f: stack1o := TypeObject(A); goto $$block7174~e;
  $$block7174~e: assert (stack0o != null); goto $$block7174~d;
  $$block7174~d: assert ($Heap[stack0o, $localinv] == System.Object); goto $$block7174~c;
  $$block7174~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == stack0o)) && ($Heap[$p, $ownerFrame] == A)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block7174~b;
  $$block7174~b: $Heap := $Heap[stack0o, $localinv := $typeof(stack0o)]; goto $$block7174~a;
  $$block7174~a: assume IsHeap($Heap); goto block7140;
  block7140: return;
  
}

procedure A.FieldUpdateOnOtherWithMethodQueryWithDifferentParam$A$notnull$A$notnull(this : ref, o$in : ref where $IsNotNull(o$in, A), oo$in : ref where $IsNotNull(oo$in, A));
  free requires ($Heap[o$in, $allocated] == true);
  free requires ($Heap[oo$in, $allocated] == true);
  requires (#A.getValue$System.Int32($Heap, o$in, 4) == 5);
  requires (o$in != oo$in);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[o$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[o$in, $ownerRef], $inv] <: $Heap[o$in, $ownerFrame])) || ($Heap[$Heap[o$in, $ownerRef], $localinv] == $BaseClass($Heap[o$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[o$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[o$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[oo$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[oo$in, $ownerRef], $inv] <: $Heap[oo$in, $ownerFrame])) || ($Heap[$Heap[oo$in, $ownerRef], $localinv] == $BaseClass($Heap[oo$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[oo$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[oo$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  ensures (#A.getValue$System.Int32($Heap, o$in, 5) == 5);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(((($o != o$in) || !($typeof(o$in) <: DeclType($f))) && (($o != oo$in) || !($typeof(oo$in) <: DeclType($f)))))) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation A.FieldUpdateOnOtherWithMethodQueryWithDifferentParam$A$notnull$A$notnull(this : ref, o$in : ref, oo$in : ref) {
  var o : ref where $IsNotNull(o, A);
  var oo : ref where $IsNotNull(oo, A);
  var local1 : ref where $Is(local1, A);
  var stack0o : ref;
  var stack1s : struct;
  var stack1o : ref;
  var temp0 : exposeVersionType;
  var stack0i : int;
  var temp1 : exposeVersionType;
  entry: assume $IsNotNull(this, A); goto $$entry~t;
  $$entry~t: assume ($Heap[this, $allocated] == true); goto $$entry~s;
  $$entry~s: o := o$in; goto $$entry~r;
  $$entry~r: oo := oo$in; goto block7956;
  block7956: goto block8160;
  block8160: local1 := oo; goto $$block8160~j;
  $$block8160~j: stack0o := local1; goto $$block8160~i;
  $$block8160~i: havoc stack1s; goto $$block8160~h;
  $$block8160~h: assume $IsTokenForType(stack1s, A); goto $$block8160~g;
  $$block8160~g: stack1o := TypeObject(A); goto $$block8160~f;
  $$block8160~f: assert (stack0o != null); goto $$block8160~e;
  $$block8160~e: assert ((((($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame])) || ($Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]))) && ($Heap[stack0o, $inv] <: A)) && ($Heap[stack0o, $localinv] == $typeof(stack0o))); goto $$block8160~d;
  $$block8160~d: $Heap := $Heap[stack0o, $localinv := System.Object]; goto $$block8160~c;
  $$block8160~c: havoc temp0; goto $$block8160~b;
  $$block8160~b: $Heap := $Heap[stack0o, $exposeVersion := temp0]; goto $$block8160~a;
  $$block8160~a: assume IsHeap($Heap); goto block8177;
  block8177: stack0i := 0; goto $$block8177~e;
  $$block8177~e: assert (oo != null); goto $$block8177~d;
  $$block8177~d: havoc temp1; goto $$block8177~c;
  $$block8177~c: $Heap := $Heap[oo, $exposeVersion := temp1]; goto $$block8177~b;
  $$block8177~b: $Heap := $Heap[oo, A.value := stack0i]; goto $$block8177~a;
  $$block8177~a: assume IsHeap($Heap); goto block8313;
  block8313: stack0o := local1; goto $$block8313~h;
  $$block8313~h: havoc stack1s; goto $$block8313~g;
  $$block8313~g: assume $IsTokenForType(stack1s, A); goto $$block8313~f;
  $$block8313~f: stack1o := TypeObject(A); goto $$block8313~e;
  $$block8313~e: assert (stack0o != null); goto $$block8313~d;
  $$block8313~d: assert ($Heap[stack0o, $localinv] == System.Object); goto $$block8313~c;
  $$block8313~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == stack0o)) && ($Heap[$p, $ownerFrame] == A)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block8313~b;
  $$block8313~b: $Heap := $Heap[stack0o, $localinv := $typeof(stack0o)]; goto $$block8313~a;
  $$block8313~a: assume IsHeap($Heap); goto block8279;
  block8279: return;
  
}

procedure A.MethodCallWithMethodQuery(this : ref);
  requires (#A.getValue$System.Int32($Heap, this, 4) == 5);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  ensures (#A.getValue$System.Int32($Heap, this, 4) == 5);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old((($o != this) || ($f != A.value)))) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation A.MethodCallWithMethodQuery(this : ref) {
  var stack0i : int;
  entry: assume $IsNotNull(this, A); goto $$entry~u;
  $$entry~u: assume ($Heap[this, $allocated] == true); goto block8993;
  block8993: goto block9095;
  block9095: stack0i := 0; goto $$block9095~b;
  $$block9095~b: assert (this != null); goto $$block9095~a;
  $$block9095~a: call A.setValue$System.Int32(this, stack0i); goto block9197;
  block9197: return;
  
}

procedure A.MethodCallWithGetterQuery(this : ref);
  requires (#A.get_Value($Heap, this) == 5);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  ensures (#A.get_Value($Heap, this) == 5);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old((($o != this) || ($f != A.value)))) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation A.MethodCallWithGetterQuery(this : ref) {
  var stack0i : int;
  entry: assume $IsNotNull(this, A); goto $$entry~v;
  $$entry~v: assume ($Heap[this, $allocated] == true); goto block9673;
  block9673: goto block9775;
  block9775: stack0i := 0; goto $$block9775~b;
  $$block9775~b: assert (this != null); goto $$block9775~a;
  $$block9775~a: call A.setValue$System.Int32(this, stack0i); goto block9877;
  block9877: return;
  
}

procedure A.MethodCallOnOtherWithMethodQuery$A$notnull(this : ref, o$in : ref where $IsNotNull(o$in, A));
  free requires ($Heap[o$in, $allocated] == true);
  requires (#A.getValue$System.Int32($Heap, this, 4) == 5);
  requires (o$in != this);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[o$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[o$in, $ownerRef], $inv] <: $Heap[o$in, $ownerFrame])) || ($Heap[$Heap[o$in, $ownerRef], $localinv] == $BaseClass($Heap[o$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[o$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[o$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  ensures (#A.getValue$System.Int32($Heap, this, 4) == 5);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old((($o != o$in) || !($typeof(o$in) <: DeclType($f))))) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation A.MethodCallOnOtherWithMethodQuery$A$notnull(this : ref, o$in : ref) {
  var o : ref where $IsNotNull(o, A);
  var stack0i : int;
  entry: assume $IsNotNull(this, A); goto $$entry~x;
  $$entry~x: assume ($Heap[this, $allocated] == true); goto $$entry~w;
  $$entry~w: o := o$in; goto block10404;
  block10404: goto block10557;
  block10557: stack0i := 0; goto $$block10557~b;
  $$block10557~b: assert (o != null); goto $$block10557~a;
  $$block10557~a: call A.setValue$System.Int32(o, stack0i); goto block10659;
  block10659: return;
  
}

procedure A.MethodCallOnOtherWithGetterQuery$A$notnull(this : ref, o$in : ref where $IsNotNull(o$in, A));
  free requires ($Heap[o$in, $allocated] == true);
  requires (#A.get_Value($Heap, this) == 5);
  requires (o$in != this);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[o$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[o$in, $ownerRef], $inv] <: $Heap[o$in, $ownerFrame])) || ($Heap[$Heap[o$in, $ownerRef], $localinv] == $BaseClass($Heap[o$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[o$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[o$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  ensures (#A.get_Value($Heap, this) == 5);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old((($o != o$in) || !($typeof(o$in) <: DeclType($f))))) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation A.MethodCallOnOtherWithGetterQuery$A$notnull(this : ref, o$in : ref) {
  var o : ref where $IsNotNull(o, A);
  var stack0i : int;
  entry: assume $IsNotNull(this, A); goto $$entry~z;
  $$entry~z: assume ($Heap[this, $allocated] == true); goto $$entry~y;
  $$entry~y: o := o$in; goto block11186;
  block11186: goto block11339;
  block11339: stack0i := 0; goto $$block11339~b;
  $$block11339~b: assert (o != null); goto $$block11339~a;
  $$block11339~a: call A.setValue$System.Int32(o, stack0i); goto block11441;
  block11441: return;
  
}

procedure A.FieldUpdateOnOtherFieldWithMethodQuery(this : ref);
  requires (#A.getValue$System.Int32($Heap, this, 4) == 5);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  ensures (#A.getValue$System.Int32($Heap, this, 4) == 5);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old((($o != this) || ($f != A.f)))) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation A.FieldUpdateOnOtherFieldWithMethodQuery(this : ref) {
  var local1 : ref where $Is(local1, A);
  var stack0o : ref;
  var stack1s : struct;
  var stack1o : ref;
  var temp0 : exposeVersionType;
  var stack0i : int;
  var temp1 : exposeVersionType;
  entry: assume $IsNotNull(this, A); goto $$entry~aa;
  $$entry~aa: assume ($Heap[this, $allocated] == true); goto block11968;
  block11968: goto block12121;
  block12121: local1 := this; goto $$block12121~j;
  $$block12121~j: stack0o := local1; goto $$block12121~i;
  $$block12121~i: havoc stack1s; goto $$block12121~h;
  $$block12121~h: assume $IsTokenForType(stack1s, A); goto $$block12121~g;
  $$block12121~g: stack1o := TypeObject(A); goto $$block12121~f;
  $$block12121~f: assert (stack0o != null); goto $$block12121~e;
  $$block12121~e: assert ((((($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame])) || ($Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]))) && ($Heap[stack0o, $inv] <: A)) && ($Heap[stack0o, $localinv] == $typeof(stack0o))); goto $$block12121~d;
  $$block12121~d: $Heap := $Heap[stack0o, $localinv := System.Object]; goto $$block12121~c;
  $$block12121~c: havoc temp0; goto $$block12121~b;
  $$block12121~b: $Heap := $Heap[stack0o, $exposeVersion := temp0]; goto $$block12121~a;
  $$block12121~a: assume IsHeap($Heap); goto block12138;
  block12138: stack0i := 10; goto $$block12138~e;
  $$block12138~e: assert (this != null); goto $$block12138~d;
  $$block12138~d: havoc temp1; goto $$block12138~c;
  $$block12138~c: $Heap := $Heap[this, $exposeVersion := temp1]; goto $$block12138~b;
  $$block12138~b: $Heap := $Heap[this, A.f := stack0i]; goto $$block12138~a;
  $$block12138~a: assume IsHeap($Heap); goto block12274;
  block12274: stack0o := local1; goto $$block12274~h;
  $$block12274~h: havoc stack1s; goto $$block12274~g;
  $$block12274~g: assume $IsTokenForType(stack1s, A); goto $$block12274~f;
  $$block12274~f: stack1o := TypeObject(A); goto $$block12274~e;
  $$block12274~e: assert (stack0o != null); goto $$block12274~d;
  $$block12274~d: assert ($Heap[stack0o, $localinv] == System.Object); goto $$block12274~c;
  $$block12274~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == stack0o)) && ($Heap[$p, $ownerFrame] == A)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block12274~b;
  $$block12274~b: $Heap := $Heap[stack0o, $localinv := $typeof(stack0o)]; goto $$block12274~a;
  $$block12274~a: assume IsHeap($Heap); goto block12240;
  block12240: return;
  
}

procedure A.FieldUpdateOnOtherFieldWithGetterQuery(this : ref);
  requires (#A.get_Value($Heap, this) == 5);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  ensures (#A.get_Value($Heap, this) == 5);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old((($o != this) || ($f != A.f)))) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation A.FieldUpdateOnOtherFieldWithGetterQuery(this : ref) {
  var local1 : ref where $Is(local1, A);
  var stack0o : ref;
  var stack1s : struct;
  var stack1o : ref;
  var temp0 : exposeVersionType;
  var stack0i : int;
  var temp1 : exposeVersionType;
  entry: assume $IsNotNull(this, A); goto $$entry~ab;
  $$entry~ab: assume ($Heap[this, $allocated] == true); goto block13005;
  block13005: goto block13158;
  block13158: local1 := this; goto $$block13158~j;
  $$block13158~j: stack0o := local1; goto $$block13158~i;
  $$block13158~i: havoc stack1s; goto $$block13158~h;
  $$block13158~h: assume $IsTokenForType(stack1s, A); goto $$block13158~g;
  $$block13158~g: stack1o := TypeObject(A); goto $$block13158~f;
  $$block13158~f: assert (stack0o != null); goto $$block13158~e;
  $$block13158~e: assert ((((($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame])) || ($Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]))) && ($Heap[stack0o, $inv] <: A)) && ($Heap[stack0o, $localinv] == $typeof(stack0o))); goto $$block13158~d;
  $$block13158~d: $Heap := $Heap[stack0o, $localinv := System.Object]; goto $$block13158~c;
  $$block13158~c: havoc temp0; goto $$block13158~b;
  $$block13158~b: $Heap := $Heap[stack0o, $exposeVersion := temp0]; goto $$block13158~a;
  $$block13158~a: assume IsHeap($Heap); goto block13175;
  block13175: stack0i := 10; goto $$block13175~e;
  $$block13175~e: assert (this != null); goto $$block13175~d;
  $$block13175~d: havoc temp1; goto $$block13175~c;
  $$block13175~c: $Heap := $Heap[this, $exposeVersion := temp1]; goto $$block13175~b;
  $$block13175~b: $Heap := $Heap[this, A.f := stack0i]; goto $$block13175~a;
  $$block13175~a: assume IsHeap($Heap); goto block13311;
  block13311: stack0o := local1; goto $$block13311~h;
  $$block13311~h: havoc stack1s; goto $$block13311~g;
  $$block13311~g: assume $IsTokenForType(stack1s, A); goto $$block13311~f;
  $$block13311~f: stack1o := TypeObject(A); goto $$block13311~e;
  $$block13311~e: assert (stack0o != null); goto $$block13311~d;
  $$block13311~d: assert ($Heap[stack0o, $localinv] == System.Object); goto $$block13311~c;
  $$block13311~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == stack0o)) && ($Heap[$p, $ownerFrame] == A)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block13311~b;
  $$block13311~b: $Heap := $Heap[stack0o, $localinv := $typeof(stack0o)]; goto $$block13311~a;
  $$block13311~a: assume IsHeap($Heap); goto block13277;
  block13277: return;
  
}

axiom (forall $Heap : <x>[ref, name]x, this : ref, p$in : int, q$in : int :: {#A.DummyPure$System.Int32$System.Int32($Heap, this, p$in, q$in)} ((((IsHeap($Heap) && InRange(p$in, System.Int32)) && InRange(q$in, System.Int32)) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))) ==> (InRange(#A.DummyPure$System.Int32$System.Int32($Heap, this, p$in, q$in), System.Int32) && (#A.DummyPure$System.Int32$System.Int32($Heap, this, p$in, q$in) == (p$in + q$in)))));
procedure A.DummyPure$System.Int32$System.Int32(this : ref, p$in : int where InRange(p$in, System.Int32), q$in : int where InRange(q$in, System.Int32)) returns ($result : int where InRange($result, System.Int32));
  free requires true;
  free requires true;
  requires (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))));
  free requires ($AsPureObject(this) == this);
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures true;
  free ensures InRange($result, System.Int32);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures ($Heap == old($Heap));
  free ensures ($result == #A.DummyPure$System.Int32$System.Int32($Heap, this, p$in, q$in));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} ((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation A.DummyPure$System.Int32$System.Int32(this : ref, p$in : int, q$in : int) returns ($result : int) {
  var p : int where InRange(p, System.Int32);
  var q : int where InRange(q, System.Int32);
  var stack0i : int;
  var return.value : int where InRange(return.value, System.Int32);
  var SS$Display.Return.Local : int where InRange(SS$Display.Return.Local, System.Int32);
  entry: assume $IsNotNull(this, A); goto $$entry~ae;
  $$entry~ae: assume ($Heap[this, $allocated] == true); goto $$entry~ad;
  $$entry~ad: p := p$in; goto $$entry~ac;
  $$entry~ac: q := q$in; goto block13821;
  block13821: goto block13838;
  block13838: stack0i := (p + q); goto $$block13838~a;
  $$block13838~a: return.value := stack0i; goto block13855;
  block13855: SS$Display.Return.Local := return.value; goto $$block13855~b;
  $$block13855~b: stack0i := return.value; goto $$block13855~a;
  $$block13855~a: $result := stack0i; return;
  
}

procedure A.PureCall$A$notnull(this : ref, o$in : ref where $IsNotNull(o$in, A));
  free requires ($Heap[o$in, $allocated] == true);
  requires (#A.get_Value($Heap, this) == 5);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[o$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[o$in, $ownerRef], $inv] <: $Heap[o$in, $ownerFrame])) || ($Heap[$Heap[o$in, $ownerRef], $localinv] == $BaseClass($Heap[o$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[o$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[o$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  ensures (#A.get_Value($Heap, this) == 5);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation A.PureCall$A$notnull(this : ref, o$in : ref) {
  var o : ref where $IsNotNull(o, A);
  var stack0i : int;
  var stack1i : int;
  entry: assume $IsNotNull(this, A); goto $$entry~ag;
  $$entry~ag: assume ($Heap[this, $allocated] == true); goto $$entry~af;
  $$entry~af: o := o$in; goto block14280;
  block14280: goto block14382;
  block14382: assert (this != null); goto $$block14382~k;
  $$block14382~k: stack0i := $Heap[this, A.value]; goto $$block14382~j;
  $$block14382~j: assert (this != null); goto $$block14382~i;
  $$block14382~i: stack1i := $Heap[this, A.f]; goto $$block14382~h;
  $$block14382~h: assert (this != null); goto $$block14382~g;
  $$block14382~g: call stack0i := A.DummyPure$System.Int32$System.Int32(this, stack0i, stack1i); goto $$block14382~f;
  $$block14382~f: assert (o != null); goto $$block14382~e;
  $$block14382~e: stack0i := $Heap[o, A.value]; goto $$block14382~d;
  $$block14382~d: assert (o != null); goto $$block14382~c;
  $$block14382~c: stack1i := $Heap[o, A.f]; goto $$block14382~b;
  $$block14382~b: assert (o != null); goto $$block14382~a;
  $$block14382~a: call stack0i := A.DummyPure$System.Int32$System.Int32(o, stack0i, stack1i); goto block14484;
  block14484: return;
  
}

procedure A..ctor(this : ref);
  free requires (forall $o : ref :: (($o != this) ==> ($Heap[$o, $ownerRef] != this)));
  free requires (($Heap[this, $ownerRef] == this) && ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder));
  free requires (forall $o : ref :: ((($Heap[$o, $ownerRef] == $Heap[this, $ownerRef]) && ($Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame])) ==> ($o == this)));
  free requires ($BeingConstructed == this);
  modifies $Heap;
  ensures ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == A)) && ($Heap[this, $localinv] == $typeof(this)));
  ensures (($Heap[this, $ownerRef] == old($Heap)[this, $ownerRef]) && ($Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame]));
  ensures ($Heap[this, $sharingMode] == $SharingMode_Unshared);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(A <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

implementation A..ctor(this : ref) {
  entry: assume $IsNotNull(this, A); goto $$entry~ak;
  $$entry~ak: assume ($Heap[this, $allocated] == true); goto $$entry~aj;
  $$entry~aj: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto $$entry~ai;
  $$entry~ai: assume ($Heap[this, A.value] == 0); goto $$entry~ah;
  $$entry~ah: assume ($Heap[this, A.f] == 0); goto block14841;
  block14841: goto block14858;
  block14858: assert (this != null); goto $$block14858~f;
  $$block14858~f: call System.Object..ctor(this); goto $$block14858~e;
  $$block14858~e: assert (this != null); goto $$block14858~d;
  $$block14858~d: assert (($Heap[this, $inv] == System.Object) && ($Heap[this, $localinv] == $typeof(this))); goto $$block14858~c;
  $$block14858~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == A)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block14858~b;
  $$block14858~b: $Heap := $Heap[this, $inv := A]; goto $$block14858~a;
  $$block14858~a: assume IsHeap($Heap); return;
  
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
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(System.Object <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

axiom (S <: S);
axiom ($BaseClass(S) == System.Object);
axiom ((S <: $BaseClass(S)) && (AsDirectSubClass(S, $BaseClass(S)) == S));
axiom (!$IsImmutable(S) && ($AsMutable(S) == S));
axiom (forall $U : name :: {($U <: S)} (($U <: S) ==> ($U == S)));
procedure S..ctor(this : ref);
  free requires (forall $o : ref :: (($o != this) ==> ($Heap[$o, $ownerRef] != this)));
  free requires (($Heap[this, $ownerRef] == this) && ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder));
  free requires (forall $o : ref :: ((($Heap[$o, $ownerRef] == $Heap[this, $ownerRef]) && ($Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame])) ==> ($o == this)));
  free requires ($BeingConstructed == this);
  modifies $Heap;
  ensures ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == S)) && ($Heap[this, $localinv] == $typeof(this)));
  ensures (($Heap[this, $ownerRef] == old($Heap)[this, $ownerRef]) && ($Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame]));
  ensures ($Heap[this, $sharingMode] == $SharingMode_Unshared);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(S <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

implementation S..ctor(this : ref) {
  entry: assume $IsNotNull(this, S); goto $$entry~an;
  $$entry~an: assume ($Heap[this, $allocated] == true); goto $$entry~am;
  $$entry~am: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto $$entry~al;
  $$entry~al: assume ($Heap[this, S.b] == false); goto block15028;
  block15028: goto block15045;
  block15045: assert (this != null); goto $$block15045~f;
  $$block15045~f: call System.Object..ctor(this); goto $$block15045~e;
  $$block15045~e: assert (this != null); goto $$block15045~d;
  $$block15045~d: assert (($Heap[this, $inv] == System.Object) && ($Heap[this, $localinv] == $typeof(this))); goto $$block15045~c;
  $$block15045~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == S)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block15045~b;
  $$block15045~b: $Heap := $Heap[this, $inv := S]; goto $$block15045~a;
  $$block15045~a: assume IsHeap($Heap); return;
  
}

axiom (forall $U : name :: {($U <: System.Boolean)} (($U <: System.Boolean) ==> ($U == System.Boolean)));
axiom (T <: T);
axiom ($BaseClass(T) == System.Object);
axiom ((T <: $BaseClass(T)) && (AsDirectSubClass(T, $BaseClass(T)) == T));
axiom (!$IsImmutable(T) && ($AsMutable(T) == T));
axiom (forall $U : name :: {($U <: T)} (($U <: T) ==> ($U == T)));
axiom (forall $Heap : <x>[ref, name]x, this : ref :: {#T.get_Value($Heap, this)} ((IsHeap($Heap) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))) ==> InRange(#T.get_Value($Heap, this), System.Int32)));
axiom (forall $Heap : <x>[ref, name]x, this : ref :: {#T.get_Value($Heap, this)} (((((((this != null) && ($typeof(this) <: T)) && ($Heap[this, $inv] == $typeof(this))) && ($Heap[this, $localinv] == $typeof(this))) && IsHeap($Heap)) && ($Heap[this, $allocated] == true)) ==> (#T.get_Value($Heap, this) == ##T.get_Value($Heap[this, $exposeVersion]))));
procedure T.get_Value(this : ref) returns ($result : int where InRange($result, System.Int32));
  requires (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))));
  free requires ($AsPureObject(this) == this);
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures true;
  free ensures InRange($result, System.Int32);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures ($Heap == old($Heap));
  free ensures ($result == #T.get_Value($Heap, this));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} ((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation T.get_Value(this : ref) returns ($result : int) {
  var return.value : int where InRange(return.value, System.Int32);
  var SS$Display.Return.Local : int where InRange(SS$Display.Return.Local, System.Int32);
  var stack0i : int;
  entry: assume $IsNotNull(this, T); goto $$entry~ao;
  $$entry~ao: assume ($Heap[this, $allocated] == true); goto block15232;
  block15232: goto block15249;
  block15249: assert (this != null); goto $$block15249~a;
  $$block15249~a: return.value := $Heap[this, T.value]; goto block15266;
  block15266: SS$Display.Return.Local := return.value; goto $$block15266~b;
  $$block15266~b: stack0i := return.value; goto $$block15266~a;
  $$block15266~a: $result := stack0i; return;
  
}

procedure T.set_Value$System.Int32(this : ref, value$in : int where InRange(value$in, System.Int32));
  free requires true;
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old((($o != this) || ($f != T.value)))) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation T.set_Value$System.Int32(this : ref, value$in : int) {
  var value : int where InRange(value, System.Int32);
  var temp0 : exposeVersionType;
  entry: assume $IsNotNull(this, T); goto $$entry~aq;
  $$entry~aq: assume ($Heap[this, $allocated] == true); goto $$entry~ap;
  $$entry~ap: value := value$in; goto block15487;
  block15487: goto block15504;
  block15504: assert (this != null); goto $$block15504~d;
  $$block15504~d: havoc temp0; goto $$block15504~c;
  $$block15504~c: $Heap := $Heap[this, $exposeVersion := temp0]; goto $$block15504~b;
  $$block15504~b: $Heap := $Heap[this, T.value := value]; goto $$block15504~a;
  $$block15504~a: assume IsHeap($Heap); return;
  
}

procedure T.m(this : ref);
  requires ($Heap[this, T.s] != null);
  requires ((((($Heap[$Heap[this, T.s], $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[$Heap[this, T.s], $ownerRef], $inv] <: $Heap[$Heap[this, T.s], $ownerFrame])) || ($Heap[$Heap[$Heap[this, T.s], $ownerRef], $localinv] == $BaseClass($Heap[$Heap[this, T.s], $ownerFrame]))) && ($Heap[$Heap[this, T.s], $inv] == S)) && ($Heap[$Heap[this, T.s], $localinv] == $typeof($Heap[this, T.s])));
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old((($o != $Heap[this, T.s]) || ($f != S.b)))) && old(((($o != $Heap[this, T.s]) || ($f != $exposeVersion)) && (($o != this) || ($f != $exposeVersion))))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation T.m(this : ref) {
  var stack0o : ref;
  var local2 : ref where $Is(local2, S);
  var stack1s : struct;
  var stack1o : ref;
  var temp0 : exposeVersionType;
  var stack1b : bool;
  var temp1 : exposeVersionType;
  entry: assume $IsNotNull(this, T); goto $$entry~ar;
  $$entry~ar: assume ($Heap[this, $allocated] == true); goto block16337;
  block16337: goto block16541;
  block16541: assume (#T.get_Value($Heap, this) == 5); goto block16626;
  block16626: assert (this != null); goto $$block16626~k;
  $$block16626~k: local2 := $Heap[this, T.s]; goto $$block16626~j;
  $$block16626~j: stack0o := local2; goto $$block16626~i;
  $$block16626~i: havoc stack1s; goto $$block16626~h;
  $$block16626~h: assume $IsTokenForType(stack1s, S); goto $$block16626~g;
  $$block16626~g: stack1o := TypeObject(S); goto $$block16626~f;
  $$block16626~f: assert (stack0o != null); goto $$block16626~e;
  $$block16626~e: assert ((((($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame])) || ($Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]))) && ($Heap[stack0o, $inv] <: S)) && ($Heap[stack0o, $localinv] == $typeof(stack0o))); goto $$block16626~d;
  $$block16626~d: $Heap := $Heap[stack0o, $localinv := System.Object]; goto $$block16626~c;
  $$block16626~c: havoc temp0; goto $$block16626~b;
  $$block16626~b: $Heap := $Heap[stack0o, $exposeVersion := temp0]; goto $$block16626~a;
  $$block16626~a: assume IsHeap($Heap); goto block16643;
  block16643: assert (this != null); goto $$block16643~g;
  $$block16643~g: stack0o := $Heap[this, T.s]; goto $$block16643~f;
  $$block16643~f: stack1b := false; goto $$block16643~e;
  $$block16643~e: assert (stack0o != null); goto $$block16643~d;
  $$block16643~d: havoc temp1; goto $$block16643~c;
  $$block16643~c: $Heap := $Heap[stack0o, $exposeVersion := temp1]; goto $$block16643~b;
  $$block16643~b: $Heap := $Heap[stack0o, S.b := stack1b]; goto $$block16643~a;
  $$block16643~a: assume IsHeap($Heap); goto block16779;
  block16779: stack0o := local2; goto $$block16779~h;
  $$block16779~h: havoc stack1s; goto $$block16779~g;
  $$block16779~g: assume $IsTokenForType(stack1s, S); goto $$block16779~f;
  $$block16779~f: stack1o := TypeObject(S); goto $$block16779~e;
  $$block16779~e: assert (stack0o != null); goto $$block16779~d;
  $$block16779~d: assert ($Heap[stack0o, $localinv] == System.Object); goto $$block16779~c;
  $$block16779~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == stack0o)) && ($Heap[$p, $ownerFrame] == S)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block16779~b;
  $$block16779~b: $Heap := $Heap[stack0o, $localinv := $typeof(stack0o)]; goto $$block16779~a;
  $$block16779~a: assume IsHeap($Heap); goto block16660;
  block16660: assert (#T.get_Value($Heap, this) == 5); goto block16745;
  block16745: return;
  
}

axiom (System.String <: System.String);
axiom ($BaseClass(System.String) == System.Object);
axiom ((System.String <: $BaseClass(System.String)) && (AsDirectSubClass(System.String, $BaseClass(System.String)) == System.String));
axiom ($IsImmutable(System.String) && ($AsImmutable(System.String) == System.String));
axiom (System.IComparable <: System.Object);
axiom $IsMemberlessType(System.IComparable);
axiom (System.String <: System.IComparable);
axiom (System.ICloneable <: System.Object);
axiom $IsMemberlessType(System.ICloneable);
axiom (System.String <: System.ICloneable);
axiom (System.IConvertible <: System.Object);
axiom $IsMemberlessType(System.IConvertible);
axiom (System.String <: System.IConvertible);
axiom (System.IComparable`1...System.String <: System.Object);
axiom $IsMemberlessType(System.IComparable`1...System.String);
axiom (System.String <: System.IComparable`1...System.String);
axiom (System.Collections.Generic.IEnumerable`1...System.Char <: System.Object);
axiom (System.Collections.IEnumerable <: System.Object);
axiom $IsMemberlessType(System.Collections.IEnumerable);
axiom (System.Collections.Generic.IEnumerable`1...System.Char <: System.Collections.IEnumerable);
axiom $IsMemberlessType(System.Collections.Generic.IEnumerable`1...System.Char);
axiom (System.String <: System.Collections.Generic.IEnumerable`1...System.Char);
axiom (System.String <: System.Collections.IEnumerable);
axiom (System.IEquatable`1...System.String <: System.Object);
axiom $IsMemberlessType(System.IEquatable`1...System.String);
axiom (System.String <: System.IEquatable`1...System.String);
axiom (forall $U : name :: {($U <: System.String)} (($U <: System.String) ==> ($U == System.String)));
procedure T.n(this : ref);
  requires ($Heap[this, T.s] != null);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old((($o != this) || ($f != T.b)))) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation T.n(this : ref) {
  var stack0o : ref;
  var local2 : ref where $Is(local2, T);
  var stack1s : struct;
  var stack1o : ref;
  var temp0 : exposeVersionType;
  var stack0b : bool;
  var temp1 : exposeVersionType;
  entry: assume $IsNotNull(this, T); goto $$entry~as;
  $$entry~as: assume ($Heap[this, $allocated] == true); goto block17731;
  block17731: goto block17884;
  block17884: assume (#T.get_Value($Heap, this) == 5); goto block17969;
  block17969: local2 := this; goto $$block17969~j;
  $$block17969~j: stack0o := local2; goto $$block17969~i;
  $$block17969~i: havoc stack1s; goto $$block17969~h;
  $$block17969~h: assume $IsTokenForType(stack1s, T); goto $$block17969~g;
  $$block17969~g: stack1o := TypeObject(T); goto $$block17969~f;
  $$block17969~f: assert (stack0o != null); goto $$block17969~e;
  $$block17969~e: assert ((((($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame])) || ($Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]))) && ($Heap[stack0o, $inv] <: T)) && ($Heap[stack0o, $localinv] == $typeof(stack0o))); goto $$block17969~d;
  $$block17969~d: $Heap := $Heap[stack0o, $localinv := System.Object]; goto $$block17969~c;
  $$block17969~c: havoc temp0; goto $$block17969~b;
  $$block17969~b: $Heap := $Heap[stack0o, $exposeVersion := temp0]; goto $$block17969~a;
  $$block17969~a: assume IsHeap($Heap); goto block17986;
  block17986: stack0b := false; goto $$block17986~e;
  $$block17986~e: assert (this != null); goto $$block17986~d;
  $$block17986~d: havoc temp1; goto $$block17986~c;
  $$block17986~c: $Heap := $Heap[this, $exposeVersion := temp1]; goto $$block17986~b;
  $$block17986~b: $Heap := $Heap[this, T.b := stack0b]; goto $$block17986~a;
  $$block17986~a: assume IsHeap($Heap); goto block18122;
  block18122: stack0o := local2; goto $$block18122~h;
  $$block18122~h: havoc stack1s; goto $$block18122~g;
  $$block18122~g: assume $IsTokenForType(stack1s, T); goto $$block18122~f;
  $$block18122~f: stack1o := TypeObject(T); goto $$block18122~e;
  $$block18122~e: assert (stack0o != null); goto $$block18122~d;
  $$block18122~d: assert ($Heap[stack0o, $localinv] == System.Object); goto $$block18122~c;
  $$block18122~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == stack0o)) && ($Heap[$p, $ownerFrame] == T)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block18122~b;
  $$block18122~b: $Heap := $Heap[stack0o, $localinv := $typeof(stack0o)]; goto $$block18122~a;
  $$block18122~a: assume IsHeap($Heap); goto block18003;
  block18003: assert (#T.get_Value($Heap, this) == 5); goto block18088;
  block18088: return;
  
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
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(T <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

implementation T..ctor(this : ref) {
  entry: assume $IsNotNull(this, T); goto $$entry~ax;
  $$entry~ax: assume ($Heap[this, $allocated] == true); goto $$entry~aw;
  $$entry~aw: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto $$entry~av;
  $$entry~av: assume ($Heap[this, T.s] == null); goto $$entry~au;
  $$entry~au: assume ($Heap[this, T.value] == 0); goto $$entry~at;
  $$entry~at: assume ($Heap[this, T.b] == false); goto block18734;
  block18734: goto block18751;
  block18751: assert (this != null); goto $$block18751~f;
  $$block18751~f: call System.Object..ctor(this); goto $$block18751~e;
  $$block18751~e: assert (this != null); goto $$block18751~d;
  $$block18751~d: assert (($Heap[this, $inv] == System.Object) && ($Heap[this, $localinv] == $typeof(this))); goto $$block18751~c;
  $$block18751~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == T)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block18751~b;
  $$block18751~b: $Heap := $Heap[this, $inv := T]; goto $$block18751~a;
  $$block18751~a: assume IsHeap($Heap); return;
  
}

axiom (C <: C);
axiom ($BaseClass(C) == System.Object);
axiom ((C <: $BaseClass(C)) && (AsDirectSubClass(C, $BaseClass(C)) == C));
axiom (!$IsImmutable(C) && ($AsMutable(C) == C));
axiom (forall $U : name :: {($U <: C)} (($U <: C) ==> ($U == C)));
axiom (forall $Heap : <x>[ref, name]x, this : ref :: {#C.foo($Heap, this)} ((IsHeap($Heap) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))) ==> InRange(#C.foo($Heap, this), System.Int32)));
axiom (forall $Heap : <x>[ref, name]x, this : ref :: {#C.foo($Heap, this)} (((((((this != null) && ($typeof(this) <: C)) && ($Heap[this, $inv] == $typeof(this))) && ($Heap[this, $localinv] == $typeof(this))) && IsHeap($Heap)) && ($Heap[this, $allocated] == true)) ==> (#C.foo($Heap, this) == ##C.foo($Heap[this, $exposeVersion]))));
procedure C.foo(this : ref) returns ($result : int where InRange($result, System.Int32));
  requires (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))));
  free requires ($AsPureObject(this) == this);
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures true;
  free ensures InRange($result, System.Int32);
  ensures (this != null);
  ensures ($result == $Heap[this, C.x]);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures ($Heap == old($Heap));
  free ensures ($result == #C.foo($Heap, this));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} ((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation C.foo(this : ref) returns ($result : int) {
  var return.value : int where InRange(return.value, System.Int32);
  var SS$Display.Return.Local : int where InRange(SS$Display.Return.Local, System.Int32);
  var stack0i : int;
  entry: assume $IsNotNull(this, C); goto $$entry~ay;
  $$entry~ay: assume ($Heap[this, $allocated] == true); goto block19074;
  block19074: goto block19091;
  block19091: assert (this != null); goto $$block19091~a;
  $$block19091~a: return.value := $Heap[this, C.x]; goto block19244;
  block19244: SS$Display.Return.Local := return.value; goto $$block19244~b;
  $$block19244~b: stack0i := return.value; goto $$block19244~a;
  $$block19244~a: $result := stack0i; return;
  
}

procedure C..ctor(this : ref);
  free requires (forall $o : ref :: (($o != this) ==> ($Heap[$o, $ownerRef] != this)));
  free requires (($Heap[this, $ownerRef] == this) && ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder));
  free requires (forall $o : ref :: ((($Heap[$o, $ownerRef] == $Heap[this, $ownerRef]) && ($Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame])) ==> ($o == this)));
  free requires ($BeingConstructed == this);
  modifies $Heap;
  ensures ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == C)) && ($Heap[this, $localinv] == $typeof(this)));
  ensures (($Heap[this, $ownerRef] == old($Heap)[this, $ownerRef]) && ($Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame]));
  ensures ($Heap[this, $sharingMode] == $SharingMode_Unshared);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(C <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

implementation C..ctor(this : ref) {
  entry: assume $IsNotNull(this, C); goto $$entry~bb;
  $$entry~bb: assume ($Heap[this, $allocated] == true); goto $$entry~ba;
  $$entry~ba: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto $$entry~az;
  $$entry~az: assume ($Heap[this, C.x] == 0); goto block19516;
  block19516: goto block19533;
  block19533: assert (this != null); goto $$block19533~f;
  $$block19533~f: call System.Object..ctor(this); goto $$block19533~e;
  $$block19533~e: assert (this != null); goto $$block19533~d;
  $$block19533~d: assert (($Heap[this, $inv] == System.Object) && ($Heap[this, $localinv] == $typeof(this))); goto $$block19533~c;
  $$block19533~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == C)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block19533~b;
  $$block19533~b: $Heap := $Heap[this, $inv := C]; goto $$block19533~a;
  $$block19533~a: assume IsHeap($Heap); return;
  
}

axiom (D <: D);
axiom ($BaseClass(D) == System.Object);
axiom ((D <: $BaseClass(D)) && (AsDirectSubClass(D, $BaseClass(D)) == D));
axiom (!$IsImmutable(D) && ($AsMutable(D) == D));
axiom (forall $U : name :: {($U <: D)} (($U <: D) ==> ($U == D)));
procedure D.bar(this : ref);
  requires ($Heap[this, D.c] != null);
  requires (#C.foo($Heap, $Heap[this, D.c]) == 5);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  ensures (#C.foo($Heap, $Heap[this, D.c]) == 5);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old((($o != this) || ($f != D.x)))) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation D.bar(this : ref) {
  var local1 : ref where $Is(local1, D);
  var stack0o : ref;
  var stack1s : struct;
  var stack1o : ref;
  var temp0 : exposeVersionType;
  var local2 : int where InRange(local2, System.Int32);
  var stack0i : int;
  var temp1 : exposeVersionType;
  entry: assume $IsNotNull(this, D); goto $$entry~bc;
  $$entry~bc: assume ($Heap[this, $allocated] == true); goto block19992;
  block19992: goto block20196;
  block20196: local1 := this; goto $$block20196~j;
  $$block20196~j: stack0o := local1; goto $$block20196~i;
  $$block20196~i: havoc stack1s; goto $$block20196~h;
  $$block20196~h: assume $IsTokenForType(stack1s, D); goto $$block20196~g;
  $$block20196~g: stack1o := TypeObject(D); goto $$block20196~f;
  $$block20196~f: assert (stack0o != null); goto $$block20196~e;
  $$block20196~e: assert ((((($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame])) || ($Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]))) && ($Heap[stack0o, $inv] <: D)) && ($Heap[stack0o, $localinv] == $typeof(stack0o))); goto $$block20196~d;
  $$block20196~d: $Heap := $Heap[stack0o, $localinv := System.Object]; goto $$block20196~c;
  $$block20196~c: havoc temp0; goto $$block20196~b;
  $$block20196~b: $Heap := $Heap[stack0o, $exposeVersion := temp0]; goto $$block20196~a;
  $$block20196~a: assume IsHeap($Heap); goto block20213;
  block20213: assert (this != null); goto $$block20213~i;
  $$block20213~i: local2 := $Heap[this, D.x]; goto $$block20213~h;
  $$block20213~h: stack0i := 1; goto $$block20213~g;
  $$block20213~g: stack0i := (local2 + stack0i); goto $$block20213~f;
  $$block20213~f: assert (this != null); goto $$block20213~e;
  $$block20213~e: havoc temp1; goto $$block20213~d;
  $$block20213~d: $Heap := $Heap[this, $exposeVersion := temp1]; goto $$block20213~c;
  $$block20213~c: $Heap := $Heap[this, D.x := stack0i]; goto $$block20213~b;
  $$block20213~b: assume IsHeap($Heap); goto $$block20213~a;
  $$block20213~a: stack0i := local2; goto block20349;
  block20349: stack0o := local1; goto $$block20349~h;
  $$block20349~h: havoc stack1s; goto $$block20349~g;
  $$block20349~g: assume $IsTokenForType(stack1s, D); goto $$block20349~f;
  $$block20349~f: stack1o := TypeObject(D); goto $$block20349~e;
  $$block20349~e: assert (stack0o != null); goto $$block20349~d;
  $$block20349~d: assert ($Heap[stack0o, $localinv] == System.Object); goto $$block20349~c;
  $$block20349~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == stack0o)) && ($Heap[$p, $ownerFrame] == D)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block20349~b;
  $$block20349~b: $Heap := $Heap[stack0o, $localinv := $typeof(stack0o)]; goto $$block20349~a;
  $$block20349~a: assume IsHeap($Heap); goto block20315;
  block20315: return;
  
}

procedure D..ctor(this : ref);
  free requires (forall $o : ref :: (($o != this) ==> ($Heap[$o, $ownerRef] != this)));
  free requires (($Heap[this, $ownerRef] == this) && ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder));
  free requires (forall $o : ref :: ((($Heap[$o, $ownerRef] == $Heap[this, $ownerRef]) && ($Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame])) ==> ($o == this)));
  free requires ($BeingConstructed == this);
  modifies $Heap;
  ensures ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == D)) && ($Heap[this, $localinv] == $typeof(this)));
  ensures (($Heap[this, $ownerRef] == old($Heap)[this, $ownerRef]) && ($Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame]));
  ensures ($Heap[this, $sharingMode] == $SharingMode_Unshared);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(D <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

implementation D..ctor(this : ref) {
  entry: assume $IsNotNull(this, D); goto $$entry~bg;
  $$entry~bg: assume ($Heap[this, $allocated] == true); goto $$entry~bf;
  $$entry~bf: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto $$entry~be;
  $$entry~be: assume ($Heap[this, D.x] == 0); goto $$entry~bd;
  $$entry~bd: assume ($Heap[this, D.c] == null); goto block20893;
  block20893: goto block20910;
  block20910: assert (this != null); goto $$block20910~f;
  $$block20910~f: call System.Object..ctor(this); goto $$block20910~e;
  $$block20910~e: assert (this != null); goto $$block20910~d;
  $$block20910~d: assert (($Heap[this, $inv] == System.Object) && ($Heap[this, $localinv] == $typeof(this))); goto $$block20910~c;
  $$block20910~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == D)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block20910~b;
  $$block20910~b: $Heap := $Heap[this, $inv := D]; goto $$block20910~a;
  $$block20910~a: assume IsHeap($Heap); return;
  
}

axiom (QClient <: QClient);
axiom ($BaseClass(QClient) == System.Object);
axiom ((QClient <: $BaseClass(QClient)) && (AsDirectSubClass(QClient, $BaseClass(QClient)) == QClient));
axiom (!$IsImmutable(QClient) && ($AsMutable(QClient) == QClient));
axiom (forall $U : name :: {($U <: QClient)} (($U <: QClient) ==> ($U == QClient)));
axiom (Q <: Q);
axiom ($BaseClass(Q) == System.Object);
axiom ((Q <: $BaseClass(Q)) && (AsDirectSubClass(Q, $BaseClass(Q)) == Q));
axiom (!$IsImmutable(Q) && ($AsMutable(Q) == Q));
axiom (forall $U : name :: {($U <: Q)} (($U <: Q) ==> ($U == Q)));
procedure QClient.bar(this : ref);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old((((($o != $Heap[this, QClient.q]) || ($f != Q.f)) && (($o != this) || ($f != QClient.f))) && (($o != $Heap[this, QClient.qclient]) || ($f != QClient.f))))) && old((((($o != $Heap[this, QClient.q]) || ($f != $exposeVersion)) && (($o != $Heap[this, QClient.qclient]) || ($f != $exposeVersion))) && (($o != this) || ($f != $exposeVersion))))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation QClient.bar(this : ref) {
  var stack0o : ref;
  var stack1i : int;
  var temp0 : exposeVersionType;
  var stack0i : int;
  var temp1 : exposeVersionType;
  var temp2 : exposeVersionType;
  entry: assume $IsNotNull(this, QClient); goto $$entry~bh;
  $$entry~bh: assume ($Heap[this, $allocated] == true); goto block21250;
  block21250: goto block21267;
  block21267: assume (#Q.blah$QClient($Heap[this, QClient.q], $Heap[this, QClient.qclient]) == 5); goto block21352;
  block21352: assert (this != null); goto $$block21352~v;
  $$block21352~v: stack0o := $Heap[this, QClient.q]; goto $$block21352~u;
  $$block21352~u: stack1i := 10; goto $$block21352~t;
  $$block21352~t: assert (stack0o != null); goto $$block21352~s;
  $$block21352~s: havoc temp0; goto $$block21352~r;
  $$block21352~r: $Heap := $Heap[stack0o, $exposeVersion := temp0]; goto $$block21352~q;
  $$block21352~q: $Heap := $Heap[stack0o, Q.f := stack1i]; goto $$block21352~p;
  $$block21352~p: assume IsHeap($Heap); goto $$block21352~o;
  $$block21352~o: stack0i := 10; goto $$block21352~n;
  $$block21352~n: assert (this != null); goto $$block21352~m;
  $$block21352~m: havoc temp1; goto $$block21352~l;
  $$block21352~l: $Heap := $Heap[this, $exposeVersion := temp1]; goto $$block21352~k;
  $$block21352~k: $Heap := $Heap[this, QClient.f := stack0i]; goto $$block21352~j;
  $$block21352~j: assume IsHeap($Heap); goto $$block21352~i;
  $$block21352~i: assert (this != null); goto $$block21352~h;
  $$block21352~h: stack0o := $Heap[this, QClient.qclient]; goto $$block21352~g;
  $$block21352~g: stack1i := 10; goto $$block21352~f;
  $$block21352~f: assert (stack0o != null); goto $$block21352~e;
  $$block21352~e: havoc temp2; goto $$block21352~d;
  $$block21352~d: $Heap := $Heap[stack0o, $exposeVersion := temp2]; goto $$block21352~c;
  $$block21352~c: $Heap := $Heap[stack0o, QClient.f := stack1i]; goto $$block21352~b;
  $$block21352~b: assume IsHeap($Heap); goto $$block21352~a;
  $$block21352~a: assert (#Q.blah$QClient($Heap[this, QClient.q], $Heap[this, QClient.qclient]) == 5); goto block21437;
  block21437: return;
  
}

axiom (forall this : ref, qclient$in : ref :: {#Q.blah$QClient(this, qclient$in)} ($Is(qclient$in, QClient) ==> InRange(#Q.blah$QClient(this, qclient$in), System.Int32)));
procedure QClient..ctor(this : ref);
  free requires (forall $o : ref :: (($o != this) ==> ($Heap[$o, $ownerRef] != this)));
  free requires (($Heap[this, $ownerRef] == this) && ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder));
  free requires (forall $o : ref :: ((($Heap[$o, $ownerRef] == $Heap[this, $ownerRef]) && ($Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame])) ==> ($o == this)));
  free requires ($BeingConstructed == this);
  modifies $Heap;
  ensures ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == QClient)) && ($Heap[this, $localinv] == $typeof(this)));
  ensures (($Heap[this, $ownerRef] == old($Heap)[this, $ownerRef]) && ($Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame]));
  ensures ($Heap[this, $sharingMode] == $SharingMode_Unshared);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(QClient <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

implementation QClient..ctor(this : ref) {
  var stack50000o : ref;
  var stack0o : ref;
  var temp0 : exposeVersionType;
  var temp1 : exposeVersionType;
  entry: assume $IsNotNull(this, QClient); goto $$entry~bk;
  $$entry~bk: assume ($Heap[this, $allocated] == true); goto $$entry~bj;
  $$entry~bj: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto $$entry~bi;
  $$entry~bi: assume ($Heap[this, QClient.f] == 0); goto block21896;
  block21896: goto block21913;
  block21913: havoc stack50000o; goto $$block21913~ad;
  $$block21913~ad: assume ((($Heap[stack50000o, $allocated] == false) && (stack50000o != null)) && ($typeof(stack50000o) == Q)); goto $$block21913~ac;
  $$block21913~ac: assume (($Heap[stack50000o, $ownerRef] == stack50000o) && ($Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder)); goto $$block21913~ab;
  $$block21913~ab: $Heap := $Heap[stack50000o, $allocated := true]; goto $$block21913~aa;
  $$block21913~aa: assert (stack50000o != null); goto $$block21913~z;
  $$block21913~z: call Q..ctor(stack50000o); goto $$block21913~y;
  $$block21913~y: stack0o := stack50000o; goto $$block21913~x;
  $$block21913~x: assert (this != null); goto $$block21913~w;
  $$block21913~w: havoc temp0; goto $$block21913~v;
  $$block21913~v: $Heap := $Heap[this, $exposeVersion := temp0]; goto $$block21913~u;
  $$block21913~u: $Heap := $Heap[this, QClient.q := stack0o]; goto $$block21913~t;
  $$block21913~t: assume IsHeap($Heap); goto $$block21913~s;
  $$block21913~s: havoc stack50000o; goto $$block21913~r;
  $$block21913~r: assume ((($Heap[stack50000o, $allocated] == false) && (stack50000o != null)) && ($typeof(stack50000o) == QClient)); goto $$block21913~q;
  $$block21913~q: assume (($Heap[stack50000o, $ownerRef] == stack50000o) && ($Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder)); goto $$block21913~p;
  $$block21913~p: $Heap := $Heap[stack50000o, $allocated := true]; goto $$block21913~o;
  $$block21913~o: assert (stack50000o != null); goto $$block21913~n;
  $$block21913~n: call QClient..ctor(stack50000o); goto $$block21913~m;
  $$block21913~m: stack0o := stack50000o; goto $$block21913~l;
  $$block21913~l: assert (this != null); goto $$block21913~k;
  $$block21913~k: havoc temp1; goto $$block21913~j;
  $$block21913~j: $Heap := $Heap[this, $exposeVersion := temp1]; goto $$block21913~i;
  $$block21913~i: $Heap := $Heap[this, QClient.qclient := stack0o]; goto $$block21913~h;
  $$block21913~h: assume IsHeap($Heap); goto $$block21913~g;
  $$block21913~g: assert (this != null); goto $$block21913~f;
  $$block21913~f: call System.Object..ctor(this); goto $$block21913~e;
  $$block21913~e: assert (this != null); goto $$block21913~d;
  $$block21913~d: assert (($Heap[this, $inv] == System.Object) && ($Heap[this, $localinv] == $typeof(this))); goto $$block21913~c;
  $$block21913~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == QClient)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block21913~b;
  $$block21913~b: $Heap := $Heap[this, $inv := QClient]; goto $$block21913~a;
  $$block21913~a: assume IsHeap($Heap); return;
  
}

procedure Q..ctor(this : ref);
  free requires (forall $o : ref :: (($o != this) ==> ($Heap[$o, $ownerRef] != this)));
  free requires (($Heap[this, $ownerRef] == this) && ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder));
  free requires (forall $o : ref :: ((($Heap[$o, $ownerRef] == $Heap[this, $ownerRef]) && ($Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame])) ==> ($o == this)));
  free requires ($BeingConstructed == this);
  modifies $Heap;
  ensures ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == Q)) && ($Heap[this, $localinv] == $typeof(this)));
  ensures (($Heap[this, $ownerRef] == old($Heap)[this, $ownerRef]) && ($Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame]));
  ensures ($Heap[this, $sharingMode] == $SharingMode_Unshared);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(Q <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

procedure Q.blah$QClient(this : ref, qclient$in : ref where $Is(qclient$in, QClient)) returns ($result : int where InRange($result, System.Int32));
  free requires ($Heap[qclient$in, $allocated] == true);
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures true;
  free ensures InRange($result, System.Int32);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures ($Heap == old($Heap));
  free ensures ($result == #Q.blah$QClient(this, qclient$in));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} ((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Q.blah$QClient(this : ref, qclient$in : ref) returns ($result : int) {
  var qclient : ref where $Is(qclient, QClient);
  var i : int where InRange(i, System.Int32);
  var return.value : int where InRange(return.value, System.Int32);
  var SS$Display.Return.Local : int where InRange(SS$Display.Return.Local, System.Int32);
  var stack0i : int;
  entry: assume $IsNotNull(this, Q); goto $$entry~bm;
  $$entry~bm: assume ($Heap[this, $allocated] == true); goto $$entry~bl;
  $$entry~bl: qclient := qclient$in; goto block22236;
  block22236: goto block22253;
  block22253: i := 5; goto $$block22253~a;
  $$block22253~a: return.value := i; goto block22270;
  block22270: SS$Display.Return.Local := return.value; goto $$block22270~b;
  $$block22270~b: stack0i := return.value; goto $$block22270~a;
  $$block22270~a: $result := stack0i; return;
  
}

implementation Q..ctor(this : ref) {
  entry: assume $IsNotNull(this, Q); goto $$entry~bp;
  $$entry~bp: assume ($Heap[this, $allocated] == true); goto $$entry~bo;
  $$entry~bo: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto $$entry~bn;
  $$entry~bn: assume ($Heap[this, Q.f] == 0); goto block22508;
  block22508: goto block22525;
  block22525: assert (this != null); goto $$block22525~f;
  $$block22525~f: call System.Object..ctor(this); goto $$block22525~e;
  $$block22525~e: assert (this != null); goto $$block22525~d;
  $$block22525~d: assert (($Heap[this, $inv] == System.Object) && ($Heap[this, $localinv] == $typeof(this))); goto $$block22525~c;
  $$block22525~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == Q)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block22525~b;
  $$block22525~b: $Heap := $Heap[this, $inv := Q]; goto $$block22525~a;
  $$block22525~a: assume IsHeap($Heap); return;
  
}

axiom (X <: X);
axiom ($BaseClass(X) == System.Object);
axiom ((X <: $BaseClass(X)) && (AsDirectSubClass(X, $BaseClass(X)) == X));
axiom (!$IsImmutable(X) && ($AsMutable(X) == X));
axiom (forall $U : name :: {($U <: X)} (($U <: X) ==> ($U == X)));
axiom (forall $Heap : <x>[ref, name]x, this : ref, p$in : int :: {#X.getValue$System.Int32($Heap, this, p$in)} (((IsHeap($Heap) && InRange(p$in, System.Int32)) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))) ==> InRange(#X.getValue$System.Int32($Heap, this, p$in), System.Int32)));
axiom (forall $Heap : <x>[ref, name]x, this : ref, p$in : int :: {#X.getValue$System.Int32($Heap, this, p$in)} (((((((this != null) && ($typeof(this) <: X)) && ($Heap[this, $inv] == $typeof(this))) && ($Heap[this, $localinv] == $typeof(this))) && IsHeap($Heap)) && ($Heap[this, $allocated] == true)) ==> (#X.getValue$System.Int32($Heap, this, p$in) == ##X.getValue$System.Int32($Heap[this, $exposeVersion], p$in))));
procedure X.getValue$System.Int32(this : ref, p$in : int where InRange(p$in, System.Int32)) returns ($result : int where InRange($result, System.Int32));
  free requires true;
  requires (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))));
  free requires ($AsPureObject(this) == this);
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures true;
  free ensures InRange($result, System.Int32);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures ($Heap == old($Heap));
  free ensures ($result == #X.getValue$System.Int32($Heap, this, p$in));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} ((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation X.getValue$System.Int32(this : ref, p$in : int) returns ($result : int) {
  var p : int where InRange(p, System.Int32);
  var return.value : int where InRange(return.value, System.Int32);
  var SS$Display.Return.Local : int where InRange(SS$Display.Return.Local, System.Int32);
  var stack0i : int;
  entry: assume $IsNotNull(this, X); goto $$entry~br;
  $$entry~br: assume ($Heap[this, $allocated] == true); goto $$entry~bq;
  $$entry~bq: p := p$in; goto block22712;
  block22712: goto block22729;
  block22729: assert (this != null); goto $$block22729~a;
  $$block22729~a: return.value := $Heap[this, X.value]; goto block22746;
  block22746: SS$Display.Return.Local := return.value; goto $$block22746~b;
  $$block22746~b: stack0i := return.value; goto $$block22746~a;
  $$block22746~a: $result := stack0i; return;
  
}

procedure X.ObjectCreationWithMethodQuery$X$notnull(this : ref, o$in : ref where $IsNotNull(o$in, X));
  free requires ($Heap[o$in, $allocated] == true);
  requires (#X.getValue$System.Int32($Heap, o$in, 4) == 5);
  requires (this != o$in);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[o$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[o$in, $ownerRef], $inv] <: $Heap[o$in, $ownerFrame])) || ($Heap[$Heap[o$in, $ownerRef], $localinv] == $BaseClass($Heap[o$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[o$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[o$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  ensures (#X.getValue$System.Int32($Heap, o$in, 4) == 5);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old((($o != this) || ($f != X.a)))) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation X.ObjectCreationWithMethodQuery$X$notnull(this : ref, o$in : ref) {
  var o : ref where $IsNotNull(o, X);
  var stack50000o : ref;
  var stack0o : ref;
  entry: assume $IsNotNull(this, X); goto $$entry~bt;
  $$entry~bt: assume ($Heap[this, $allocated] == true); goto $$entry~bs;
  $$entry~bs: o := o$in; goto block23205;
  block23205: goto block23358;
  block23358: havoc stack50000o; goto $$block23358~f;
  $$block23358~f: assume ((($Heap[stack50000o, $allocated] == false) && (stack50000o != null)) && ($typeof(stack50000o) == X)); goto $$block23358~e;
  $$block23358~e: assume (($Heap[stack50000o, $ownerRef] == stack50000o) && ($Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder)); goto $$block23358~d;
  $$block23358~d: $Heap := $Heap[stack50000o, $allocated := true]; goto $$block23358~c;
  $$block23358~c: assert (stack50000o != null); goto $$block23358~b;
  $$block23358~b: call X..ctor(stack50000o); goto $$block23358~a;
  $$block23358~a: stack0o := stack50000o; goto block23460;
  block23460: return;
  
}

procedure X..ctor(this : ref);
  free requires (forall $o : ref :: (($o != this) ==> ($Heap[$o, $ownerRef] != this)));
  free requires (($Heap[this, $ownerRef] == this) && ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder));
  free requires (forall $o : ref :: ((($Heap[$o, $ownerRef] == $Heap[this, $ownerRef]) && ($Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame])) ==> ($o == this)));
  free requires ($BeingConstructed == this);
  modifies $Heap;
  ensures ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == X)) && ($Heap[this, $localinv] == $typeof(this)));
  ensures (($Heap[this, $ownerRef] == old($Heap)[this, $ownerRef]) && ($Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame]));
  ensures ($Heap[this, $sharingMode] == $SharingMode_Unshared);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(X <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

procedure X.FieldUpdateByObjectCreationWithMethodQuery$X$notnull(this : ref, o$in : ref where $IsNotNull(o$in, X));
  free requires ($Heap[o$in, $allocated] == true);
  requires (#X.getValue$System.Int32($Heap, o$in, 4) == 5);
  requires (this != o$in);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[o$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[o$in, $ownerRef], $inv] <: $Heap[o$in, $ownerFrame])) || ($Heap[$Heap[o$in, $ownerRef], $localinv] == $BaseClass($Heap[o$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[o$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[o$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  ensures (#X.getValue$System.Int32($Heap, o$in, 4) == 5);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old((($o != this) || ($f != X.a)))) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation X.FieldUpdateByObjectCreationWithMethodQuery$X$notnull(this : ref, o$in : ref) {
  var o : ref where $IsNotNull(o, X);
  var stack50000o : ref;
  var stack0o : ref;
  var temp0 : exposeVersionType;
  entry: assume $IsNotNull(this, X); goto $$entry~bv;
  $$entry~bv: assume ($Heap[this, $allocated] == true); goto $$entry~bu;
  $$entry~bu: o := o$in; goto block24004;
  block24004: goto block24157;
  block24157: havoc stack50000o; goto $$block24157~k;
  $$block24157~k: assume ((($Heap[stack50000o, $allocated] == false) && (stack50000o != null)) && ($typeof(stack50000o) == X)); goto $$block24157~j;
  $$block24157~j: assume (($Heap[stack50000o, $ownerRef] == stack50000o) && ($Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder)); goto $$block24157~i;
  $$block24157~i: $Heap := $Heap[stack50000o, $allocated := true]; goto $$block24157~h;
  $$block24157~h: assert (stack50000o != null); goto $$block24157~g;
  $$block24157~g: call X..ctor(stack50000o); goto $$block24157~f;
  $$block24157~f: stack0o := stack50000o; goto $$block24157~e;
  $$block24157~e: assert (this != null); goto $$block24157~d;
  $$block24157~d: havoc temp0; goto $$block24157~c;
  $$block24157~c: $Heap := $Heap[this, $exposeVersion := temp0]; goto $$block24157~b;
  $$block24157~b: $Heap := $Heap[this, X.a := stack0o]; goto $$block24157~a;
  $$block24157~a: assume IsHeap($Heap); goto block24259;
  block24259: return;
  
}

procedure X.FieldUpdateByObjectCreationWithMethodQueryFails$X$notnull(this : ref, o$in : ref where $IsNotNull(o$in, X));
  free requires ($Heap[o$in, $allocated] == true);
  requires (#X.getValue$System.Int32($Heap, o$in, 4) == 5);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[o$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[o$in, $ownerRef], $inv] <: $Heap[o$in, $ownerFrame])) || ($Heap[$Heap[o$in, $ownerRef], $localinv] == $BaseClass($Heap[o$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[o$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[o$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  ensures (#X.getValue$System.Int32($Heap, o$in, 4) == 5);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old((($o != this) || ($f != X.a)))) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation X.FieldUpdateByObjectCreationWithMethodQueryFails$X$notnull(this : ref, o$in : ref) {
  var o : ref where $IsNotNull(o, X);
  var stack50000o : ref;
  var stack0o : ref;
  var temp0 : exposeVersionType;
  entry: assume $IsNotNull(this, X); goto $$entry~bx;
  $$entry~bx: assume ($Heap[this, $allocated] == true); goto $$entry~bw;
  $$entry~bw: o := o$in; goto block24769;
  block24769: goto block24871;
  block24871: havoc stack50000o; goto $$block24871~k;
  $$block24871~k: assume ((($Heap[stack50000o, $allocated] == false) && (stack50000o != null)) && ($typeof(stack50000o) == X)); goto $$block24871~j;
  $$block24871~j: assume (($Heap[stack50000o, $ownerRef] == stack50000o) && ($Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder)); goto $$block24871~i;
  $$block24871~i: $Heap := $Heap[stack50000o, $allocated := true]; goto $$block24871~h;
  $$block24871~h: assert (stack50000o != null); goto $$block24871~g;
  $$block24871~g: call X..ctor(stack50000o); goto $$block24871~f;
  $$block24871~f: stack0o := stack50000o; goto $$block24871~e;
  $$block24871~e: assert (this != null); goto $$block24871~d;
  $$block24871~d: havoc temp0; goto $$block24871~c;
  $$block24871~c: $Heap := $Heap[this, $exposeVersion := temp0]; goto $$block24871~b;
  $$block24871~b: $Heap := $Heap[this, X.a := stack0o]; goto $$block24871~a;
  $$block24871~a: assume IsHeap($Heap); goto block24973;
  block24973: return;
  
}

implementation X..ctor(this : ref) {
  entry: assume $IsNotNull(this, X); goto $$entry~cc;
  $$entry~cc: assume ($Heap[this, $allocated] == true); goto $$entry~cb;
  $$entry~cb: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto $$entry~ca;
  $$entry~ca: assume ($Heap[this, X.value] == 0); goto $$entry~bz;
  $$entry~bz: assume ($Heap[this, X.f] == 0); goto $$entry~by;
  $$entry~by: assume ($Heap[this, X.a] == null); goto block25296;
  block25296: goto block25313;
  block25313: assert (this != null); goto $$block25313~f;
  $$block25313~f: call System.Object..ctor(this); goto $$block25313~e;
  $$block25313~e: assert (this != null); goto $$block25313~d;
  $$block25313~d: assert (($Heap[this, $inv] == System.Object) && ($Heap[this, $localinv] == $typeof(this))); goto $$block25313~c;
  $$block25313~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == X)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block25313~b;
  $$block25313~b: $Heap := $Heap[this, $inv := X]; goto $$block25313~a;
  $$block25313~a: assume IsHeap($Heap); return;
  
}

