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
const Getter.value : name;
const A.x : name;
const B.a : name;
const A.y : name;
const GetterClient.g : name;
const GetterClient.value : name;
const System.ICloneable : name;
const System.Collections.IEnumerable : name;
const Getter : name;
const GetterClient : name;
const System.IComparable`1...System.String : name;
const UnsoundSpec : name;
const B : name;
const System.IEquatable`1...System.String : name;
const System.IComparable : name;
const A : name;
const System.Collections.Generic.IEnumerable`1...System.Char : name;
const System.IConvertible : name;
axiom !IsStaticField(A.x);
axiom IsDirectlyModifiableField(A.x);
axiom (DeclType(A.x) == A);
axiom (AsRangeField(A.x, System.Int32) == A.x);
axiom !IsStaticField(A.y);
axiom IsDirectlyModifiableField(A.y);
axiom (DeclType(A.y) == A);
axiom (AsRangeField(A.y, System.Int32) == A.y);
function #A.SumXYAxiomFromPost($$unnamed~fb : <x>[ref, name]x, $$unnamed~fa : ref) returns ($$unnamed~fc : int);
function #A.SumXYAxiomFromBody($$unnamed~fe : <x>[ref, name]x, $$unnamed~fd : ref) returns ($$unnamed~ff : int);
function ##A.SumXYAxiomFromBody($$unnamed~fg : exposeVersionType) returns ($$unnamed~fh : int);
function #A.SumXYNoAxiom1($$unnamed~fj : <x>[ref, name]x, $$unnamed~fi : ref) returns ($$unnamed~fk : int);
function #A.SumXYNoAxiom2($$unnamed~fm : <x>[ref, name]x, $$unnamed~fl : ref) returns ($$unnamed~fn : int);
function ##A.SumXYNoAxiom2($$unnamed~fo : exposeVersionType) returns ($$unnamed~fp : int);
axiom !IsStaticField(B.a);
axiom IsDirectlyModifiableField(B.a);
axiom (DeclType(B.a) == B);
axiom (AsRefField(B.a, A) == B.a);
function #UnsoundSpec.Unsound($$unnamed~fr : <x>[ref, name]x, $$unnamed~fq : ref) returns ($$unnamed~fs : int);
function #Getter.get_Value($$unnamed~fu : <x>[ref, name]x, $$unnamed~ft : ref) returns ($$unnamed~fv : int);
function ##Getter.get_Value($$unnamed~fw : exposeVersionType) returns ($$unnamed~fx : int);
axiom !IsStaticField(Getter.value);
axiom IsDirectlyModifiableField(Getter.value);
axiom (DeclType(Getter.value) == Getter);
axiom (AsRangeField(Getter.value, System.Int32) == Getter.value);
axiom !IsStaticField(GetterClient.g);
axiom IsDirectlyModifiableField(GetterClient.g);
axiom (DeclType(GetterClient.g) == GetterClient);
axiom (AsNonNullRefField(GetterClient.g, Getter) == GetterClient.g);
axiom !IsStaticField(GetterClient.value);
axiom IsDirectlyModifiableField(GetterClient.value);
axiom (DeclType(GetterClient.value) == GetterClient);
axiom (AsRangeField(GetterClient.value, System.Int32) == GetterClient.value);
axiom (A <: A);
axiom ($BaseClass(A) == System.Object);
axiom ((A <: $BaseClass(A)) && (AsDirectSubClass(A, $BaseClass(A)) == A));
axiom (!$IsImmutable(A) && ($AsMutable(A) == A));
axiom (forall $U : name :: {($U <: A)} (($U <: A) ==> ($U == A)));
axiom (forall $Heap : <x>[ref, name]x, this : ref :: {#A.SumXYAxiomFromPost($Heap, this)} ((IsHeap($Heap) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))) ==> (InRange(#A.SumXYAxiomFromPost($Heap, this), System.Int32) && (#A.SumXYAxiomFromPost($Heap, this) == ($Heap[this, A.x] + $Heap[this, A.y])))));
procedure A.SumXYAxiomFromPost(this : ref) returns ($result : int where InRange($result, System.Int32));
  requires (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))));
  free requires ($AsPureObject(this) == this);
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures true;
  free ensures InRange($result, System.Int32);
  ensures ($result == ($Heap[this, A.x] + $Heap[this, A.y]));
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures ($Heap == old($Heap));
  free ensures ($result == #A.SumXYAxiomFromPost($Heap, this));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} ((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation A.SumXYAxiomFromPost(this : ref) returns ($result : int) {
  var stack0i : int;
  var stack1i : int;
  var temp : int where InRange(temp, System.Int32);
  var return.value : int where InRange(return.value, System.Int32);
  var SS$Display.Return.Local : int where InRange(SS$Display.Return.Local, System.Int32);
  entry: assume $IsNotNull(this, A); goto $$entry~a;
  $$entry~a: assume ($Heap[this, $allocated] == true); goto block1479;
  block1479: goto block1496;
  block1496: assert (this != null); goto $$block1496~f;
  $$block1496~f: stack0i := $Heap[this, A.x]; goto $$block1496~e;
  $$block1496~e: assert (this != null); goto $$block1496~d;
  $$block1496~d: stack1i := $Heap[this, A.y]; goto $$block1496~c;
  $$block1496~c: stack0i := (stack0i + stack1i); goto $$block1496~b;
  $$block1496~b: temp := stack0i; goto $$block1496~a;
  $$block1496~a: return.value := temp; goto block1598;
  block1598: SS$Display.Return.Local := return.value; goto $$block1598~b;
  $$block1598~b: stack0i := return.value; goto $$block1598~a;
  $$block1598~a: $result := stack0i; return;
  
}

axiom (forall $Heap : <x>[ref, name]x, this : ref :: {#A.SumXYAxiomFromBody($Heap, this)} ((IsHeap($Heap) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))) ==> (InRange(#A.SumXYAxiomFromBody($Heap, this), System.Int32) && (#A.SumXYAxiomFromBody($Heap, this) == ($Heap[this, A.x] + $Heap[this, A.y])))));
axiom (forall $Heap : <x>[ref, name]x, this : ref :: {#A.SumXYAxiomFromBody($Heap, this)} (((((((this != null) && ($typeof(this) <: A)) && ($Heap[this, $inv] == $typeof(this))) && ($Heap[this, $localinv] == $typeof(this))) && IsHeap($Heap)) && ($Heap[this, $allocated] == true)) ==> (#A.SumXYAxiomFromBody($Heap, this) == ##A.SumXYAxiomFromBody($Heap[this, $exposeVersion]))));
procedure A.SumXYAxiomFromBody(this : ref) returns ($result : int where InRange($result, System.Int32));
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
  free ensures ($result == #A.SumXYAxiomFromBody($Heap, this));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} ((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation A.SumXYAxiomFromBody(this : ref) returns ($result : int) {
  var stack0i : int;
  var stack1i : int;
  var return.value : int where InRange(return.value, System.Int32);
  var SS$Display.Return.Local : int where InRange(SS$Display.Return.Local, System.Int32);
  entry: assume $IsNotNull(this, A); goto $$entry~b;
  $$entry~b: assume ($Heap[this, $allocated] == true); goto block1955;
  block1955: goto block1972;
  block1972: assert (this != null); goto $$block1972~e;
  $$block1972~e: stack0i := $Heap[this, A.x]; goto $$block1972~d;
  $$block1972~d: assert (this != null); goto $$block1972~c;
  $$block1972~c: stack1i := $Heap[this, A.y]; goto $$block1972~b;
  $$block1972~b: stack0i := (stack0i + stack1i); goto $$block1972~a;
  $$block1972~a: return.value := stack0i; goto block1989;
  block1989: SS$Display.Return.Local := return.value; goto $$block1989~b;
  $$block1989~b: stack0i := return.value; goto $$block1989~a;
  $$block1989~a: $result := stack0i; return;
  
}

axiom (forall $Heap : <x>[ref, name]x, this : ref :: {#A.SumXYNoAxiom1($Heap, this)} ((IsHeap($Heap) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))) ==> InRange(#A.SumXYNoAxiom1($Heap, this), System.Int32)));
procedure A.SumXYNoAxiom1(this : ref) returns ($result : int where InRange($result, System.Int32));
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
  free ensures ($result == #A.SumXYNoAxiom1($Heap, this));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} ((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation A.SumXYNoAxiom1(this : ref) returns ($result : int) {
  var stack0i : int;
  var stack1i : int;
  var temp : int where InRange(temp, System.Int32);
  var return.value : int where InRange(return.value, System.Int32);
  var SS$Display.Return.Local : int where InRange(SS$Display.Return.Local, System.Int32);
  entry: assume $IsNotNull(this, A); goto $$entry~c;
  $$entry~c: assume ($Heap[this, $allocated] == true); goto block2278;
  block2278: goto block2295;
  block2295: assert (this != null); goto $$block2295~f;
  $$block2295~f: stack0i := $Heap[this, A.x]; goto $$block2295~e;
  $$block2295~e: assert (this != null); goto $$block2295~d;
  $$block2295~d: stack1i := $Heap[this, A.y]; goto $$block2295~c;
  $$block2295~c: stack0i := (stack0i + stack1i); goto $$block2295~b;
  $$block2295~b: temp := stack0i; goto $$block2295~a;
  $$block2295~a: return.value := temp; goto block2312;
  block2312: SS$Display.Return.Local := return.value; goto $$block2312~b;
  $$block2312~b: stack0i := return.value; goto $$block2312~a;
  $$block2312~a: $result := stack0i; return;
  
}

axiom (forall $Heap : <x>[ref, name]x, this : ref :: {#A.SumXYNoAxiom2($Heap, this)} ((((IsHeap($Heap) && ($Heap[this, A.x] > 0)) && ($Heap[this, A.y] > 0)) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))) ==> InRange(#A.SumXYNoAxiom2($Heap, this), System.Int32)));
axiom (forall $Heap : <x>[ref, name]x, this : ref :: {#A.SumXYNoAxiom2($Heap, this)} (((((((this != null) && ($typeof(this) <: A)) && ($Heap[this, $inv] == $typeof(this))) && ($Heap[this, $localinv] == $typeof(this))) && IsHeap($Heap)) && ($Heap[this, $allocated] == true)) ==> (#A.SumXYNoAxiom2($Heap, this) == ##A.SumXYNoAxiom2($Heap[this, $exposeVersion]))));
procedure A.SumXYNoAxiom2(this : ref) returns ($result : int where InRange($result, System.Int32));
  requires (($Heap[this, A.x] > 0) && ($Heap[this, A.y] > 0));
  requires (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))));
  free requires ($AsPureObject(this) == this);
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures true;
  free ensures InRange($result, System.Int32);
  ensures ($result > 0);
  ensures ($result == ($Heap[this, A.x] + $Heap[this, A.y]));
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures ($Heap == old($Heap));
  free ensures ($result == #A.SumXYNoAxiom2($Heap, this));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} ((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation A.SumXYNoAxiom2(this : ref) returns ($result : int) {
  var stack0i : int;
  var stack1i : int;
  var return.value : int where InRange(return.value, System.Int32);
  var SS$Display.Return.Local : int where InRange(SS$Display.Return.Local, System.Int32);
  entry: assume $IsNotNull(this, A); goto $$entry~d;
  $$entry~d: assume ($Heap[this, $allocated] == true); goto block2856;
  block2856: goto block2975;
  block2975: assert (this != null); goto $$block2975~e;
  $$block2975~e: stack0i := $Heap[this, A.x]; goto $$block2975~d;
  $$block2975~d: assert (this != null); goto $$block2975~c;
  $$block2975~c: stack1i := $Heap[this, A.y]; goto $$block2975~b;
  $$block2975~b: stack0i := (stack0i + stack1i); goto $$block2975~a;
  $$block2975~a: return.value := stack0i; goto block3128;
  block3128: SS$Display.Return.Local := return.value; goto $$block3128~b;
  $$block3128~b: stack0i := return.value; goto $$block3128~a;
  $$block3128~a: $result := stack0i; return;
  
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
  entry: assume $IsNotNull(this, A); goto $$entry~h;
  $$entry~h: assume ($Heap[this, $allocated] == true); goto $$entry~g;
  $$entry~g: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto $$entry~f;
  $$entry~f: assume ($Heap[this, A.x] == 0); goto $$entry~e;
  $$entry~e: assume ($Heap[this, A.y] == 0); goto block3502;
  block3502: goto block3519;
  block3519: assert (this != null); goto $$block3519~f;
  $$block3519~f: call System.Object..ctor(this); goto $$block3519~e;
  $$block3519~e: assert (this != null); goto $$block3519~d;
  $$block3519~d: assert (($Heap[this, $inv] == System.Object) && ($Heap[this, $localinv] == $typeof(this))); goto $$block3519~c;
  $$block3519~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == A)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block3519~b;
  $$block3519~b: $Heap := $Heap[this, $inv := A]; goto $$block3519~a;
  $$block3519~a: assume IsHeap($Heap); return;
  
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
  

axiom (B <: B);
axiom ($BaseClass(B) == System.Object);
axiom ((B <: $BaseClass(B)) && (AsDirectSubClass(B, $BaseClass(B)) == B));
axiom (!$IsImmutable(B) && ($AsMutable(B) == B));
axiom (forall $U : name :: {($U <: B)} (($U <: B) ==> ($U == B)));
procedure B.Dummy1(this : ref);
  requires ((($Heap[this, B.a] != null) && ((($Heap[$Heap[this, B.a], $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[$Heap[this, B.a], $ownerRef], $inv] <: $Heap[$Heap[this, B.a], $ownerFrame])) || ($Heap[$Heap[$Heap[this, B.a], $ownerRef], $localinv] == $BaseClass($Heap[$Heap[this, B.a], $ownerFrame])))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[$Heap[this, B.a], $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[$Heap[this, B.a], $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  ensures (($Heap[$Heap[this, B.a], A.x] + $Heap[$Heap[this, B.a], A.y]) == #A.SumXYAxiomFromPost($Heap, $Heap[this, B.a]));
  ensures (($Heap[$Heap[this, B.a], A.x] + $Heap[$Heap[this, B.a], A.y]) == #A.SumXYAxiomFromBody($Heap, $Heap[this, B.a]));
  ensures (($Heap[$Heap[this, B.a], A.x] + $Heap[$Heap[this, B.a], A.y]) == #A.SumXYNoAxiom1($Heap, $Heap[this, B.a]));
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation B.Dummy1(this : ref) {
  entry: assume $IsNotNull(this, B); goto $$entry~i;
  $$entry~i: assume ($Heap[this, $allocated] == true); goto block4284;
  block4284: goto block4403;
  block4403: goto block4607;
  block4607: return;
  
}

procedure B.Dummy2(this : ref);
  requires ((($Heap[this, B.a] != null) && ((($Heap[$Heap[this, B.a], $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[$Heap[this, B.a], $ownerRef], $inv] <: $Heap[$Heap[this, B.a], $ownerFrame])) || ($Heap[$Heap[$Heap[this, B.a], $ownerRef], $localinv] == $BaseClass($Heap[$Heap[this, B.a], $ownerFrame])))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[$Heap[this, B.a], $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[$Heap[this, B.a], $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  ensures (($Heap[$Heap[this, B.a], A.x] + $Heap[$Heap[this, B.a], A.y]) == #A.SumXYNoAxiom2($Heap, $Heap[this, B.a]));
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation B.Dummy2(this : ref) {
  entry: assume $IsNotNull(this, B); goto $$entry~j;
  $$entry~j: assume ($Heap[this, $allocated] == true); goto block5066;
  block5066: goto block5185;
  block5185: goto block5287;
  block5287: return;
  
}

procedure B..ctor(this : ref);
  free requires (forall $o : ref :: (($o != this) ==> ($Heap[$o, $ownerRef] != this)));
  free requires (($Heap[this, $ownerRef] == this) && ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder));
  free requires (forall $o : ref :: ((($Heap[$o, $ownerRef] == $Heap[this, $ownerRef]) && ($Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame])) ==> ($o == this)));
  free requires ($BeingConstructed == this);
  modifies $Heap;
  ensures ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == B)) && ($Heap[this, $localinv] == $typeof(this)));
  ensures (($Heap[this, $ownerRef] == old($Heap)[this, $ownerRef]) && ($Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame]));
  ensures ($Heap[this, $sharingMode] == $SharingMode_Unshared);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(B <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

implementation B..ctor(this : ref) {
  var stack50000o : ref;
  var stack0o : ref;
  var temp0 : exposeVersionType;
  entry: assume $IsNotNull(this, B); goto $$entry~m;
  $$entry~m: assume ($Heap[this, $allocated] == true); goto $$entry~l;
  $$entry~l: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto $$entry~k;
  $$entry~k: assume ($Heap[this, B.a] == null); goto block5542;
  block5542: goto block5559;
  block5559: havoc stack50000o; goto $$block5559~r;
  $$block5559~r: assume ((($Heap[stack50000o, $allocated] == false) && (stack50000o != null)) && ($typeof(stack50000o) == A)); goto $$block5559~q;
  $$block5559~q: assume (($Heap[stack50000o, $ownerRef] == stack50000o) && ($Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder)); goto $$block5559~p;
  $$block5559~p: $Heap := $Heap[stack50000o, $allocated := true]; goto $$block5559~o;
  $$block5559~o: assert (stack50000o != null); goto $$block5559~n;
  $$block5559~n: call A..ctor(stack50000o); goto $$block5559~m;
  $$block5559~m: stack0o := stack50000o; goto $$block5559~l;
  $$block5559~l: assert (this != null); goto $$block5559~k;
  $$block5559~k: havoc temp0; goto $$block5559~j;
  $$block5559~j: $Heap := $Heap[this, $exposeVersion := temp0]; goto $$block5559~i;
  $$block5559~i: $Heap := $Heap[this, B.a := stack0o]; goto $$block5559~h;
  $$block5559~h: assume IsHeap($Heap); goto $$block5559~g;
  $$block5559~g: assert (this != null); goto $$block5559~f;
  $$block5559~f: call System.Object..ctor(this); goto $$block5559~e;
  $$block5559~e: assert (this != null); goto $$block5559~d;
  $$block5559~d: assert (($Heap[this, $inv] == System.Object) && ($Heap[this, $localinv] == $typeof(this))); goto $$block5559~c;
  $$block5559~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == B)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block5559~b;
  $$block5559~b: $Heap := $Heap[this, $inv := B]; goto $$block5559~a;
  $$block5559~a: assume IsHeap($Heap); return;
  
}

axiom (UnsoundSpec <: UnsoundSpec);
axiom ($BaseClass(UnsoundSpec) == System.Object);
axiom ((UnsoundSpec <: $BaseClass(UnsoundSpec)) && (AsDirectSubClass(UnsoundSpec, $BaseClass(UnsoundSpec)) == UnsoundSpec));
axiom (!$IsImmutable(UnsoundSpec) && ($AsMutable(UnsoundSpec) == UnsoundSpec));
axiom (forall $U : name :: {($U <: UnsoundSpec)} (($U <: UnsoundSpec) ==> ($U == UnsoundSpec)));
axiom (forall $Heap : <x>[ref, name]x, this : ref :: {#UnsoundSpec.Unsound($Heap, this)} ((IsHeap($Heap) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))) ==> InRange(#UnsoundSpec.Unsound($Heap, this), System.Int32)));
procedure UnsoundSpec.Unsound(this : ref) returns ($result : int where InRange($result, System.Int32));
  requires (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))));
  free requires ($AsPureObject(this) == this);
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures true;
  free ensures InRange($result, System.Int32);
  ensures false;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures ($Heap == old($Heap));
  free ensures ($result == #UnsoundSpec.Unsound($Heap, this));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} ((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation UnsoundSpec.Unsound(this : ref) returns ($result : int) {
  var $Heap$block5933$LoopPreheader : <x>[ref, name]x;
  entry: assume $IsNotNull(this, UnsoundSpec); goto $$entry~n;
  $$entry~n: assume ($Heap[this, $allocated] == true); goto block5916;
  block5916: goto block5933$LoopPreheader;
  block5933: assume (((forall $o : ref :: (($Heap$block5933$LoopPreheader[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: ((($Heap$block5933$LoopPreheader[$ot, $allocated] == true) && ($Heap$block5933$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == $Heap$block5933$LoopPreheader[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == $Heap$block5933$LoopPreheader[$ot, $ownerFrame]))))) && ($Heap$block5933$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized])); goto $$block5933~c;
  $$block5933~c: assume (forall $o : ref :: ((($Heap$block5933$LoopPreheader[$o, $inv] == $Heap[$o, $inv]) && ($Heap$block5933$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv])) || ($Heap$block5933$LoopPreheader[$o, $allocated] != true))); goto $$block5933~b;
  $$block5933~b: assume (forall $o : ref :: ((($Heap$block5933$LoopPreheader[$o, $allocated] != true) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o))))); goto $$block5933~a;
  $$block5933~a: assert (forall $o : ref :: ((($o != null) && ($Heap$block5933$LoopPreheader[$o, $allocated] == true)) ==> (($Heap$block5933$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef]) && ($Heap$block5933$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame])))); goto block5950;
  block5950: goto block5933;
  block5933$LoopPreheader: $Heap$block5933$LoopPreheader := $Heap; goto block5933;
  
}

procedure UnsoundSpec.Dummy1(this : ref);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  ensures (#UnsoundSpec.Unsound($Heap, this) == (#UnsoundSpec.Unsound($Heap, this) + 1));
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation UnsoundSpec.Dummy1(this : ref) {
  entry: assume $IsNotNull(this, UnsoundSpec); goto $$entry~o;
  $$entry~o: assume ($Heap[this, $allocated] == true); goto block6307;
  block6307: goto block6409;
  block6409: return;
  
}

procedure UnsoundSpec..ctor(this : ref);
  free requires (forall $o : ref :: (($o != this) ==> ($Heap[$o, $ownerRef] != this)));
  free requires (($Heap[this, $ownerRef] == this) && ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder));
  free requires (forall $o : ref :: ((($Heap[$o, $ownerRef] == $Heap[this, $ownerRef]) && ($Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame])) ==> ($o == this)));
  free requires ($BeingConstructed == this);
  modifies $Heap;
  ensures ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == UnsoundSpec)) && ($Heap[this, $localinv] == $typeof(this)));
  ensures (($Heap[this, $ownerRef] == old($Heap)[this, $ownerRef]) && ($Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame]));
  ensures ($Heap[this, $sharingMode] == $SharingMode_Unshared);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(UnsoundSpec <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

implementation UnsoundSpec..ctor(this : ref) {
  entry: assume $IsNotNull(this, UnsoundSpec); goto $$entry~q;
  $$entry~q: assume ($Heap[this, $allocated] == true); goto $$entry~p;
  $$entry~p: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto block6613;
  block6613: goto block6630;
  block6630: assert (this != null); goto $$block6630~f;
  $$block6630~f: call System.Object..ctor(this); goto $$block6630~e;
  $$block6630~e: assert (this != null); goto $$block6630~d;
  $$block6630~d: assert (($Heap[this, $inv] == System.Object) && ($Heap[this, $localinv] == $typeof(this))); goto $$block6630~c;
  $$block6630~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == UnsoundSpec)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block6630~b;
  $$block6630~b: $Heap := $Heap[this, $inv := UnsoundSpec]; goto $$block6630~a;
  $$block6630~a: assume IsHeap($Heap); return;
  
}

axiom (Getter <: Getter);
axiom ($BaseClass(Getter) == System.Object);
axiom ((Getter <: $BaseClass(Getter)) && (AsDirectSubClass(Getter, $BaseClass(Getter)) == Getter));
axiom (!$IsImmutable(Getter) && ($AsMutable(Getter) == Getter));
axiom (forall $U : name :: {($U <: Getter)} (($U <: Getter) ==> ($U == Getter)));
axiom (forall $Heap : <x>[ref, name]x, this : ref :: {#Getter.get_Value($Heap, this)} ((IsHeap($Heap) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))) ==> (InRange(#Getter.get_Value($Heap, this), System.Int32) && (#Getter.get_Value($Heap, this) == $Heap[this, Getter.value]))));
axiom (forall $Heap : <x>[ref, name]x, this : ref :: {#Getter.get_Value($Heap, this)} (((((((this != null) && ($typeof(this) <: Getter)) && ($Heap[this, $inv] == $typeof(this))) && ($Heap[this, $localinv] == $typeof(this))) && IsHeap($Heap)) && ($Heap[this, $allocated] == true)) ==> (#Getter.get_Value($Heap, this) == ##Getter.get_Value($Heap[this, $exposeVersion]))));
procedure Getter.get_Value(this : ref) returns ($result : int where InRange($result, System.Int32));
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
  free ensures ($result == #Getter.get_Value($Heap, this));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} ((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Getter.get_Value(this : ref) returns ($result : int) {
  var return.value : int where InRange(return.value, System.Int32);
  var SS$Display.Return.Local : int where InRange(SS$Display.Return.Local, System.Int32);
  var stack0i : int;
  entry: assume $IsNotNull(this, Getter); goto $$entry~r;
  $$entry~r: assume ($Heap[this, $allocated] == true); goto block6817;
  block6817: goto block6834;
  block6834: assert (this != null); goto $$block6834~a;
  $$block6834~a: return.value := $Heap[this, Getter.value]; goto block6851;
  block6851: SS$Display.Return.Local := return.value; goto $$block6851~b;
  $$block6851~b: stack0i := return.value; goto $$block6851~a;
  $$block6851~a: $result := stack0i; return;
  
}

procedure Getter.set_Value$System.Int32(this : ref, value$in : int where InRange(value$in, System.Int32));
  free requires true;
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  ensures ($Heap[this, Getter.value] == value$in);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old((($o != this) || ($f != Getter.value)))) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Getter.set_Value$System.Int32(this : ref, value$in : int) {
  var value : int where InRange(value, System.Int32);
  var temp0 : exposeVersionType;
  entry: assume $IsNotNull(this, Getter); goto $$entry~t;
  $$entry~t: assume ($Heap[this, $allocated] == true); goto $$entry~s;
  $$entry~s: value := value$in; goto block7259;
  block7259: goto block7361;
  block7361: assert (this != null); goto $$block7361~d;
  $$block7361~d: havoc temp0; goto $$block7361~c;
  $$block7361~c: $Heap := $Heap[this, $exposeVersion := temp0]; goto $$block7361~b;
  $$block7361~b: $Heap := $Heap[this, Getter.value := value]; goto $$block7361~a;
  $$block7361~a: assume IsHeap($Heap); goto block7463;
  block7463: return;
  
}

procedure Getter..ctor(this : ref);
  free requires (forall $o : ref :: (($o != this) ==> ($Heap[$o, $ownerRef] != this)));
  free requires (($Heap[this, $ownerRef] == this) && ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder));
  free requires (forall $o : ref :: ((($Heap[$o, $ownerRef] == $Heap[this, $ownerRef]) && ($Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame])) ==> ($o == this)));
  free requires ($BeingConstructed == this);
  modifies $Heap;
  ensures ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == Getter)) && ($Heap[this, $localinv] == $typeof(this)));
  ensures (($Heap[this, $ownerRef] == old($Heap)[this, $ownerRef]) && ($Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame]));
  ensures ($Heap[this, $sharingMode] == $SharingMode_Unshared);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(Getter <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

implementation Getter..ctor(this : ref) {
  entry: assume $IsNotNull(this, Getter); goto $$entry~w;
  $$entry~w: assume ($Heap[this, $allocated] == true); goto $$entry~v;
  $$entry~v: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto $$entry~u;
  $$entry~u: assume ($Heap[this, Getter.value] == 0); goto block7735;
  block7735: goto block7752;
  block7752: assert (this != null); goto $$block7752~f;
  $$block7752~f: call System.Object..ctor(this); goto $$block7752~e;
  $$block7752~e: assert (this != null); goto $$block7752~d;
  $$block7752~d: assert (($Heap[this, $inv] == System.Object) && ($Heap[this, $localinv] == $typeof(this))); goto $$block7752~c;
  $$block7752~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == Getter)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block7752~b;
  $$block7752~b: $Heap := $Heap[this, $inv := Getter]; goto $$block7752~a;
  $$block7752~a: assume IsHeap($Heap); return;
  
}

axiom (GetterClient <: GetterClient);
axiom ($BaseClass(GetterClient) == System.Object);
axiom ((GetterClient <: $BaseClass(GetterClient)) && (AsDirectSubClass(GetterClient, $BaseClass(GetterClient)) == GetterClient));
axiom (!$IsImmutable(GetterClient) && ($AsMutable(GetterClient) == GetterClient));
axiom (forall $U : name :: {($U <: GetterClient)} (($U <: GetterClient) ==> ($U == GetterClient)));
procedure GetterClient.Dummy(this : ref);
  requires (((($Heap[$Heap[this, GetterClient.g], $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[$Heap[this, GetterClient.g], $ownerRef], $inv] <: $Heap[$Heap[this, GetterClient.g], $ownerFrame])) || ($Heap[$Heap[$Heap[this, GetterClient.g], $ownerRef], $localinv] == $BaseClass($Heap[$Heap[this, GetterClient.g], $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[$Heap[this, GetterClient.g], $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[$Heap[this, GetterClient.g], $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old((($o != $Heap[this, GetterClient.g]) || ($f != Getter.value)))) && old(((($o != $Heap[this, GetterClient.g]) || ($f != $exposeVersion)) && (($o != this) || ($f != $exposeVersion))))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation GetterClient.Dummy(this : ref) {
  var stack0o : ref;
  var stack1i : int;
  var temp0 : exposeVersionType;
  entry: assume $IsNotNull(this, GetterClient); goto $$entry~x;
  $$entry~x: assume ($Heap[this, $allocated] == true); goto block8177;
  block8177: goto block8279;
  block8279: assert (this != null); goto $$block8279~e;
  $$block8279~e: stack0o := $Heap[this, GetterClient.g]; goto $$block8279~d;
  $$block8279~d: stack1i := 5; goto $$block8279~c;
  $$block8279~c: assert (stack0o != null); goto $$block8279~b;
  $$block8279~b: call Getter.set_Value$System.Int32(stack0o, stack1i); goto $$block8279~a;
  $$block8279~a: assert (#Getter.get_Value($Heap, $Heap[this, GetterClient.g]) == 5); goto block8364;
  block8364: assert (this != null); goto $$block8364~h;
  $$block8364~h: stack0o := $Heap[this, GetterClient.g]; goto $$block8364~g;
  $$block8364~g: stack1i := 6; goto $$block8364~f;
  $$block8364~f: assert (stack0o != null); goto $$block8364~e;
  $$block8364~e: havoc temp0; goto $$block8364~d;
  $$block8364~d: $Heap := $Heap[stack0o, $exposeVersion := temp0]; goto $$block8364~c;
  $$block8364~c: $Heap := $Heap[stack0o, Getter.value := stack1i]; goto $$block8364~b;
  $$block8364~b: assume IsHeap($Heap); goto $$block8364~a;
  $$block8364~a: assert (#Getter.get_Value($Heap, $Heap[this, GetterClient.g]) == 6); goto block8449;
  block8449: return;
  
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
procedure GetterClient..ctor(this : ref);
  free requires (forall $o : ref :: (($o != this) ==> ($Heap[$o, $ownerRef] != this)));
  free requires (($Heap[this, $ownerRef] == this) && ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder));
  free requires (forall $o : ref :: ((($Heap[$o, $ownerRef] == $Heap[this, $ownerRef]) && ($Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame])) ==> ($o == this)));
  free requires ($BeingConstructed == this);
  modifies $Heap;
  ensures ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == GetterClient)) && ($Heap[this, $localinv] == $typeof(this)));
  ensures (($Heap[this, $ownerRef] == old($Heap)[this, $ownerRef]) && ($Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame]));
  ensures ($Heap[this, $sharingMode] == $SharingMode_Unshared);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(GetterClient <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

implementation GetterClient..ctor(this : ref) {
  var stack50000o : ref;
  var stack0o : ref;
  var temp0 : exposeVersionType;
  entry: assume $IsNotNull(this, GetterClient); goto $$entry~aa;
  $$entry~aa: assume ($Heap[this, $allocated] == true); goto $$entry~z;
  $$entry~z: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto $$entry~y;
  $$entry~y: assume ($Heap[this, GetterClient.value] == 0); goto block8925;
  block8925: goto block8942;
  block8942: havoc stack50000o; goto $$block8942~r;
  $$block8942~r: assume ((($Heap[stack50000o, $allocated] == false) && (stack50000o != null)) && ($typeof(stack50000o) == Getter)); goto $$block8942~q;
  $$block8942~q: assume (($Heap[stack50000o, $ownerRef] == stack50000o) && ($Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder)); goto $$block8942~p;
  $$block8942~p: $Heap := $Heap[stack50000o, $allocated := true]; goto $$block8942~o;
  $$block8942~o: assert (stack50000o != null); goto $$block8942~n;
  $$block8942~n: call Getter..ctor(stack50000o); goto $$block8942~m;
  $$block8942~m: stack0o := stack50000o; goto $$block8942~l;
  $$block8942~l: assert (this != null); goto $$block8942~k;
  $$block8942~k: havoc temp0; goto $$block8942~j;
  $$block8942~j: $Heap := $Heap[this, $exposeVersion := temp0]; goto $$block8942~i;
  $$block8942~i: $Heap := $Heap[this, GetterClient.g := stack0o]; goto $$block8942~h;
  $$block8942~h: assume IsHeap($Heap); goto $$block8942~g;
  $$block8942~g: assert (this != null); goto $$block8942~f;
  $$block8942~f: call System.Object..ctor(this); goto $$block8942~e;
  $$block8942~e: assert (this != null); goto $$block8942~d;
  $$block8942~d: assert (($Heap[this, $inv] == System.Object) && ($Heap[this, $localinv] == $typeof(this))); goto $$block8942~c;
  $$block8942~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == GetterClient)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block8942~b;
  $$block8942~b: $Heap := $Heap[this, $inv := GetterClient]; goto $$block8942~a;
  $$block8942~a: assume IsHeap($Heap); return;
  
}

