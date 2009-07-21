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
const C0.t : name;
const C1.impX : name;
const C0.s : name;
const C2.impX : name;
const System.IComparable : name;
const System.Boolean : name;
const C2 : name;
const System.Collections.IEnumerable : name;
const AlsoImpossible : name;
const System.Collections.Generic.IEnumerable`1...System.Char : name;
const System.ICloneable : name;
const AlsoImpossibleSub : name;
const System.IComparable`1...System.String : name;
const ImpossibleSub : name;
const System.IEquatable`1...System.String : name;
const System.IConvertible : name;
const Impossible : name;
const C0 : name;
const C1 : name;
const D : name;
axiom !IsStaticField(C0.s);
axiom IsDirectlyModifiableField(C0.s);
axiom (DeclType(C0.s) == C0);
axiom (AsNonNullRefField(C0.s, System.String) == C0.s);
axiom !IsStaticField(C0.t);
axiom IsDirectlyModifiableField(C0.t);
axiom (DeclType(C0.t) == C0);
axiom (AsRefField(C0.t, System.String) == C0.t);
axiom !IsStaticField(C1.impX);
axiom IsDirectlyModifiableField(C1.impX);
axiom (DeclType(C1.impX) == C1);
axiom (AsRefField(C1.impX, Impossible) == C1.impX);
function #C1.impY($$unnamed~fa : ref) returns ($$unnamed~fb : ref);
axiom (forall $r : ref :: $Is(#C1.impY($r), Impossible));
function #C1.P($$unnamed~fd : <x>[ref, name]x, $$unnamed~fc : ref) returns ($$unnamed~fe : ref);
function ##C1.P($$unnamed~ff : exposeVersionType) returns ($$unnamed~fg : ref);
axiom !IsStaticField(C2.impX);
axiom IsDirectlyModifiableField(C2.impX);
axiom (DeclType(C2.impX) == C2);
function #C2.impY($$unnamed~fh : ref) returns ($$unnamed~fi : ref);
function #C2.P($$unnamed~fk : <x>[ref, name]x, $$unnamed~fj : ref) returns ($$unnamed~fl : ref);
function ##C2.P($$unnamed~fm : exposeVersionType) returns ($$unnamed~fn : ref);
axiom (Impossible <: Impossible);
axiom ($BaseClass(Impossible) == System.Object);
axiom ((Impossible <: $BaseClass(Impossible)) && (AsDirectSubClass(Impossible, $BaseClass(Impossible)) == Impossible));
axiom (!$IsImmutable(Impossible) && ($AsMutable(Impossible) == Impossible));
axiom $IsMemberlessType(Impossible);
axiom (ImpossibleSub <: ImpossibleSub);
axiom ($BaseClass(ImpossibleSub) == Impossible);
axiom ((ImpossibleSub <: $BaseClass(ImpossibleSub)) && (AsDirectSubClass(ImpossibleSub, $BaseClass(ImpossibleSub)) == ImpossibleSub));
axiom (!$IsImmutable(ImpossibleSub) && ($AsMutable(ImpossibleSub) == ImpossibleSub));
axiom $IsMemberlessType(ImpossibleSub);
axiom (forall $U : name :: {($U <: ImpossibleSub)} (($U <: ImpossibleSub) ==> ($U == ImpossibleSub)));
axiom (forall $U : name :: {($U <: Impossible)} (($U <: Impossible) ==> (($U == Impossible) || ($U <: ImpossibleSub))));
procedure Impossible..ctor(this : ref);
  free requires (forall $o : ref :: (($o != this) ==> ($Heap[$o, $ownerRef] != this)));
  free requires (($Heap[this, $ownerRef] == this) && ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder));
  free requires (forall $o : ref :: ((($Heap[$o, $ownerRef] == $Heap[this, $ownerRef]) && ($Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame])) ==> ($o == this)));
  free requires ($BeingConstructed == this);
  modifies $Heap;
  ensures ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == Impossible)) && ($Heap[this, $localinv] == $typeof(this)));
  ensures (($Heap[this, $ownerRef] == old($Heap)[this, $ownerRef]) && ($Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame]));
  ensures ($Heap[this, $sharingMode] == $SharingMode_Unshared);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(Impossible <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

implementation Impossible..ctor(this : ref) {
  entry: assume $IsNotNull(this, Impossible); goto $$entry~b;
  $$entry~b: assume ($Heap[this, $allocated] == true); goto $$entry~a;
  $$entry~a: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto block1819;
  block1819: goto block1836;
  block1836: assert (this != null); goto $$block1836~f;
  $$block1836~f: call System.Object..ctor(this); goto $$block1836~e;
  $$block1836~e: assert (this != null); goto $$block1836~d;
  $$block1836~d: assert (($Heap[this, $inv] == System.Object) && ($Heap[this, $localinv] == $typeof(this))); goto $$block1836~c;
  $$block1836~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == Impossible)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block1836~b;
  $$block1836~b: $Heap := $Heap[this, $inv := Impossible]; goto $$block1836~a;
  $$block1836~a: assume IsHeap($Heap); return;
  
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
  

procedure ImpossibleSub..ctor(this : ref);
  free requires (forall $o : ref :: (($o != this) ==> ($Heap[$o, $ownerRef] != this)));
  free requires (($Heap[this, $ownerRef] == this) && ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder));
  free requires (forall $o : ref :: ((($Heap[$o, $ownerRef] == $Heap[this, $ownerRef]) && ($Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame])) ==> ($o == this)));
  free requires ($BeingConstructed == this);
  modifies $Heap;
  ensures ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == ImpossibleSub)) && ($Heap[this, $localinv] == $typeof(this)));
  ensures (($Heap[this, $ownerRef] == old($Heap)[this, $ownerRef]) && ($Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame]));
  ensures ($Heap[this, $sharingMode] == $SharingMode_Unshared);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(ImpossibleSub <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

implementation ImpossibleSub..ctor(this : ref) {
  entry: assume $IsNotNull(this, ImpossibleSub); goto $$entry~d;
  $$entry~d: assume ($Heap[this, $allocated] == true); goto $$entry~c;
  $$entry~c: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto block2006;
  block2006: goto block2023;
  block2023: assert (this != null); goto $$block2023~f;
  $$block2023~f: call Impossible..ctor(this); goto $$block2023~e;
  $$block2023~e: assert (this != null); goto $$block2023~d;
  $$block2023~d: assert (($Heap[this, $inv] == Impossible) && ($Heap[this, $localinv] == $typeof(this))); goto $$block2023~c;
  $$block2023~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == ImpossibleSub)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block2023~b;
  $$block2023~b: $Heap := $Heap[this, $inv := ImpossibleSub]; goto $$block2023~a;
  $$block2023~a: assume IsHeap($Heap); return;
  
}

axiom (AlsoImpossible <: AlsoImpossible);
axiom ($BaseClass(AlsoImpossible) == System.Object);
axiom ((AlsoImpossible <: $BaseClass(AlsoImpossible)) && (AsDirectSubClass(AlsoImpossible, $BaseClass(AlsoImpossible)) == AlsoImpossible));
axiom (!$IsImmutable(AlsoImpossible) && ($AsMutable(AlsoImpossible) == AlsoImpossible));
axiom $IsMemberlessType(AlsoImpossible);
axiom (forall $U : name :: {($U <: AlsoImpossible)} (($U <: AlsoImpossible) ==> ($U == AlsoImpossible)));
procedure AlsoImpossible..ctor(this : ref);
  free requires (forall $o : ref :: (($o != this) ==> ($Heap[$o, $ownerRef] != this)));
  free requires (($Heap[this, $ownerRef] == this) && ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder));
  free requires (forall $o : ref :: ((($Heap[$o, $ownerRef] == $Heap[this, $ownerRef]) && ($Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame])) ==> ($o == this)));
  free requires ($BeingConstructed == this);
  modifies $Heap;
  ensures ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == AlsoImpossible)) && ($Heap[this, $localinv] == $typeof(this)));
  ensures (($Heap[this, $ownerRef] == old($Heap)[this, $ownerRef]) && ($Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame]));
  ensures ($Heap[this, $sharingMode] == $SharingMode_Unshared);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(AlsoImpossible <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

implementation AlsoImpossible..ctor(this : ref) {
  var stack0o : ref;
  entry: assume $IsNotNull(this, AlsoImpossible); goto $$entry~f;
  $$entry~f: assume ($Heap[this, $allocated] == true); goto $$entry~e;
  $$entry~e: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto block2295;
  block2295: goto block2312;
  block2312: assert (this != null); goto $$block2312~g;
  $$block2312~g: call System.Object..ctor(this); goto $$block2312~f;
  $$block2312~f: assert false; goto $$block2312~e;
  $$block2312~e: assert (this != null); goto $$block2312~d;
  $$block2312~d: assert (($Heap[this, $inv] == System.Object) && ($Heap[this, $localinv] == $typeof(this))); goto $$block2312~c;
  $$block2312~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == AlsoImpossible)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block2312~b;
  $$block2312~b: $Heap := $Heap[this, $inv := AlsoImpossible]; goto $$block2312~a;
  $$block2312~a: assume IsHeap($Heap); return;
  
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
axiom (AlsoImpossibleSub <: AlsoImpossibleSub);
axiom ($BaseClass(AlsoImpossibleSub) == System.Object);
axiom ((AlsoImpossibleSub <: $BaseClass(AlsoImpossibleSub)) && (AsDirectSubClass(AlsoImpossibleSub, $BaseClass(AlsoImpossibleSub)) == AlsoImpossibleSub));
axiom (!$IsImmutable(AlsoImpossibleSub) && ($AsMutable(AlsoImpossibleSub) == AlsoImpossibleSub));
axiom $IsMemberlessType(AlsoImpossibleSub);
axiom (forall $U : name :: {($U <: AlsoImpossibleSub)} (($U <: AlsoImpossibleSub) ==> ($U == AlsoImpossibleSub)));
procedure AlsoImpossibleSub..ctor$System.Int32(this : ref, x$in : int where InRange(x$in, System.Int32));
  free requires true;
  free requires (forall $o : ref :: (($o != this) ==> ($Heap[$o, $ownerRef] != this)));
  free requires (($Heap[this, $ownerRef] == this) && ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder));
  free requires (forall $o : ref :: ((($Heap[$o, $ownerRef] == $Heap[this, $ownerRef]) && ($Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame])) ==> ($o == this)));
  free requires ($BeingConstructed == this);
  modifies $Heap;
  ensures ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == AlsoImpossibleSub)) && ($Heap[this, $localinv] == $typeof(this)));
  ensures (($Heap[this, $ownerRef] == old($Heap)[this, $ownerRef]) && ($Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame]));
  ensures ($Heap[this, $sharingMode] == $SharingMode_Unshared);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(AlsoImpossibleSub <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

implementation AlsoImpossibleSub..ctor$System.Int32(this : ref, x$in : int) {
  var x : int where InRange(x, System.Int32);
  var stack0o : ref;
  entry: assume $IsNotNull(this, AlsoImpossibleSub); goto $$entry~i;
  $$entry~i: assume ($Heap[this, $allocated] == true); goto $$entry~h;
  $$entry~h: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto $$entry~g;
  $$entry~g: x := x$in; goto block2771;
  block2771: goto block2788;
  block2788: assert false; goto $$block2788~e;
  $$block2788~e: assert (this != null); goto $$block2788~d;
  $$block2788~d: assert (($Heap[this, $inv] == System.Object) && ($Heap[this, $localinv] == $typeof(this))); goto $$block2788~c;
  $$block2788~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == AlsoImpossibleSub)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block2788~b;
  $$block2788~b: $Heap := $Heap[this, $inv := AlsoImpossibleSub]; goto $$block2788~a;
  $$block2788~a: assume IsHeap($Heap); return;
  
}

axiom (forall $U : name :: {($U <: System.Boolean)} (($U <: System.Boolean) ==> ($U == System.Boolean)));
procedure AlsoImpossibleSub..ctor$System.Boolean(this : ref, b$in : bool where true);
  free requires true;
  free requires (forall $o : ref :: (($o != this) ==> ($Heap[$o, $ownerRef] != this)));
  free requires (($Heap[this, $ownerRef] == this) && ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder));
  free requires (forall $o : ref :: ((($Heap[$o, $ownerRef] == $Heap[this, $ownerRef]) && ($Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame])) ==> ($o == this)));
  free requires ($BeingConstructed == this);
  modifies $Heap;
  ensures ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == AlsoImpossibleSub)) && ($Heap[this, $localinv] == $typeof(this)));
  ensures (($Heap[this, $ownerRef] == old($Heap)[this, $ownerRef]) && ($Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame]));
  ensures ($Heap[this, $sharingMode] == $SharingMode_Unshared);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(AlsoImpossibleSub <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

implementation AlsoImpossibleSub..ctor$System.Boolean(this : ref, b$in : bool) {
  var b : bool where true;
  var stack0o : ref;
  entry: assume $IsNotNull(this, AlsoImpossibleSub); goto $$entry~l;
  $$entry~l: assume ($Heap[this, $allocated] == true); goto $$entry~k;
  $$entry~k: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto $$entry~j;
  $$entry~j: b := b$in; goto block3230;
  block3230: goto block3247;
  block3247: assert (this != null); goto $$block3247~g;
  $$block3247~g: call System.Object..ctor(this); goto $$block3247~f;
  $$block3247~f: assert false; goto $$block3247~e;
  $$block3247~e: assert (this != null); goto $$block3247~d;
  $$block3247~d: assert (($Heap[this, $inv] == System.Object) && ($Heap[this, $localinv] == $typeof(this))); goto $$block3247~c;
  $$block3247~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == AlsoImpossibleSub)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block3247~b;
  $$block3247~b: $Heap := $Heap[this, $inv := AlsoImpossibleSub]; goto $$block3247~a;
  $$block3247~a: assume IsHeap($Heap); return;
  
}

axiom (D <: D);
axiom ($BaseClass(D) == System.Object);
axiom ((D <: $BaseClass(D)) && (AsDirectSubClass(D, $BaseClass(D)) == D));
axiom (!$IsImmutable(D) && ($AsMutable(D) == D));
axiom (forall $U : name :: {($U <: D)} (($U <: D) ==> ($U == D)));
procedure D.foo0$Impossible$notnull(this : ref, c$in : ref where $IsNotNull(c$in, Impossible)) returns ($result : int where InRange($result, System.Int32));
  free requires ($Heap[c$in, $allocated] == true);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[c$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[c$in, $ownerRef], $inv] <: $Heap[c$in, $ownerFrame])) || ($Heap[$Heap[c$in, $ownerRef], $localinv] == $BaseClass($Heap[c$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[c$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[c$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures true;
  free ensures InRange($result, System.Int32);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation D.foo0$Impossible$notnull(this : ref, c$in : ref) returns ($result : int) {
  var c : ref where $IsNotNull(c, Impossible);
  var stack0o : ref;
  entry: assume $IsNotNull(this, D); goto $$entry~n;
  $$entry~n: assume ($Heap[this, $allocated] == true); goto $$entry~m;
  $$entry~m: c := c$in; goto block3706;
  block3706: goto block3723;
  block3723: assert false; return;
  
}

procedure D.foo1$ImpossibleSub$notnull(this : ref, c$in : ref where $IsNotNull(c$in, ImpossibleSub)) returns ($result : int where InRange($result, System.Int32));
  free requires ($Heap[c$in, $allocated] == true);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[c$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[c$in, $ownerRef], $inv] <: $Heap[c$in, $ownerFrame])) || ($Heap[$Heap[c$in, $ownerRef], $localinv] == $BaseClass($Heap[c$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[c$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[c$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures true;
  free ensures InRange($result, System.Int32);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation D.foo1$ImpossibleSub$notnull(this : ref, c$in : ref) returns ($result : int) {
  var c : ref where $IsNotNull(c, ImpossibleSub);
  var stack0o : ref;
  entry: assume $IsNotNull(this, D); goto $$entry~p;
  $$entry~p: assume ($Heap[this, $allocated] == true); goto $$entry~o;
  $$entry~o: c := c$in; goto block4165;
  block4165: goto block4182;
  block4182: assert false; return;
  
}

procedure D.foo2$AlsoImpossible$notnull(this : ref, c$in : ref where $IsNotNull(c$in, AlsoImpossible)) returns ($result : int where InRange($result, System.Int32));
  free requires ($Heap[c$in, $allocated] == true);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[c$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[c$in, $ownerRef], $inv] <: $Heap[c$in, $ownerFrame])) || ($Heap[$Heap[c$in, $ownerRef], $localinv] == $BaseClass($Heap[c$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[c$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[c$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures true;
  free ensures InRange($result, System.Int32);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation D.foo2$AlsoImpossible$notnull(this : ref, c$in : ref) returns ($result : int) {
  var c : ref where $IsNotNull(c, AlsoImpossible);
  var stack0o : ref;
  entry: assume $IsNotNull(this, D); goto $$entry~r;
  $$entry~r: assume ($Heap[this, $allocated] == true); goto $$entry~q;
  $$entry~q: c := c$in; goto block4624;
  block4624: goto block4641;
  block4641: assert false; return;
  
}

procedure D.foo3$AlsoImpossibleSub$notnull(this : ref, c$in : ref where $IsNotNull(c$in, AlsoImpossibleSub)) returns ($result : int where InRange($result, System.Int32));
  free requires ($Heap[c$in, $allocated] == true);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[c$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[c$in, $ownerRef], $inv] <: $Heap[c$in, $ownerFrame])) || ($Heap[$Heap[c$in, $ownerRef], $localinv] == $BaseClass($Heap[c$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[c$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[c$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures true;
  free ensures InRange($result, System.Int32);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation D.foo3$AlsoImpossibleSub$notnull(this : ref, c$in : ref) returns ($result : int) {
  var c : ref where $IsNotNull(c, AlsoImpossibleSub);
  var stack0o : ref;
  entry: assume $IsNotNull(this, D); goto $$entry~t;
  $$entry~t: assume ($Heap[this, $allocated] == true); goto $$entry~s;
  $$entry~s: c := c$in; goto block5083;
  block5083: goto block5100;
  block5100: assert false; return;
  
}

procedure D.foo4$D$notnull(this : ref, d$in : ref where $IsNotNull(d$in, D)) returns ($result : int where InRange($result, System.Int32));
  free requires ($Heap[d$in, $allocated] == true);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[d$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[d$in, $ownerRef], $inv] <: $Heap[d$in, $ownerFrame])) || ($Heap[$Heap[d$in, $ownerRef], $localinv] == $BaseClass($Heap[d$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[d$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[d$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures true;
  free ensures InRange($result, System.Int32);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation D.foo4$D$notnull(this : ref, d$in : ref) returns ($result : int) {
  var d : ref where $IsNotNull(d, D);
  var stack0o : ref;
  entry: assume $IsNotNull(this, D); goto $$entry~v;
  $$entry~v: assume ($Heap[this, $allocated] == true); goto $$entry~u;
  $$entry~u: d := d$in; goto block5542;
  block5542: goto block5559;
  block5559: assert false; return;
  
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
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(D <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

implementation D..ctor(this : ref) {
  entry: assume $IsNotNull(this, D); goto $$entry~x;
  $$entry~x: assume ($Heap[this, $allocated] == true); goto $$entry~w;
  $$entry~w: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto block5899;
  block5899: goto block5916;
  block5916: assert (this != null); goto $$block5916~f;
  $$block5916~f: call System.Object..ctor(this); goto $$block5916~e;
  $$block5916~e: assert (this != null); goto $$block5916~d;
  $$block5916~d: assert (($Heap[this, $inv] == System.Object) && ($Heap[this, $localinv] == $typeof(this))); goto $$block5916~c;
  $$block5916~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == D)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block5916~b;
  $$block5916~b: $Heap := $Heap[this, $inv := D]; goto $$block5916~a;
  $$block5916~a: assume IsHeap($Heap); return;
  
}

axiom (C0 <: C0);
axiom ($BaseClass(C0) == System.Object);
axiom ((C0 <: $BaseClass(C0)) && (AsDirectSubClass(C0, $BaseClass(C0)) == C0));
axiom (!$IsImmutable(C0) && ($AsMutable(C0) == C0));
axiom (forall $U : name :: {($U <: C0)} (($U <: C0) ==> ($U == C0)));
procedure C0.foo0(this : ref) returns ($result : int where InRange($result, System.Int32));
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures true;
  free ensures InRange($result, System.Int32);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation C0.foo0(this : ref) returns ($result : int) {
  var stack0o : ref;
  var return.value : int where InRange(return.value, System.Int32);
  var SS$Display.Return.Local : int where InRange(SS$Display.Return.Local, System.Int32);
  var stack0i : int;
  entry: assume $IsNotNull(this, C0); goto $$entry~y;
  $$entry~y: assume ($Heap[this, $allocated] == true); goto block6426;
  block6426: goto block6443;
  block6443: assert (this != null); goto $$block6443~c;
  $$block6443~c: stack0o := $Heap[this, C0.s]; goto $$block6443~b;
  $$block6443~b: assert (stack0o != null); goto $$block6443~a;
  $$block6443~a: return.value := $StringLength(stack0o); goto block6460;
  block6460: SS$Display.Return.Local := return.value; goto $$block6460~b;
  $$block6460~b: stack0i := return.value; goto $$block6460~a;
  $$block6460~a: $result := stack0i; return;
  
}

procedure C0.foo1(this : ref) returns ($result : int where InRange($result, System.Int32));
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures true;
  free ensures InRange($result, System.Int32);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation C0.foo1(this : ref) returns ($result : int) {
  var stack0o : ref;
  var return.value : int where InRange(return.value, System.Int32);
  var SS$Display.Return.Local : int where InRange(SS$Display.Return.Local, System.Int32);
  var stack0i : int;
  entry: assume $IsNotNull(this, C0); goto $$entry~z;
  $$entry~z: assume ($Heap[this, $allocated] == true); goto block6800;
  block6800: goto block6817;
  block6817: assert ($Heap[this, C0.t] != null); goto block6902;
  block6902: return.value := 0; goto block6919;
  block6919: SS$Display.Return.Local := return.value; goto $$block6919~b;
  $$block6919~b: stack0i := return.value; goto $$block6919~a;
  $$block6919~a: $result := stack0i; return;
  
}

procedure C0..ctor(this : ref);
  free requires (forall $o : ref :: (($o != this) ==> ($Heap[$o, $ownerRef] != this)));
  free requires (($Heap[this, $ownerRef] == this) && ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder));
  free requires (forall $o : ref :: ((($Heap[$o, $ownerRef] == $Heap[this, $ownerRef]) && ($Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame])) ==> ($o == this)));
  free requires ($BeingConstructed == this);
  modifies $Heap;
  ensures ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == C0)) && ($Heap[this, $localinv] == $typeof(this)));
  ensures (($Heap[this, $ownerRef] == old($Heap)[this, $ownerRef]) && ($Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame]));
  ensures ($Heap[this, $sharingMode] == $SharingMode_Unshared);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(C0 <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

implementation C0..ctor(this : ref) {
  var stack0o : ref;
  var temp0 : exposeVersionType;
  var temp1 : exposeVersionType;
  entry: assume $IsNotNull(this, C0); goto $$entry~ac;
  $$entry~ac: assume ($Heap[this, $allocated] == true); goto $$entry~ab;
  $$entry~ab: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto $$entry~aa;
  $$entry~aa: assume ($Heap[this, C0.t] == null); goto block7225;
  block7225: goto block7242;
  block7242: stack0o := $stringLiteral2; goto $$block7242~r;
  $$block7242~r: assert (this != null); goto $$block7242~q;
  $$block7242~q: havoc temp0; goto $$block7242~p;
  $$block7242~p: $Heap := $Heap[this, $exposeVersion := temp0]; goto $$block7242~o;
  $$block7242~o: $Heap := $Heap[this, C0.s := stack0o]; goto $$block7242~n;
  $$block7242~n: assume IsHeap($Heap); goto $$block7242~m;
  $$block7242~m: stack0o := $stringLiteral2; goto $$block7242~l;
  $$block7242~l: assert (this != null); goto $$block7242~k;
  $$block7242~k: havoc temp1; goto $$block7242~j;
  $$block7242~j: $Heap := $Heap[this, $exposeVersion := temp1]; goto $$block7242~i;
  $$block7242~i: $Heap := $Heap[this, C0.t := stack0o]; goto $$block7242~h;
  $$block7242~h: assume IsHeap($Heap); goto $$block7242~g;
  $$block7242~g: assert (this != null); goto $$block7242~f;
  $$block7242~f: call System.Object..ctor(this); goto $$block7242~e;
  $$block7242~e: assert (this != null); goto $$block7242~d;
  $$block7242~d: assert (($Heap[this, $inv] == System.Object) && ($Heap[this, $localinv] == $typeof(this))); goto $$block7242~c;
  $$block7242~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == C0)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block7242~b;
  $$block7242~b: $Heap := $Heap[this, $inv := C0]; goto $$block7242~a;
  $$block7242~a: assume IsHeap($Heap); return;
  
}

axiom (C1 <: C1);
axiom ($BaseClass(C1) == System.Object);
axiom ((C1 <: $BaseClass(C1)) && (AsDirectSubClass(C1, $BaseClass(C1)) == C1));
axiom (!$IsImmutable(C1) && ($AsMutable(C1) == C1));
axiom (forall $U : name :: {($U <: C1)} (($U <: C1) ==> ($U == C1)));
procedure C1.X0(this : ref);
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
  

implementation C1.X0(this : ref) {
  var stack0o : ref;
  entry: assume $IsNotNull(this, C1); goto $$entry~ad;
  $$entry~ad: assume ($Heap[this, $allocated] == true); goto block7565;
  block7565: goto block7582;
  block7582: assert ($Heap[this, C1.impX] != null); goto block7667;
  block7667: return;
  
}

procedure C1.X1(this : ref);
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
  

implementation C1.X1(this : ref) {
  var stack0o : ref;
  entry: assume $IsNotNull(this, C1); goto $$entry~ae;
  $$entry~ae: assume ($Heap[this, $allocated] == true); goto block7990;
  block7990: goto block8007;
  block8007: assert ($Heap[this, C1.impX] == null); goto block8092;
  block8092: return;
  
}

procedure C1.Y0(this : ref);
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
  

implementation C1.Y0(this : ref) {
  var stack0o : ref;
  entry: assume $IsNotNull(this, C1); goto $$entry~af;
  $$entry~af: assume ($Heap[this, $allocated] == true); goto block8415;
  block8415: goto block8432;
  block8432: assert (#C1.impY(this) != null); goto block8517;
  block8517: return;
  
}

procedure C1.Y1(this : ref);
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
  

implementation C1.Y1(this : ref) {
  var stack0o : ref;
  entry: assume $IsNotNull(this, C1); goto $$entry~ag;
  $$entry~ag: assume ($Heap[this, $allocated] == true); goto block8840;
  block8840: goto block8857;
  block8857: assert (#C1.impY(this) == null); goto block8942;
  block8942: return;
  
}

procedure C1.M(this : ref) returns ($result : ref where $Is($result, Impossible));
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures ($Heap[$result, $allocated] == true);
  free ensures $Is($result, Impossible);
  ensures (($result == null) || (((($Heap[$result, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[$result, $ownerRef], $inv] <: $Heap[$result, $ownerFrame])) || ($Heap[$Heap[$result, $ownerRef], $localinv] == $BaseClass($Heap[$result, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))));
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation C1.M(this : ref) returns ($result : ref) {
  var $Heap$block9231$LoopPreheader : <x>[ref, name]x;
  entry: assume $IsNotNull(this, C1); goto $$entry~ah;
  $$entry~ah: assume ($Heap[this, $allocated] == true); goto block9214;
  block9214: goto block9231$LoopPreheader;
  block9231: assume (((forall $o : ref :: (($Heap$block9231$LoopPreheader[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: ((($Heap$block9231$LoopPreheader[$ot, $allocated] == true) && ($Heap$block9231$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == $Heap$block9231$LoopPreheader[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == $Heap$block9231$LoopPreheader[$ot, $ownerFrame]))))) && ($Heap$block9231$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized])); goto $$block9231~c;
  $$block9231~c: assume (forall $o : ref :: ((($Heap$block9231$LoopPreheader[$o, $inv] == $Heap[$o, $inv]) && ($Heap$block9231$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv])) || ($Heap$block9231$LoopPreheader[$o, $allocated] != true))); goto $$block9231~b;
  $$block9231~b: assume (forall $o : ref :: ((($Heap$block9231$LoopPreheader[$o, $allocated] != true) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o))))); goto $$block9231~a;
  $$block9231~a: assert (forall $o : ref :: ((($o != null) && ($Heap$block9231$LoopPreheader[$o, $allocated] == true)) ==> (($Heap$block9231$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef]) && ($Heap$block9231$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame])))); goto block9248;
  block9248: goto block9231;
  block9231$LoopPreheader: $Heap$block9231$LoopPreheader := $Heap; goto block9231;
  
}

procedure C1.Z0(this : ref) returns ($result : ref where $Is($result, System.Object));
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures ($Heap[$result, $allocated] == true);
  free ensures $Is($result, System.Object);
  ensures ($result == null);
  ensures (($result == null) || (((($Heap[$result, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[$result, $ownerRef], $inv] <: $Heap[$result, $ownerFrame])) || ($Heap[$Heap[$result, $ownerRef], $localinv] == $BaseClass($Heap[$result, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))));
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation C1.Z0(this : ref) returns ($result : ref) {
  var o : ref where $Is(o, System.Object);
  var return.value : ref where $Is(return.value, System.Object);
  var SS$Display.Return.Local : ref where $Is(SS$Display.Return.Local, System.Object);
  var stack0o : ref;
  entry: assume $IsNotNull(this, C1); goto $$entry~ai;
  $$entry~ai: assume ($Heap[this, $allocated] == true); goto block9520;
  block9520: goto block9537;
  block9537: assert (this != null); goto $$block9537~b;
  $$block9537~b: call o := C1.M(this); goto $$block9537~a;
  $$block9537~a: return.value := o; goto block9639;
  block9639: SS$Display.Return.Local := return.value; goto $$block9639~b;
  $$block9639~b: stack0o := return.value; goto $$block9639~a;
  $$block9639~a: $result := stack0o; return;
  
}

procedure C1.Z1(this : ref) returns ($result : ref where $Is($result, System.Object));
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures ($Heap[$result, $allocated] == true);
  free ensures $Is($result, System.Object);
  ensures (($result == null) || (((($Heap[$result, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[$result, $ownerRef], $inv] <: $Heap[$result, $ownerFrame])) || ($Heap[$Heap[$result, $ownerRef], $localinv] == $BaseClass($Heap[$result, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))));
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation C1.Z1(this : ref) returns ($result : ref) {
  var o : ref where $Is(o, System.Object);
  var stack0o : ref;
  entry: assume $IsNotNull(this, C1); goto $$entry~aj;
  $$entry~aj: assume ($Heap[this, $allocated] == true); goto block10030;
  block10030: goto block10047;
  block10047: assert (this != null); goto $$block10047~b;
  $$block10047~b: call o := C1.M(this); goto $$block10047~a;
  $$block10047~a: assert false; return;
  
}

axiom (forall $Heap : <x>[ref, name]x, this : ref :: {#C1.P($Heap, this)} ((IsHeap($Heap) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))) ==> ((($Heap[#C1.P($Heap, this), $allocated] == true) && $Is(#C1.P($Heap, this), Impossible)) && ((#C1.P($Heap, this) == null) || (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[#C1.P($Heap, this), $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[#C1.P($Heap, this), $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))))));
axiom (forall $Heap : <x>[ref, name]x, this : ref :: {#C1.P($Heap, this)} (((((((this != null) && ($typeof(this) <: C1)) && ($Heap[this, $inv] == $typeof(this))) && ($Heap[this, $localinv] == $typeof(this))) && IsHeap($Heap)) && ($Heap[this, $allocated] == true)) ==> (#C1.P($Heap, this) == ##C1.P($Heap[this, $exposeVersion]))));
procedure C1.P(this : ref) returns ($result : ref where $Is($result, Impossible));
  requires (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))));
  free requires ($AsPureObject(this) == this);
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures ($Heap[$result, $allocated] == true);
  free ensures $Is($result, Impossible);
  ensures (($result == null) || (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures ($result == #C1.P($Heap, this));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} ((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation C1.P(this : ref) returns ($result : ref) {
  var $Heap$block10455$LoopPreheader : <x>[ref, name]x;
  entry: assume $IsNotNull(this, C1); goto $$entry~ak;
  $$entry~ak: assume ($Heap[this, $allocated] == true); goto block10438;
  block10438: goto block10455$LoopPreheader;
  block10455: assume (((forall $o : ref :: (($Heap$block10455$LoopPreheader[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: ((($Heap$block10455$LoopPreheader[$ot, $allocated] == true) && ($Heap$block10455$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == $Heap$block10455$LoopPreheader[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == $Heap$block10455$LoopPreheader[$ot, $ownerFrame]))))) && ($Heap$block10455$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized])); goto $$block10455~c;
  $$block10455~c: assume (forall $o : ref :: ((($Heap$block10455$LoopPreheader[$o, $inv] == $Heap[$o, $inv]) && ($Heap$block10455$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv])) || ($Heap$block10455$LoopPreheader[$o, $allocated] != true))); goto $$block10455~b;
  $$block10455~b: assume (forall $o : ref :: ((($Heap$block10455$LoopPreheader[$o, $allocated] != true) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o))))); goto $$block10455~a;
  $$block10455~a: assert (forall $o : ref :: ((($o != null) && ($Heap$block10455$LoopPreheader[$o, $allocated] == true)) ==> (($Heap$block10455$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef]) && ($Heap$block10455$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame])))); goto block10472;
  block10472: goto block10455;
  block10455$LoopPreheader: $Heap$block10455$LoopPreheader := $Heap; goto block10455;
  
}

procedure C1.W0(this : ref) returns ($result : ref where $Is($result, System.Object));
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures ($Heap[$result, $allocated] == true);
  free ensures $Is($result, System.Object);
  ensures ($result == null);
  ensures (($result == null) || (((($Heap[$result, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[$result, $ownerRef], $inv] <: $Heap[$result, $ownerFrame])) || ($Heap[$Heap[$result, $ownerRef], $localinv] == $BaseClass($Heap[$result, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))));
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation C1.W0(this : ref) returns ($result : ref) {
  var o : ref where $Is(o, System.Object);
  var return.value : ref where $Is(return.value, System.Object);
  var SS$Display.Return.Local : ref where $Is(SS$Display.Return.Local, System.Object);
  var stack0o : ref;
  entry: assume $IsNotNull(this, C1); goto $$entry~al;
  $$entry~al: assume ($Heap[this, $allocated] == true); goto block10744;
  block10744: goto block10761;
  block10761: assert (this != null); goto $$block10761~b;
  $$block10761~b: call o := C1.P(this); goto $$block10761~a;
  $$block10761~a: return.value := o; goto block10863;
  block10863: SS$Display.Return.Local := return.value; goto $$block10863~b;
  $$block10863~b: stack0o := return.value; goto $$block10863~a;
  $$block10863~a: $result := stack0o; return;
  
}

procedure C1.W1(this : ref) returns ($result : ref where $Is($result, System.Object));
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures ($Heap[$result, $allocated] == true);
  free ensures $Is($result, System.Object);
  ensures (($result == null) || (((($Heap[$result, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[$result, $ownerRef], $inv] <: $Heap[$result, $ownerFrame])) || ($Heap[$Heap[$result, $ownerRef], $localinv] == $BaseClass($Heap[$result, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))));
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation C1.W1(this : ref) returns ($result : ref) {
  var o : ref where $Is(o, System.Object);
  var stack0o : ref;
  entry: assume $IsNotNull(this, C1); goto $$entry~am;
  $$entry~am: assume ($Heap[this, $allocated] == true); goto block11254;
  block11254: goto block11271;
  block11271: assert (this != null); goto $$block11271~b;
  $$block11271~b: call o := C1.P(this); goto $$block11271~a;
  $$block11271~a: assert false; return;
  
}

procedure C1.W2(this : ref);
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
  

implementation C1.W2(this : ref) {
  var stack0o : ref;
  entry: assume $IsNotNull(this, C1); goto $$entry~an;
  $$entry~an: assume ($Heap[this, $allocated] == true); goto block11713;
  block11713: goto block11730;
  block11730: assert (#C1.P($Heap, this) == null); goto block11815;
  block11815: return;
  
}

procedure C1.W3(this : ref);
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
  

implementation C1.W3(this : ref) {
  var stack0o : ref;
  entry: assume $IsNotNull(this, C1); goto $$entry~ao;
  $$entry~ao: assume ($Heap[this, $allocated] == true); goto block12138;
  block12138: goto block12155;
  block12155: assert (#C1.P($Heap, this) != null); goto block12240;
  block12240: return;
  
}

procedure C1..ctor(this : ref);
  free requires (forall $o : ref :: (($o != this) ==> ($Heap[$o, $ownerRef] != this)));
  free requires (($Heap[this, $ownerRef] == this) && ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder));
  free requires (forall $o : ref :: ((($Heap[$o, $ownerRef] == $Heap[this, $ownerRef]) && ($Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame])) ==> ($o == this)));
  free requires ($BeingConstructed == this);
  modifies $Heap;
  ensures ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == C1)) && ($Heap[this, $localinv] == $typeof(this)));
  ensures (($Heap[this, $ownerRef] == old($Heap)[this, $ownerRef]) && ($Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame]));
  ensures ($Heap[this, $sharingMode] == $SharingMode_Unshared);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(C1 <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

implementation C1..ctor(this : ref) {
  entry: assume $IsNotNull(this, C1); goto $$entry~ar;
  $$entry~ar: assume ($Heap[this, $allocated] == true); goto $$entry~aq;
  $$entry~aq: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto $$entry~ap;
  $$entry~ap: assume ($Heap[this, C1.impX] == null); goto block12478;
  block12478: goto block12495;
  block12495: assert (this != null); goto $$block12495~f;
  $$block12495~f: call System.Object..ctor(this); goto $$block12495~e;
  $$block12495~e: assert (this != null); goto $$block12495~d;
  $$block12495~d: assert (($Heap[this, $inv] == System.Object) && ($Heap[this, $localinv] == $typeof(this))); goto $$block12495~c;
  $$block12495~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == C1)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block12495~b;
  $$block12495~b: $Heap := $Heap[this, $inv := C1]; goto $$block12495~a;
  $$block12495~a: assume IsHeap($Heap); return;
  
}

axiom (C2 <: C2);
axiom ($BaseClass(C2) == System.Object);
axiom ((C2 <: $BaseClass(C2)) && (AsDirectSubClass(C2, $BaseClass(C2)) == C2));
axiom (!$IsImmutable(C2) && ($AsMutable(C2) == C2));
axiom (forall $U : name :: {($U <: C2)} (($U <: C2) ==> ($U == C2)));
procedure C2..ctor(this : ref);
  free requires (forall $o : ref :: (($o != this) ==> ($Heap[$o, $ownerRef] != this)));
  free requires (($Heap[this, $ownerRef] == this) && ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder));
  free requires (forall $o : ref :: ((($Heap[$o, $ownerRef] == $Heap[this, $ownerRef]) && ($Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame])) ==> ($o == this)));
  free requires ($BeingConstructed == this);
  modifies $Heap;
  ensures ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == C2)) && ($Heap[this, $localinv] == $typeof(this)));
  ensures (($Heap[this, $ownerRef] == old($Heap)[this, $ownerRef]) && ($Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame]));
  ensures ($Heap[this, $sharingMode] == $SharingMode_Unshared);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(C2 <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

implementation C2..ctor(this : ref) {
  var stack0o : ref;
  entry: assume $IsNotNull(this, C2); goto $$entry~at;
  $$entry~at: assume ($Heap[this, $allocated] == true); goto $$entry~as;
  $$entry~as: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto block12767;
  block12767: goto block12784;
  block12784: assert (this != null); goto $$block12784~g;
  $$block12784~g: call System.Object..ctor(this); goto $$block12784~f;
  $$block12784~f: assert false; goto $$block12784~e;
  $$block12784~e: assert (this != null); goto $$block12784~d;
  $$block12784~d: assert (($Heap[this, $inv] == System.Object) && ($Heap[this, $localinv] == $typeof(this))); goto $$block12784~c;
  $$block12784~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == C2)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block12784~b;
  $$block12784~b: $Heap := $Heap[this, $inv := C2]; goto $$block12784~a;
  $$block12784~a: assume IsHeap($Heap); return;
  
}

procedure C2.X0(this : ref);
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
  

implementation C2.X0(this : ref) {
  var stack0o : ref;
  entry: assume $IsNotNull(this, C2); goto $$entry~au;
  $$entry~au: assume ($Heap[this, $allocated] == true); goto block13226;
  block13226: goto block13243;
  block13243: assert ($Heap[this, C2.impX] != null); goto block13328;
  block13328: return;
  
}

procedure C2.X1(this : ref);
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation C2.X1(this : ref) {
  var stack0o : ref;
  entry: assume $IsNotNull(this, C2); goto $$entry~av;
  $$entry~av: assume ($Heap[this, $allocated] == true); goto block13651;
  block13651: goto block13668;
  block13668: assert ($Heap[this, C2.impX] != null); goto block13753;
  block13753: return;
  
}

procedure C2.X2(this : ref);
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation C2.X2(this : ref) {
  var stack0o : ref;
  entry: assume $IsNotNull(this, C2); goto $$entry~aw;
  $$entry~aw: assume ($Heap[this, $allocated] == true); goto block14093;
  block14093: goto block14110;
  block14110: assert false; return;
  
}

procedure C2.X3(this : ref);
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation C2.X3(this : ref) {
  var stack0o : ref;
  entry: assume $IsNotNull(this, C2); goto $$entry~ax;
  $$entry~ax: assume ($Heap[this, $allocated] == true); goto block14535;
  block14535: goto block14552;
  block14552: assert ($Heap[this, C2.impX] == null); goto block14637;
  block14637: return;
  
}

procedure C2.Y0(this : ref);
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
  

implementation C2.Y0(this : ref) {
  var stack0o : ref;
  entry: assume $IsNotNull(this, C2); goto $$entry~ay;
  $$entry~ay: assume ($Heap[this, $allocated] == true); goto block14960;
  block14960: goto block14977;
  block14977: assert (#C2.impY(this) != null); goto block15062;
  block15062: return;
  
}

procedure C2.Y1(this : ref);
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation C2.Y1(this : ref) {
  var stack0o : ref;
  entry: assume $IsNotNull(this, C2); goto $$entry~az;
  $$entry~az: assume ($Heap[this, $allocated] == true); goto block15385;
  block15385: goto block15402;
  block15402: assert (#C2.impY(this) != null); goto block15487;
  block15487: return;
  
}

procedure C2.Y2(this : ref);
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation C2.Y2(this : ref) {
  var stack0o : ref;
  entry: assume $IsNotNull(this, C2); goto $$entry~ba;
  $$entry~ba: assume ($Heap[this, $allocated] == true); goto block15827;
  block15827: goto block15844;
  block15844: assert false; return;
  
}

procedure C2.Y3(this : ref);
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation C2.Y3(this : ref) {
  var stack0o : ref;
  entry: assume $IsNotNull(this, C2); goto $$entry~bb;
  $$entry~bb: assume ($Heap[this, $allocated] == true); goto block16269;
  block16269: goto block16286;
  block16286: assert (#C2.impY(this) == null); goto block16371;
  block16371: return;
  
}

procedure C2.M(this : ref) returns ($result : ref where $IsNotNull($result, Impossible));
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures ($Heap[$result, $allocated] == true);
  free ensures $IsNotNull($result, Impossible);
  ensures (((($Heap[$result, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[$result, $ownerRef], $inv] <: $Heap[$result, $ownerFrame])) || ($Heap[$Heap[$result, $ownerRef], $localinv] == $BaseClass($Heap[$result, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation C2.M(this : ref) returns ($result : ref) {
  var $Heap$block16660$LoopPreheader : <x>[ref, name]x;
  entry: assume $IsNotNull(this, C2); goto $$entry~bc;
  $$entry~bc: assume ($Heap[this, $allocated] == true); goto block16643;
  block16643: goto block16660$LoopPreheader;
  block16660: assume (((forall $o : ref :: (($Heap$block16660$LoopPreheader[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: ((($Heap$block16660$LoopPreheader[$ot, $allocated] == true) && ($Heap$block16660$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == $Heap$block16660$LoopPreheader[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == $Heap$block16660$LoopPreheader[$ot, $ownerFrame]))))) && ($Heap$block16660$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized])); goto $$block16660~c;
  $$block16660~c: assume (forall $o : ref :: ((($Heap$block16660$LoopPreheader[$o, $inv] == $Heap[$o, $inv]) && ($Heap$block16660$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv])) || ($Heap$block16660$LoopPreheader[$o, $allocated] != true))); goto $$block16660~b;
  $$block16660~b: assume (forall $o : ref :: ((($Heap$block16660$LoopPreheader[$o, $allocated] != true) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o))))); goto $$block16660~a;
  $$block16660~a: assert (forall $o : ref :: ((($o != null) && ($Heap$block16660$LoopPreheader[$o, $allocated] == true)) ==> (($Heap$block16660$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef]) && ($Heap$block16660$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame])))); goto block16677;
  block16677: goto block16660;
  block16660$LoopPreheader: $Heap$block16660$LoopPreheader := $Heap; goto block16660;
  
}

procedure C2.Z0(this : ref) returns ($result : ref where $Is($result, System.Object));
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures ($Heap[$result, $allocated] == true);
  free ensures $Is($result, System.Object);
  ensures (($result == null) || (((($Heap[$result, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[$result, $ownerRef], $inv] <: $Heap[$result, $ownerFrame])) || ($Heap[$Heap[$result, $ownerRef], $localinv] == $BaseClass($Heap[$result, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))));
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation C2.Z0(this : ref) returns ($result : ref) {
  var o : ref where $Is(o, System.Object);
  var stack0o : ref;
  entry: assume $IsNotNull(this, C2); goto $$entry~bd;
  $$entry~bd: assume ($Heap[this, $allocated] == true); goto block16949;
  block16949: goto block16966;
  block16966: assert (this != null); goto $$block16966~b;
  $$block16966~b: call o := C2.M(this); goto $$block16966~a;
  $$block16966~a: assert false; return;
  
}

axiom (forall $Heap : <x>[ref, name]x, this : ref :: {#C2.P($Heap, this)} ((IsHeap($Heap) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))) ==> (($Heap[#C2.P($Heap, this), $allocated] == true) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[#C2.P($Heap, this), $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[#C2.P($Heap, this), $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))))));
axiom (forall $Heap : <x>[ref, name]x, this : ref :: {#C2.P($Heap, this)} (((((((this != null) && ($typeof(this) <: C2)) && ($Heap[this, $inv] == $typeof(this))) && ($Heap[this, $localinv] == $typeof(this))) && IsHeap($Heap)) && ($Heap[this, $allocated] == true)) ==> (#C2.P($Heap, this) == ##C2.P($Heap[this, $exposeVersion]))));
procedure C2.P(this : ref) returns ($result : ref where $IsNotNull($result, Impossible));
  requires (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))));
  free requires ($AsPureObject(this) == this);
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures ($Heap[$result, $allocated] == true);
  free ensures $IsNotNull($result, Impossible);
  ensures (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))));
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures ($result == #C2.P($Heap, this));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} ((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation C2.P(this : ref) returns ($result : ref) {
  var $Heap$block17374$LoopPreheader : <x>[ref, name]x;
  entry: assume $IsNotNull(this, C2); goto $$entry~be;
  $$entry~be: assume ($Heap[this, $allocated] == true); goto block17357;
  block17357: goto block17374$LoopPreheader;
  block17374: assume (((forall $o : ref :: (($Heap$block17374$LoopPreheader[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: ((($Heap$block17374$LoopPreheader[$ot, $allocated] == true) && ($Heap$block17374$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == $Heap$block17374$LoopPreheader[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == $Heap$block17374$LoopPreheader[$ot, $ownerFrame]))))) && ($Heap$block17374$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized])); goto $$block17374~c;
  $$block17374~c: assume (forall $o : ref :: ((($Heap$block17374$LoopPreheader[$o, $inv] == $Heap[$o, $inv]) && ($Heap$block17374$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv])) || ($Heap$block17374$LoopPreheader[$o, $allocated] != true))); goto $$block17374~b;
  $$block17374~b: assume (forall $o : ref :: ((($Heap$block17374$LoopPreheader[$o, $allocated] != true) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o))))); goto $$block17374~a;
  $$block17374~a: assert (forall $o : ref :: ((($o != null) && ($Heap$block17374$LoopPreheader[$o, $allocated] == true)) ==> (($Heap$block17374$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef]) && ($Heap$block17374$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame])))); goto block17391;
  block17391: goto block17374;
  block17374$LoopPreheader: $Heap$block17374$LoopPreheader := $Heap; goto block17374;
  
}

procedure C2.W0(this : ref) returns ($result : ref where $Is($result, System.Object));
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures ($Heap[$result, $allocated] == true);
  free ensures $Is($result, System.Object);
  ensures (($result == null) || (((($Heap[$result, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[$result, $ownerRef], $inv] <: $Heap[$result, $ownerFrame])) || ($Heap[$Heap[$result, $ownerRef], $localinv] == $BaseClass($Heap[$result, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))));
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation C2.W0(this : ref) returns ($result : ref) {
  var o : ref where $Is(o, System.Object);
  var stack0o : ref;
  entry: assume $IsNotNull(this, C2); goto $$entry~bf;
  $$entry~bf: assume ($Heap[this, $allocated] == true); goto block17663;
  block17663: goto block17680;
  block17680: assert (this != null); goto $$block17680~b;
  $$block17680~b: call o := C2.P(this); goto $$block17680~a;
  $$block17680~a: assert false; return;
  
}

procedure C2.W1(this : ref);
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
  

implementation C2.W1(this : ref) {
  var stack0o : ref;
  entry: assume $IsNotNull(this, C2); goto $$entry~bg;
  $$entry~bg: assume ($Heap[this, $allocated] == true); goto block18122;
  block18122: goto block18139;
  block18139: assert (#C2.P($Heap, this) == null); goto block18224;
  block18224: return;
  
}

procedure C2.W2(this : ref);
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
  

implementation C2.W2(this : ref) {
  var stack0o : ref;
  entry: assume $IsNotNull(this, C2); goto $$entry~bh;
  $$entry~bh: assume ($Heap[this, $allocated] == true); goto block18547;
  block18547: goto block18564;
  block18564: assert (#C2.P($Heap, this) != null); goto block18649;
  block18649: return;
  
}

const $stringLiteral2 : ref;
axiom (((forall heap : <x>[ref, name]x :: {heap[$stringLiteral2, $allocated]} (IsHeap(heap) ==> heap[$stringLiteral2, $allocated])) && $IsNotNull($stringLiteral2, System.String)) && ($StringLength($stringLiteral2) == 3));
axiom (((forall heap : <x>[ref, name]x :: {heap[$stringLiteral2, $allocated]} (IsHeap(heap) ==> heap[$stringLiteral2, $allocated])) && $IsNotNull($stringLiteral2, System.String)) && (#System.String.IsInterned$System.String$notnull($stringLiteral2) == $stringLiteral2));
