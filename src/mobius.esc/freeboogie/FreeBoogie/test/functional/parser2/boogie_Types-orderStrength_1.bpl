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
const T.x : name;
const T.g : name;
const T.y : name;
const T.next : name;
const System.Collections.ICollection : name;
const System.ICloneable : name;
const System.Boolean : name;
const L : name;
const J : name;
const System.IEquatable`1...System.String : name;
const F : name;
const System.Runtime.InteropServices._Type : name;
const System.Reflection.IReflect : name;
const T : name;
const System.IComparable : name;
const K : name;
const System.Runtime.InteropServices._MemberInfo : name;
const System.Reflection.MemberInfo : name;
const A : name;
const MoreTypes : name;
const System.Collections.IList : name;
const Types : name;
const System.Collections.IEnumerable : name;
const System.IConvertible : name;
const System.Reflection.ICustomAttributeProvider : name;
const System.Collections.Generic.IEnumerable`1...System.Char : name;
const D : name;
const B : name;
const System.IComparable`1...System.String : name;
const C : name;
axiom !IsStaticField(T.x);
axiom IsDirectlyModifiableField(T.x);
axiom (DeclType(T.x) == T);
axiom (AsRefField(T.x, D) == T.x);
axiom !IsStaticField(T.y);
axiom IsDirectlyModifiableField(T.y);
axiom (DeclType(T.y) == T);
axiom (AsNonNullRefField(T.y, D) == T.y);
axiom !IsStaticField(T.next);
axiom IsDirectlyModifiableField(T.next);
axiom (DeclType(T.next) == T);
axiom (AsRefField(T.next, T) == T.next);
axiom IsStaticField(T.g);
axiom IsDirectlyModifiableField(T.g);
axiom (DeclType(T.g) == T);
axiom (AsRefField(T.g, C) == T.g);
axiom (Types <: Types);
axiom ($BaseClass(Types) == System.Object);
axiom ((Types <: $BaseClass(Types)) && (AsDirectSubClass(Types, $BaseClass(Types)) == Types));
axiom (!$IsImmutable(Types) && ($AsMutable(Types) == Types));
axiom (forall $K : name :: {(Types <: $K)} ((Types <: $K) <==> ((Types == $K) || (System.Object <: $K))));
axiom (forall $U : name :: {($U <: Types)} (($U <: Types) ==> ($U == Types)));
procedure Types.Main();
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Types.Main() {
  entry: goto block1785;
  block1785: goto block1802;
  block1802: return;
  
}

axiom (B <: B);
axiom (A <: A);
axiom ($BaseClass(A) == System.Object);
axiom ((A <: $BaseClass(A)) && (AsDirectSubClass(A, $BaseClass(A)) == A));
axiom (!$IsImmutable(A) && ($AsMutable(A) == A));
axiom (forall $K : name :: {(A <: $K)} ((A <: $K) <==> ((A == $K) || (System.Object <: $K))));
axiom ($BaseClass(B) == A);
axiom ((B <: $BaseClass(B)) && (AsDirectSubClass(B, $BaseClass(B)) == B));
axiom (!$IsImmutable(B) && ($AsMutable(B) == B));
axiom (J <: System.Object);
axiom (forall $K : name :: {(J <: $K)} ((J <: $K) <==> ((J == $K) || (System.Object == $K))));
axiom $IsMemberlessType(J);
axiom (B <: J);
axiom (forall $K : name :: {(B <: $K)} ((B <: $K) <==> (((B == $K) || (A <: $K)) || (J <: $K))));
axiom (forall $U : name :: {($U <: System.Boolean)} (($U <: System.Boolean) ==> ($U == System.Boolean)));
procedure Types.M0$B$notnull$System.Boolean(this : ref, b$in : ref where $IsNotNull(b$in, B), maybe$in : bool where true);
  free requires ($Heap[b$in, $allocated] == true);
  free requires true;
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[b$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[b$in, $ownerRef], $inv] <: $Heap[b$in, $ownerFrame])) || ($Heap[$Heap[b$in, $ownerRef], $localinv] == $BaseClass($Heap[b$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[b$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[b$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Types.M0$B$notnull$System.Boolean(this : ref, b$in : ref, maybe$in : bool) {
  var b : ref where $IsNotNull(b, B);
  var maybe : bool where true;
  var stack0o : ref;
  var o : ref where $Is(o, System.Object);
  var stack0b : bool;
  var stack1o : ref;
  var isString : bool where true;
  entry: assume $IsNotNull(this, Types); goto $$entry~c;
  $$entry~c: assume ($Heap[this, $allocated] == true); goto $$entry~b;
  $$entry~b: b := b$in; goto $$entry~a;
  $$entry~a: maybe := maybe$in; goto block2873;
  block2873: goto block2975;
  block2975: assert $IsNotNull(b, B); goto block3060;
  block3060: assert $IsNotNull(b, A); goto block3145;
  block3145: assert $IsNotNull(b, System.Object); goto block3230;
  block3230: assert $IsNotNull(b, J); goto block3315;
  block3315: o := b; goto $$block3315~a;
  $$block3315~a: assert (o == b); goto block3400;
  block3400: stack0b := maybe; goto true3400to3621, false3400to3417;
  true3400to3621: assume !stack0b; goto block3621;
  false3400to3417: assume stack0b; goto block3417;
  block3621: stack0o := $As(o, System.String); goto $$block3621~a;
  $$block3621~a: stack1o := null; goto true3621to3655, false3621to3638;
  block3417: assert !$IsNotNull(o, System.String); goto block3604;
  true3621to3655: assume (stack0o != stack1o); goto block3655;
  false3621to3638: assume (stack0o == stack1o); goto block3638;
  block3655: stack0b := true; goto block3672;
  block3638: stack0b := false; goto block3672;
  block3604: goto block3825;
  block3825: return;
  block3672: isString := stack0b; goto $$block3672~a;
  $$block3672~a: assert !isString; goto block3808;
  block3808: goto block3825;
  
}

axiom (System.String <: System.String);
axiom ($BaseClass(System.String) == System.Object);
axiom ((System.String <: $BaseClass(System.String)) && (AsDirectSubClass(System.String, $BaseClass(System.String)) == System.String));
axiom ($IsImmutable(System.String) && ($AsImmutable(System.String) == System.String));
axiom (System.IComparable <: System.Object);
axiom (forall $K : name :: {(System.IComparable <: $K)} ((System.IComparable <: $K) <==> ((System.IComparable == $K) || (System.Object == $K))));
axiom $IsMemberlessType(System.IComparable);
axiom (System.String <: System.IComparable);
axiom (System.ICloneable <: System.Object);
axiom (forall $K : name :: {(System.ICloneable <: $K)} ((System.ICloneable <: $K) <==> ((System.ICloneable == $K) || (System.Object == $K))));
axiom $IsMemberlessType(System.ICloneable);
axiom (System.String <: System.ICloneable);
axiom (System.IConvertible <: System.Object);
axiom (forall $K : name :: {(System.IConvertible <: $K)} ((System.IConvertible <: $K) <==> ((System.IConvertible == $K) || (System.Object == $K))));
axiom $IsMemberlessType(System.IConvertible);
axiom (System.String <: System.IConvertible);
axiom (System.IComparable`1...System.String <: System.Object);
axiom (forall $K : name :: {(System.IComparable`1...System.String <: $K)} ((System.IComparable`1...System.String <: $K) <==> ((System.IComparable`1...System.String == $K) || (System.Object == $K))));
axiom $IsMemberlessType(System.IComparable`1...System.String);
axiom (System.String <: System.IComparable`1...System.String);
axiom (System.Collections.Generic.IEnumerable`1...System.Char <: System.Object);
axiom (System.Collections.IEnumerable <: System.Object);
axiom (forall $K : name :: {(System.Collections.IEnumerable <: $K)} ((System.Collections.IEnumerable <: $K) <==> ((System.Collections.IEnumerable == $K) || (System.Object == $K))));
axiom $IsMemberlessType(System.Collections.IEnumerable);
axiom (System.Collections.Generic.IEnumerable`1...System.Char <: System.Collections.IEnumerable);
axiom (forall $K : name :: {(System.Collections.Generic.IEnumerable`1...System.Char <: $K)} ((System.Collections.Generic.IEnumerable`1...System.Char <: $K) <==> (((System.Collections.Generic.IEnumerable`1...System.Char == $K) || (System.Object == $K)) || (System.Collections.IEnumerable <: $K))));
axiom $IsMemberlessType(System.Collections.Generic.IEnumerable`1...System.Char);
axiom (System.String <: System.Collections.Generic.IEnumerable`1...System.Char);
axiom (System.String <: System.Collections.IEnumerable);
axiom (System.IEquatable`1...System.String <: System.Object);
axiom (forall $K : name :: {(System.IEquatable`1...System.String <: $K)} ((System.IEquatable`1...System.String <: $K) <==> ((System.IEquatable`1...System.String == $K) || (System.Object == $K))));
axiom $IsMemberlessType(System.IEquatable`1...System.String);
axiom (System.String <: System.IEquatable`1...System.String);
axiom (forall $K : name :: {(System.String <: $K)} ((System.String <: $K) <==> (((((((((System.String == $K) || (System.Object <: $K)) || (System.IComparable <: $K)) || (System.ICloneable <: $K)) || (System.IConvertible <: $K)) || (System.IComparable`1...System.String <: $K)) || (System.Collections.Generic.IEnumerable`1...System.Char <: $K)) || (System.Collections.IEnumerable <: $K)) || (System.IEquatable`1...System.String <: $K))));
axiom (forall $U : name :: {($U <: System.String)} (($U <: System.String) ==> ($U == System.String)));
procedure Types.Px0$System.Object(this : ref, t$in : ref where $Is(t$in, System.Object));
  free requires ($Heap[t$in, $allocated] == true);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires ((t$in == null) || (((($Heap[t$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[t$in, $ownerRef], $inv] <: $Heap[t$in, $ownerFrame])) || ($Heap[$Heap[t$in, $ownerRef], $localinv] == $BaseClass($Heap[t$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[t$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[t$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Types.Px0$System.Object(this : ref, t$in : ref) {
  var t : ref where $Is(t, System.Object);
  var stack0o : ref;
  entry: assume $IsNotNull(this, Types); goto $$entry~e;
  $$entry~e: assume ($Heap[this, $allocated] == true); goto $$entry~d;
  $$entry~d: t := t$in; goto block5049;
  block5049: goto block5066;
  block5066: assume $IsNotNull(t, Types); goto block5151;
  block5151: assert (t != null); goto block5236;
  block5236: return;
  
}

procedure Types.Px1$System.Object(this : ref, t$in : ref where $Is(t$in, System.Object));
  free requires ($Heap[t$in, $allocated] == true);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires ((t$in == null) || (((($Heap[t$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[t$in, $ownerRef], $inv] <: $Heap[t$in, $ownerFrame])) || ($Heap[$Heap[t$in, $ownerRef], $localinv] == $BaseClass($Heap[t$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[t$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[t$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Types.Px1$System.Object(this : ref, t$in : ref) {
  var t : ref where $Is(t, System.Object);
  var stack0o : ref;
  var stack0b : bool;
  entry: assume $IsNotNull(this, Types); goto $$entry~g;
  $$entry~g: assume ($Heap[this, $allocated] == true); goto $$entry~f;
  $$entry~f: t := t$in; goto block5678;
  block5678: goto block5695;
  block5695: stack0o := $As(t, Types); goto true5695to5814, false5695to5712;
  true5695to5814: assume (stack0o == null); goto block5814;
  false5695to5712: assume (stack0o != null); goto block5712;
  block5814: return;
  block5712: assert (t != null); goto block5797;
  block5797: goto block5814;
  
}

procedure Types.Px2$System.Object(this : ref, t$in : ref where $Is(t$in, System.Object));
  free requires ($Heap[t$in, $allocated] == true);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires ((t$in == null) || (((($Heap[t$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[t$in, $ownerRef], $inv] <: $Heap[t$in, $ownerFrame])) || ($Heap[$Heap[t$in, $ownerRef], $localinv] == $BaseClass($Heap[t$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[t$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[t$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Types.Px2$System.Object(this : ref, t$in : ref) {
  var t : ref where $Is(t, System.Object);
  var stack0o : ref;
  var stack1o : ref;
  var stack0b : bool;
  var b : bool where true;
  entry: assume $IsNotNull(this, Types); goto $$entry~i;
  $$entry~i: assume ($Heap[this, $allocated] == true); goto $$entry~h;
  $$entry~h: t := t$in; goto block6273;
  block6273: goto block6290;
  block6290: stack0o := $As(t, Types); goto $$block6290~a;
  $$block6290~a: stack1o := null; goto true6290to6324, false6290to6307;
  true6290to6324: assume (stack0o != stack1o); goto block6324;
  false6290to6307: assume (stack0o == stack1o); goto block6307;
  block6324: stack0b := true; goto block6341;
  block6307: stack0b := false; goto block6341;
  block6341: b := stack0b; goto $$block6341~a;
  $$block6341~a: stack0b := b; goto true6341to6460, false6341to6358;
  true6341to6460: assume !stack0b; goto block6460;
  false6341to6358: assume stack0b; goto block6358;
  block6460: return;
  block6358: assert (t != null); goto block6443;
  block6443: goto block6460;
  
}

procedure Types.M1$B(this : ref, b$in : ref where $Is(b$in, B));
  free requires ($Heap[b$in, $allocated] == true);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires ((b$in == null) || (((($Heap[b$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[b$in, $ownerRef], $inv] <: $Heap[b$in, $ownerFrame])) || ($Heap[$Heap[b$in, $ownerRef], $localinv] == $BaseClass($Heap[b$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[b$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[b$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Types.M1$B(this : ref, b$in : ref) {
  var b : ref where $Is(b, B);
  var stack0o : ref;
  var stack0b : bool;
  var c : ref where $Is(c, C);
  entry: assume $IsNotNull(this, Types); goto $$entry~k;
  $$entry~k: assume ($Heap[this, $allocated] == true); goto $$entry~j;
  $$entry~j: b := b$in; goto block7089;
  block7089: goto block7106;
  block7106: stack0o := $As(b, C); goto true7106to7310, false7106to7123;
  true7106to7310: assume (stack0o == null); goto block7310;
  false7106to7123: assume (stack0o != null); goto block7123;
  block7310: return;
  block7123: assert (b != null); goto block7208;
  block7208: assert $Is(b, C); goto $$block7208~c;
  $$block7208~c: stack0o := b; goto $$block7208~b;
  $$block7208~b: c := stack0o; goto $$block7208~a;
  $$block7208~a: assert (b == c); goto block7293;
  block7293: goto block7310;
  
}

axiom (C <: C);
axiom ($BaseClass(C) == B);
axiom ((C <: $BaseClass(C)) && (AsDirectSubClass(C, $BaseClass(C)) == C));
axiom (!$IsImmutable(C) && ($AsMutable(C) == C));
axiom (forall $K : name :: {(C <: $K)} ((C <: $K) <==> ((C == $K) || (B <: $K))));
procedure Types.M2$B(this : ref, b$in : ref where $Is(b$in, B));
  free requires ($Heap[b$in, $allocated] == true);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires ((b$in == null) || (((($Heap[b$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[b$in, $ownerRef], $inv] <: $Heap[b$in, $ownerFrame])) || ($Heap[$Heap[b$in, $ownerRef], $localinv] == $BaseClass($Heap[b$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[b$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[b$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Types.M2$B(this : ref, b$in : ref) {
  var b : ref where $Is(b, B);
  var stack0o : ref;
  var c : ref where $Is(c, C);
  var stack0b : bool;
  entry: assume $IsNotNull(this, Types); goto $$entry~m;
  $$entry~m: assume ($Heap[this, $allocated] == true); goto $$entry~l;
  $$entry~l: b := b$in; goto block7922;
  block7922: goto block7939;
  block7939: stack0o := $As(b, C); goto $$block7939~b;
  $$block7939~b: c := stack0o; goto $$block7939~a;
  $$block7939~a: stack0o := null; goto true7939to8143, false7939to7956;
  true7939to8143: assume (c == stack0o); goto block8143;
  false7939to7956: assume (c != stack0o); goto block7956;
  block8143: return;
  block7956: assert $IsNotNull(b, C); goto block8041;
  block8041: assert (b == c); goto block8126;
  block8126: goto block8143;
  
}

procedure Types.M3$B(this : ref, b$in : ref where $Is(b$in, B));
  free requires ($Heap[b$in, $allocated] == true);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires ((b$in == null) || (((($Heap[b$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[b$in, $ownerRef], $inv] <: $Heap[b$in, $ownerFrame])) || ($Heap[$Heap[b$in, $ownerRef], $localinv] == $BaseClass($Heap[b$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[b$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[b$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Types.M3$B(this : ref, b$in : ref) {
  var b : ref where $Is(b, B);
  var stack0o : ref;
  var bb : ref where $Is(bb, B);
  entry: assume $IsNotNull(this, Types); goto $$entry~o;
  $$entry~o: assume ($Heap[this, $allocated] == true); goto $$entry~n;
  $$entry~n: b := b$in; goto block9061;
  block9061: goto block9078;
  block9078: goto true9078to9197, false9078to9095;
  true9078to9197: assume ($As(b, B) != null); goto block9197;
  false9078to9095: assume ($As(b, B) == null); goto block9095;
  block9197: stack0o := b; goto $$block9197~c;
  $$block9197~c: assert (stack0o != null); goto $$block9197~b;
  $$block9197~b: bb := stack0o; goto $$block9197~a;
  $$block9197~a: assert (bb == b); goto block9282;
  block9095: assert (b == null); goto block9180;
  block9180: goto block9299;
  block9282: goto block9299;
  block9299: return;
  
}

procedure Types.M4$System.Object(this : ref, o$in : ref where $Is(o$in, System.Object));
  free requires ($Heap[o$in, $allocated] == true);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires ((o$in == null) || (((($Heap[o$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[o$in, $ownerRef], $inv] <: $Heap[o$in, $ownerFrame])) || ($Heap[$Heap[o$in, $ownerRef], $localinv] == $BaseClass($Heap[o$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[o$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[o$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Types.M4$System.Object(this : ref, o$in : ref) {
  var o : ref where $Is(o, System.Object);
  var stack0o : ref;
  entry: assume $IsNotNull(this, Types); goto $$entry~q;
  $$entry~q: assume ($Heap[this, $allocated] == true); goto $$entry~p;
  $$entry~p: o := o$in; goto block10047;
  block10047: goto block10064;
  block10064: assert ($IsNotNull(o, D) == $IsNotNull(o, D)); goto block10251;
  block10251: assert ($As(o, A) == $As(o, A)); goto block10336;
  block10336: assert ($As(o, C) == $As(o, C)); goto block10421;
  block10421: return;
  
}

axiom (D <: D);
axiom ($BaseClass(D) == A);
axiom ((D <: $BaseClass(D)) && (AsDirectSubClass(D, $BaseClass(D)) == D));
axiom (!$IsImmutable(D) && ($AsMutable(D) == D));
axiom (forall $K : name :: {(D <: $K)} ((D <: $K) <==> ((D == $K) || (A <: $K))));
procedure Types.N0$C$D(this : ref, c$in : ref where $Is(c$in, C), d$in : ref where $Is(d$in, D));
  free requires ($Heap[c$in, $allocated] == true);
  free requires ($Heap[d$in, $allocated] == true);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires ((c$in == null) || (((($Heap[c$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[c$in, $ownerRef], $inv] <: $Heap[c$in, $ownerFrame])) || ($Heap[$Heap[c$in, $ownerRef], $localinv] == $BaseClass($Heap[c$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[c$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[c$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))));
  requires ((d$in == null) || (((($Heap[d$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[d$in, $ownerRef], $inv] <: $Heap[d$in, $ownerFrame])) || ($Heap[$Heap[d$in, $ownerRef], $localinv] == $BaseClass($Heap[d$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[d$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[d$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Types.N0$C$D(this : ref, c$in : ref, d$in : ref) {
  var c : ref where $Is(c, C);
  var d : ref where $Is(d, D);
  var cc : ref where $Is(cc, System.Object);
  var dd : ref where $Is(dd, System.Object);
  var stack0o : ref;
  var stack0b : bool;
  entry: assume $IsNotNull(this, Types); goto $$entry~t;
  $$entry~t: assume ($Heap[this, $allocated] == true); goto $$entry~s;
  $$entry~s: c := c$in; goto $$entry~r;
  $$entry~r: d := d$in; goto block11237;
  block11237: goto block11254;
  block11254: cc := c; goto $$block11254~b;
  $$block11254~b: dd := d; goto $$block11254~a;
  $$block11254~a: assert ((cc == c) && (dd == d)); goto block11373;
  block11373: stack0o := null; goto true11373to11492, false11373to11390;
  true11373to11492: assume (c == stack0o); goto block11492;
  false11373to11390: assume (c != stack0o); goto block11390;
  block11492: stack0o := null; goto true11492to11611, false11492to11509;
  block11390: assert (cc != dd); goto block11475;
  true11492to11611: assume (d == stack0o); goto block11611;
  false11492to11509: assume (d != stack0o); goto block11509;
  block11611: goto block11628;
  block11509: assert (cc != dd); goto block11594;
  block11475: goto block11628;
  block11628: return;
  block11594: goto block11611;
  
}

procedure Types.N1$C$D(this : ref, c$in : ref where $Is(c$in, C), d$in : ref where $Is(d$in, D));
  free requires ($Heap[c$in, $allocated] == true);
  free requires ($Heap[d$in, $allocated] == true);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires ((c$in == null) || (((($Heap[c$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[c$in, $ownerRef], $inv] <: $Heap[c$in, $ownerFrame])) || ($Heap[$Heap[c$in, $ownerRef], $localinv] == $BaseClass($Heap[c$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[c$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[c$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))));
  requires ((d$in == null) || (((($Heap[d$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[d$in, $ownerRef], $inv] <: $Heap[d$in, $ownerFrame])) || ($Heap[$Heap[d$in, $ownerRef], $localinv] == $BaseClass($Heap[d$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[d$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[d$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Types.N1$C$D(this : ref, c$in : ref, d$in : ref) {
  var c : ref where $Is(c, C);
  var d : ref where $Is(d, D);
  var stack0o : ref;
  entry: assume $IsNotNull(this, Types); goto $$entry~w;
  $$entry~w: assume ($Heap[this, $allocated] == true); goto $$entry~v;
  $$entry~v: c := c$in; goto $$entry~u;
  $$entry~u: d := d$in; goto block12257;
  block12257: goto block12274;
  block12274: assert (c != d); goto block12359;
  block12359: return;
  
}

axiom (K <: System.Object);
axiom (K <: J);
axiom (forall $K : name :: {(K <: $K)} ((K <: $K) <==> (((K == $K) || (System.Object == $K)) || (J <: $K))));
axiom $IsMemberlessType(K);
procedure Types.P0$K$notnull(this : ref, k$in : ref where $IsNotNull(k$in, K));
  free requires ($Heap[k$in, $allocated] == true);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[k$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[k$in, $ownerRef], $inv] <: $Heap[k$in, $ownerFrame])) || ($Heap[$Heap[k$in, $ownerRef], $localinv] == $BaseClass($Heap[k$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[k$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[k$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Types.P0$K$notnull(this : ref, k$in : ref) {
  var k : ref where $IsNotNull(k, K);
  var stack0o : ref;
  var ok : ref where $Is(ok, System.Object);
  entry: assume $IsNotNull(this, Types); goto $$entry~y;
  $$entry~y: assume ($Heap[this, $allocated] == true); goto $$entry~x;
  $$entry~x: k := k$in; goto block13226;
  block13226: goto block13328;
  block13328: assert $IsNotNull(k, J); goto block13413;
  block13413: assert $IsNotNull(k, System.Object); goto block13498;
  block13498: ok := k; goto $$block13498~a;
  $$block13498~a: assert !$IsNotNull(ok, F); goto block13685;
  block13685: assert !$IsNotNull(ok, ValueArray(System.Int32, 1)); goto block13872;
  block13872: return;
  
}

axiom (F <: F);
axiom ($BaseClass(F) == A);
axiom ((F <: $BaseClass(F)) && (AsDirectSubClass(F, $BaseClass(F)) == F));
axiom (!$IsImmutable(F) && ($AsMutable(F) == F));
axiom (forall $K : name :: {(F <: $K)} ((F <: $K) <==> ((F == $K) || (A <: $K))));
axiom (forall $U : name :: {($U <: F)} (($U <: F) ==> ($U == F)));
procedure Types.P1$K$notnull(this : ref, k$in : ref where $IsNotNull(k$in, K));
  free requires ($Heap[k$in, $allocated] == true);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[k$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[k$in, $ownerRef], $inv] <: $Heap[k$in, $ownerFrame])) || ($Heap[$Heap[k$in, $ownerRef], $localinv] == $BaseClass($Heap[k$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[k$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[k$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Types.P1$K$notnull(this : ref, k$in : ref) {
  var k : ref where $IsNotNull(k, K);
  var ok : ref where $Is(ok, System.Object);
  var stack0o : ref;
  entry: assume $IsNotNull(this, Types); goto $$entry~aa;
  $$entry~aa: assume ($Heap[this, $allocated] == true); goto $$entry~z;
  $$entry~z: k := k$in; goto block14773;
  block14773: goto block14875;
  block14875: ok := k; goto $$block14875~a;
  $$block14875~a: assert !$IsNotNull(ok, A); goto block15062;
  block15062: return;
  
}

procedure Types.P2$K$notnull(this : ref, k$in : ref where $IsNotNull(k$in, K));
  free requires ($Heap[k$in, $allocated] == true);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[k$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[k$in, $ownerRef], $inv] <: $Heap[k$in, $ownerFrame])) || ($Heap[$Heap[k$in, $ownerRef], $localinv] == $BaseClass($Heap[k$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[k$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[k$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Types.P2$K$notnull(this : ref, k$in : ref) {
  var k : ref where $IsNotNull(k, K);
  var stack0o : ref;
  entry: assume $IsNotNull(this, Types); goto $$entry~ac;
  $$entry~ac: assume ($Heap[this, $allocated] == true); goto $$entry~ab;
  $$entry~ab: k := k$in; goto block15674;
  block15674: goto block15776;
  block15776: assert !$IsNotNull(k, L); goto block15963;
  block15963: return;
  
}

axiom (L <: System.Object);
axiom (forall $K : name :: {(L <: $K)} ((L <: $K) <==> ((L == $K) || (System.Object == $K))));
axiom $IsMemberlessType(L);
procedure Types.P3$K$notnull(this : ref, k$in : ref where $IsNotNull(k$in, K));
  free requires ($Heap[k$in, $allocated] == true);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[k$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[k$in, $ownerRef], $inv] <: $Heap[k$in, $ownerFrame])) || ($Heap[$Heap[k$in, $ownerRef], $localinv] == $BaseClass($Heap[k$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[k$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[k$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Types.P3$K$notnull(this : ref, k$in : ref) {
  var k : ref where $IsNotNull(k, K);
  var ok : ref where $Is(ok, System.Object);
  var stack0o : ref;
  entry: assume $IsNotNull(this, Types); goto $$entry~ae;
  $$entry~ae: assume ($Heap[this, $allocated] == true); goto $$entry~ad;
  $$entry~ad: k := k$in; goto block16558;
  block16558: goto block16660;
  block16660: ok := k; goto $$block16660~a;
  $$block16660~a: assert !$IsNotNull(ok, System.Array); goto block16847;
  block16847: return;
  
}

axiom (System.Array <: System.Array);
axiom ($BaseClass(System.Array) == System.Object);
axiom ((System.Array <: $BaseClass(System.Array)) && (AsDirectSubClass(System.Array, $BaseClass(System.Array)) == System.Array));
axiom (!$IsImmutable(System.Array) && ($AsMutable(System.Array) == System.Array));
axiom (System.Array <: System.ICloneable);
axiom (System.Collections.IList <: System.Object);
axiom (System.Collections.ICollection <: System.Object);
axiom (System.Collections.ICollection <: System.Collections.IEnumerable);
axiom (forall $K : name :: {(System.Collections.ICollection <: $K)} ((System.Collections.ICollection <: $K) <==> (((System.Collections.ICollection == $K) || (System.Object == $K)) || (System.Collections.IEnumerable <: $K))));
axiom $IsMemberlessType(System.Collections.ICollection);
axiom (System.Collections.IList <: System.Collections.ICollection);
axiom (System.Collections.IList <: System.Collections.IEnumerable);
axiom (forall $K : name :: {(System.Collections.IList <: $K)} ((System.Collections.IList <: $K) <==> ((((System.Collections.IList == $K) || (System.Object == $K)) || (System.Collections.ICollection <: $K)) || (System.Collections.IEnumerable <: $K))));
axiom $IsMemberlessType(System.Collections.IList);
axiom (System.Array <: System.Collections.IList);
axiom (System.Array <: System.Collections.ICollection);
axiom (System.Array <: System.Collections.IEnumerable);
axiom (forall $K : name :: {(System.Array <: $K)} ((System.Array <: $K) <==> ((((((System.Array == $K) || (System.Object <: $K)) || (System.ICloneable <: $K)) || (System.Collections.IList <: $K)) || (System.Collections.ICollection <: $K)) || (System.Collections.IEnumerable <: $K))));
axiom $IsMemberlessType(System.Array);
procedure Types.P4$System.Object.array$notnull$System.Int32.array$notnull$A.array$notnull$J.array$notnull$B.array$notnull(this : ref, aObject$in : ref where $IsNotNull(aObject$in, RefArray(System.Object, 1)), aInt$in : ref where $IsNotNull(aInt$in, ValueArray(System.Int32, 1)), aA$in : ref where $IsNotNull(aA$in, RefArray(A, 1)), aJ$in : ref where $IsNotNull(aJ$in, RefArray(J, 1)), aB$in : ref where $IsNotNull(aB$in, RefArray(B, 1)));
  free requires ($Heap[aObject$in, $allocated] == true);
  free requires ($Heap[aInt$in, $allocated] == true);
  free requires ($Heap[aA$in, $allocated] == true);
  free requires ($Heap[aJ$in, $allocated] == true);
  free requires ($Heap[aB$in, $allocated] == true);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[aObject$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[aObject$in, $ownerRef], $inv] <: $Heap[aObject$in, $ownerFrame])) || ($Heap[$Heap[aObject$in, $ownerRef], $localinv] == $BaseClass($Heap[aObject$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[aObject$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[aObject$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[aInt$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[aInt$in, $ownerRef], $inv] <: $Heap[aInt$in, $ownerFrame])) || ($Heap[$Heap[aInt$in, $ownerRef], $localinv] == $BaseClass($Heap[aInt$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[aInt$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[aInt$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[aA$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[aA$in, $ownerRef], $inv] <: $Heap[aA$in, $ownerFrame])) || ($Heap[$Heap[aA$in, $ownerRef], $localinv] == $BaseClass($Heap[aA$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[aA$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[aA$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[aJ$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[aJ$in, $ownerRef], $inv] <: $Heap[aJ$in, $ownerFrame])) || ($Heap[$Heap[aJ$in, $ownerRef], $localinv] == $BaseClass($Heap[aJ$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[aJ$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[aJ$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[aB$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[aB$in, $ownerRef], $inv] <: $Heap[aB$in, $ownerFrame])) || ($Heap[$Heap[aB$in, $ownerRef], $localinv] == $BaseClass($Heap[aB$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[aB$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[aB$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Types.P4$System.Object.array$notnull$System.Int32.array$notnull$A.array$notnull$J.array$notnull$B.array$notnull(this : ref, aObject$in : ref, aInt$in : ref, aA$in : ref, aJ$in : ref, aB$in : ref) {
  var aObject : ref where $IsNotNull(aObject, RefArray(System.Object, 1));
  var aInt : ref where $IsNotNull(aInt, ValueArray(System.Int32, 1));
  var aA : ref where $IsNotNull(aA, RefArray(A, 1));
  var aJ : ref where $IsNotNull(aJ, RefArray(J, 1));
  var aB : ref where $IsNotNull(aB, RefArray(B, 1));
  var o : ref where $Is(o, System.Object);
  var p : ref where $Is(p, System.Object);
  var stack0o : ref;
  entry: assume $IsNotNull(this, Types); goto $$entry~ak;
  $$entry~ak: assume ($Heap[this, $allocated] == true); goto $$entry~aj;
  $$entry~aj: aObject := aObject$in; goto $$entry~ai;
  $$entry~ai: aInt := aInt$in; goto $$entry~ah;
  $$entry~ah: aA := aA$in; goto $$entry~ag;
  $$entry~ag: aJ := aJ$in; goto $$entry~af;
  $$entry~af: aB := aB$in; goto block18496;
  block18496: goto block18802;
  block18802: o := aInt; goto $$block18802~b;
  $$block18802~b: p := aObject; goto $$block18802~a;
  $$block18802~a: assert (o != p); goto block18887;
  block18887: assert (aInt != aObject); goto block18972;
  block18972: assert (aInt != aObject); goto block19057;
  block19057: assert (aInt != aObject); goto block19142;
  block19142: assert (aInt == aInt); goto block19227;
  block19227: assert (aInt != aJ); goto block19312;
  block19312: assert (aInt != aA); goto block19397;
  block19397: assert (aInt != aB); goto block19482;
  block19482: o := aB; goto $$block19482~a;
  $$block19482~a: assert $IsNotNull(o, RefArray(A, 1)); goto block19567;
  block19567: assert $IsNotNull(o, RefArray(J, 1)); goto block19652;
  block19652: assert $IsNotNull(o, RefArray(System.Object, 1)); goto block19737;
  block19737: assert $IsNotNull(o, RefArray(System.Object, 1)); goto block19822;
  block19822: return;
  
}

procedure Types.P5$System.Object.array$notnull$System.Int32.array$notnull$A.array$notnull$J.array$notnull$B.array$notnull(this : ref, aObject$in : ref where $IsNotNull(aObject$in, RefArray(System.Object, 1)), aInt$in : ref where $IsNotNull(aInt$in, ValueArray(System.Int32, 1)), aA$in : ref where $IsNotNull(aA$in, RefArray(A, 1)), aJ$in : ref where $IsNotNull(aJ$in, RefArray(J, 1)), aB$in : ref where $IsNotNull(aB$in, RefArray(B, 1)));
  free requires ($Heap[aObject$in, $allocated] == true);
  free requires ($Heap[aInt$in, $allocated] == true);
  free requires ($Heap[aA$in, $allocated] == true);
  free requires ($Heap[aJ$in, $allocated] == true);
  free requires ($Heap[aB$in, $allocated] == true);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[aObject$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[aObject$in, $ownerRef], $inv] <: $Heap[aObject$in, $ownerFrame])) || ($Heap[$Heap[aObject$in, $ownerRef], $localinv] == $BaseClass($Heap[aObject$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[aObject$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[aObject$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[aInt$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[aInt$in, $ownerRef], $inv] <: $Heap[aInt$in, $ownerFrame])) || ($Heap[$Heap[aInt$in, $ownerRef], $localinv] == $BaseClass($Heap[aInt$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[aInt$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[aInt$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[aA$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[aA$in, $ownerRef], $inv] <: $Heap[aA$in, $ownerFrame])) || ($Heap[$Heap[aA$in, $ownerRef], $localinv] == $BaseClass($Heap[aA$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[aA$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[aA$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[aJ$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[aJ$in, $ownerRef], $inv] <: $Heap[aJ$in, $ownerFrame])) || ($Heap[$Heap[aJ$in, $ownerRef], $localinv] == $BaseClass($Heap[aJ$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[aJ$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[aJ$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[aB$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[aB$in, $ownerRef], $inv] <: $Heap[aB$in, $ownerFrame])) || ($Heap[$Heap[aB$in, $ownerRef], $localinv] == $BaseClass($Heap[aB$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[aB$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[aB$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Types.P5$System.Object.array$notnull$System.Int32.array$notnull$A.array$notnull$J.array$notnull$B.array$notnull(this : ref, aObject$in : ref, aInt$in : ref, aA$in : ref, aJ$in : ref, aB$in : ref) {
  var aObject : ref where $IsNotNull(aObject, RefArray(System.Object, 1));
  var aInt : ref where $IsNotNull(aInt, ValueArray(System.Int32, 1));
  var aA : ref where $IsNotNull(aA, RefArray(A, 1));
  var aJ : ref where $IsNotNull(aJ, RefArray(J, 1));
  var aB : ref where $IsNotNull(aB, RefArray(B, 1));
  var stack0o : ref;
  entry: assume $IsNotNull(this, Types); goto $$entry~aq;
  $$entry~aq: assume ($Heap[this, $allocated] == true); goto $$entry~ap;
  $$entry~ap: aObject := aObject$in; goto $$entry~ao;
  $$entry~ao: aInt := aInt$in; goto $$entry~an;
  $$entry~an: aA := aA$in; goto $$entry~am;
  $$entry~am: aJ := aJ$in; goto $$entry~al;
  $$entry~al: aB := aB$in; goto block21471;
  block21471: goto block21777;
  block21777: assert (aA != aJ); goto block21862;
  block21862: return;
  
}

procedure Types.P6$System.Object.array$notnull$System.Int32.array$notnull$A.array$notnull$J.array$notnull$B.array$notnull(this : ref, aObject$in : ref where $IsNotNull(aObject$in, RefArray(System.Object, 1)), aInt$in : ref where $IsNotNull(aInt$in, ValueArray(System.Int32, 1)), aA$in : ref where $IsNotNull(aA$in, RefArray(A, 1)), aJ$in : ref where $IsNotNull(aJ$in, RefArray(J, 1)), aB$in : ref where $IsNotNull(aB$in, RefArray(B, 1)));
  free requires ($Heap[aObject$in, $allocated] == true);
  free requires ($Heap[aInt$in, $allocated] == true);
  free requires ($Heap[aA$in, $allocated] == true);
  free requires ($Heap[aJ$in, $allocated] == true);
  free requires ($Heap[aB$in, $allocated] == true);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[aObject$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[aObject$in, $ownerRef], $inv] <: $Heap[aObject$in, $ownerFrame])) || ($Heap[$Heap[aObject$in, $ownerRef], $localinv] == $BaseClass($Heap[aObject$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[aObject$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[aObject$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[aInt$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[aInt$in, $ownerRef], $inv] <: $Heap[aInt$in, $ownerFrame])) || ($Heap[$Heap[aInt$in, $ownerRef], $localinv] == $BaseClass($Heap[aInt$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[aInt$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[aInt$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[aA$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[aA$in, $ownerRef], $inv] <: $Heap[aA$in, $ownerFrame])) || ($Heap[$Heap[aA$in, $ownerRef], $localinv] == $BaseClass($Heap[aA$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[aA$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[aA$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[aJ$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[aJ$in, $ownerRef], $inv] <: $Heap[aJ$in, $ownerFrame])) || ($Heap[$Heap[aJ$in, $ownerRef], $localinv] == $BaseClass($Heap[aJ$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[aJ$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[aJ$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[aB$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[aB$in, $ownerRef], $inv] <: $Heap[aB$in, $ownerFrame])) || ($Heap[$Heap[aB$in, $ownerRef], $localinv] == $BaseClass($Heap[aB$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[aB$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[aB$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Types.P6$System.Object.array$notnull$System.Int32.array$notnull$A.array$notnull$J.array$notnull$B.array$notnull(this : ref, aObject$in : ref, aInt$in : ref, aA$in : ref, aJ$in : ref, aB$in : ref) {
  var aObject : ref where $IsNotNull(aObject, RefArray(System.Object, 1));
  var aInt : ref where $IsNotNull(aInt, ValueArray(System.Int32, 1));
  var aA : ref where $IsNotNull(aA, RefArray(A, 1));
  var aJ : ref where $IsNotNull(aJ, RefArray(J, 1));
  var aB : ref where $IsNotNull(aB, RefArray(B, 1));
  var stack0o : ref;
  entry: assume $IsNotNull(this, Types); goto $$entry~aw;
  $$entry~aw: assume ($Heap[this, $allocated] == true); goto $$entry~av;
  $$entry~av: aObject := aObject$in; goto $$entry~au;
  $$entry~au: aInt := aInt$in; goto $$entry~at;
  $$entry~at: aA := aA$in; goto $$entry~as;
  $$entry~as: aJ := aJ$in; goto $$entry~ar;
  $$entry~ar: aB := aB$in; goto block22525;
  block22525: goto block22831;
  block22831: assert (aB != aJ); goto block22916;
  block22916: return;
  
}

procedure Types.P7$System.Object.array$notnull$System.Int32.array$notnull$A.array$notnull$J.array$notnull$B.array$notnull(this : ref, aObject$in : ref where $IsNotNull(aObject$in, RefArray(System.Object, 1)), aInt$in : ref where $IsNotNull(aInt$in, ValueArray(System.Int32, 1)), aA$in : ref where $IsNotNull(aA$in, RefArray(A, 1)), aJ$in : ref where $IsNotNull(aJ$in, RefArray(J, 1)), aB$in : ref where $IsNotNull(aB$in, RefArray(B, 1)));
  free requires ($Heap[aObject$in, $allocated] == true);
  free requires ($Heap[aInt$in, $allocated] == true);
  free requires ($Heap[aA$in, $allocated] == true);
  free requires ($Heap[aJ$in, $allocated] == true);
  free requires ($Heap[aB$in, $allocated] == true);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[aObject$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[aObject$in, $ownerRef], $inv] <: $Heap[aObject$in, $ownerFrame])) || ($Heap[$Heap[aObject$in, $ownerRef], $localinv] == $BaseClass($Heap[aObject$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[aObject$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[aObject$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[aInt$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[aInt$in, $ownerRef], $inv] <: $Heap[aInt$in, $ownerFrame])) || ($Heap[$Heap[aInt$in, $ownerRef], $localinv] == $BaseClass($Heap[aInt$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[aInt$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[aInt$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[aA$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[aA$in, $ownerRef], $inv] <: $Heap[aA$in, $ownerFrame])) || ($Heap[$Heap[aA$in, $ownerRef], $localinv] == $BaseClass($Heap[aA$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[aA$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[aA$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[aJ$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[aJ$in, $ownerRef], $inv] <: $Heap[aJ$in, $ownerFrame])) || ($Heap[$Heap[aJ$in, $ownerRef], $localinv] == $BaseClass($Heap[aJ$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[aJ$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[aJ$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[aB$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[aB$in, $ownerRef], $inv] <: $Heap[aB$in, $ownerFrame])) || ($Heap[$Heap[aB$in, $ownerRef], $localinv] == $BaseClass($Heap[aB$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[aB$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[aB$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Types.P7$System.Object.array$notnull$System.Int32.array$notnull$A.array$notnull$J.array$notnull$B.array$notnull(this : ref, aObject$in : ref, aInt$in : ref, aA$in : ref, aJ$in : ref, aB$in : ref) {
  var aObject : ref where $IsNotNull(aObject, RefArray(System.Object, 1));
  var aInt : ref where $IsNotNull(aInt, ValueArray(System.Int32, 1));
  var aA : ref where $IsNotNull(aA, RefArray(A, 1));
  var aJ : ref where $IsNotNull(aJ, RefArray(J, 1));
  var aB : ref where $IsNotNull(aB, RefArray(B, 1));
  var stack0o : ref;
  entry: assume $IsNotNull(this, Types); goto $$entry~bc;
  $$entry~bc: assume ($Heap[this, $allocated] == true); goto $$entry~bb;
  $$entry~bb: aObject := aObject$in; goto $$entry~ba;
  $$entry~ba: aInt := aInt$in; goto $$entry~az;
  $$entry~az: aA := aA$in; goto $$entry~ay;
  $$entry~ay: aJ := aJ$in; goto $$entry~ax;
  $$entry~ax: aB := aB$in; goto block23579;
  block23579: goto block23885;
  block23885: assert (aB != aA); goto block23970;
  block23970: return;
  
}

procedure Types.P8$System.Object.array$notnull$System.Int32.array$notnull$A.array$notnull$J.array$notnull$B.array$notnull(this : ref, aObject$in : ref where $IsNotNull(aObject$in, RefArray(System.Object, 1)), aInt$in : ref where $IsNotNull(aInt$in, ValueArray(System.Int32, 1)), aA$in : ref where $IsNotNull(aA$in, RefArray(A, 1)), aJ$in : ref where $IsNotNull(aJ$in, RefArray(J, 1)), aB$in : ref where $IsNotNull(aB$in, RefArray(B, 1)));
  free requires ($Heap[aObject$in, $allocated] == true);
  free requires ($Heap[aInt$in, $allocated] == true);
  free requires ($Heap[aA$in, $allocated] == true);
  free requires ($Heap[aJ$in, $allocated] == true);
  free requires ($Heap[aB$in, $allocated] == true);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[aObject$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[aObject$in, $ownerRef], $inv] <: $Heap[aObject$in, $ownerFrame])) || ($Heap[$Heap[aObject$in, $ownerRef], $localinv] == $BaseClass($Heap[aObject$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[aObject$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[aObject$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[aInt$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[aInt$in, $ownerRef], $inv] <: $Heap[aInt$in, $ownerFrame])) || ($Heap[$Heap[aInt$in, $ownerRef], $localinv] == $BaseClass($Heap[aInt$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[aInt$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[aInt$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[aA$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[aA$in, $ownerRef], $inv] <: $Heap[aA$in, $ownerFrame])) || ($Heap[$Heap[aA$in, $ownerRef], $localinv] == $BaseClass($Heap[aA$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[aA$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[aA$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[aJ$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[aJ$in, $ownerRef], $inv] <: $Heap[aJ$in, $ownerFrame])) || ($Heap[$Heap[aJ$in, $ownerRef], $localinv] == $BaseClass($Heap[aJ$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[aJ$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[aJ$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[aB$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[aB$in, $ownerRef], $inv] <: $Heap[aB$in, $ownerFrame])) || ($Heap[$Heap[aB$in, $ownerRef], $localinv] == $BaseClass($Heap[aB$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[aB$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[aB$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Types.P8$System.Object.array$notnull$System.Int32.array$notnull$A.array$notnull$J.array$notnull$B.array$notnull(this : ref, aObject$in : ref, aInt$in : ref, aA$in : ref, aJ$in : ref, aB$in : ref) {
  var aObject : ref where $IsNotNull(aObject, RefArray(System.Object, 1));
  var aInt : ref where $IsNotNull(aInt, ValueArray(System.Int32, 1));
  var aA : ref where $IsNotNull(aA, RefArray(A, 1));
  var aJ : ref where $IsNotNull(aJ, RefArray(J, 1));
  var aB : ref where $IsNotNull(aB, RefArray(B, 1));
  var stack0o : ref;
  entry: assume $IsNotNull(this, Types); goto $$entry~bi;
  $$entry~bi: assume ($Heap[this, $allocated] == true); goto $$entry~bh;
  $$entry~bh: aObject := aObject$in; goto $$entry~bg;
  $$entry~bg: aInt := aInt$in; goto $$entry~bf;
  $$entry~bf: aA := aA$in; goto $$entry~be;
  $$entry~be: aJ := aJ$in; goto $$entry~bd;
  $$entry~bd: aB := aB$in; goto block24633;
  block24633: goto block24939;
  block24939: assert (aObject != aJ); goto block25024;
  block25024: return;
  
}

procedure Types.P9$System.Object.array$notnull$System.Int32.array$notnull$A.array$notnull$J.array$notnull$B.array$notnull(this : ref, aObject$in : ref where $IsNotNull(aObject$in, RefArray(System.Object, 1)), aInt$in : ref where $IsNotNull(aInt$in, ValueArray(System.Int32, 1)), aA$in : ref where $IsNotNull(aA$in, RefArray(A, 1)), aJ$in : ref where $IsNotNull(aJ$in, RefArray(J, 1)), aB$in : ref where $IsNotNull(aB$in, RefArray(B, 1)));
  free requires ($Heap[aObject$in, $allocated] == true);
  free requires ($Heap[aInt$in, $allocated] == true);
  free requires ($Heap[aA$in, $allocated] == true);
  free requires ($Heap[aJ$in, $allocated] == true);
  free requires ($Heap[aB$in, $allocated] == true);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[aObject$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[aObject$in, $ownerRef], $inv] <: $Heap[aObject$in, $ownerFrame])) || ($Heap[$Heap[aObject$in, $ownerRef], $localinv] == $BaseClass($Heap[aObject$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[aObject$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[aObject$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[aInt$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[aInt$in, $ownerRef], $inv] <: $Heap[aInt$in, $ownerFrame])) || ($Heap[$Heap[aInt$in, $ownerRef], $localinv] == $BaseClass($Heap[aInt$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[aInt$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[aInt$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[aA$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[aA$in, $ownerRef], $inv] <: $Heap[aA$in, $ownerFrame])) || ($Heap[$Heap[aA$in, $ownerRef], $localinv] == $BaseClass($Heap[aA$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[aA$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[aA$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[aJ$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[aJ$in, $ownerRef], $inv] <: $Heap[aJ$in, $ownerFrame])) || ($Heap[$Heap[aJ$in, $ownerRef], $localinv] == $BaseClass($Heap[aJ$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[aJ$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[aJ$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[aB$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[aB$in, $ownerRef], $inv] <: $Heap[aB$in, $ownerFrame])) || ($Heap[$Heap[aB$in, $ownerRef], $localinv] == $BaseClass($Heap[aB$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[aB$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[aB$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Types.P9$System.Object.array$notnull$System.Int32.array$notnull$A.array$notnull$J.array$notnull$B.array$notnull(this : ref, aObject$in : ref, aInt$in : ref, aA$in : ref, aJ$in : ref, aB$in : ref) {
  var aObject : ref where $IsNotNull(aObject, RefArray(System.Object, 1));
  var aInt : ref where $IsNotNull(aInt, ValueArray(System.Int32, 1));
  var aA : ref where $IsNotNull(aA, RefArray(A, 1));
  var aJ : ref where $IsNotNull(aJ, RefArray(J, 1));
  var aB : ref where $IsNotNull(aB, RefArray(B, 1));
  var stack0o : ref;
  entry: assume $IsNotNull(this, Types); goto $$entry~bo;
  $$entry~bo: assume ($Heap[this, $allocated] == true); goto $$entry~bn;
  $$entry~bn: aObject := aObject$in; goto $$entry~bm;
  $$entry~bm: aInt := aInt$in; goto $$entry~bl;
  $$entry~bl: aA := aA$in; goto $$entry~bk;
  $$entry~bk: aJ := aJ$in; goto $$entry~bj;
  $$entry~bj: aB := aB$in; goto block25687;
  block25687: goto block25993;
  block25993: assert (aObject != aB); goto block26078;
  block26078: return;
  
}

procedure Types.P10$J.array$notnull$B.array$notnull$F.array$notnull(this : ref, a$in : ref where $IsNotNull(a$in, RefArray(J, 1)), b$in : ref where $IsNotNull(b$in, RefArray(B, 1)), f$in : ref where $IsNotNull(f$in, RefArray(F, 1)));
  free requires ($Heap[a$in, $allocated] == true);
  free requires ($Heap[b$in, $allocated] == true);
  free requires ($Heap[f$in, $allocated] == true);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[a$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[a$in, $ownerRef], $inv] <: $Heap[a$in, $ownerFrame])) || ($Heap[$Heap[a$in, $ownerRef], $localinv] == $BaseClass($Heap[a$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[a$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[a$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[b$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[b$in, $ownerRef], $inv] <: $Heap[b$in, $ownerFrame])) || ($Heap[$Heap[b$in, $ownerRef], $localinv] == $BaseClass($Heap[b$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[b$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[b$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires (((($Heap[f$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[f$in, $ownerRef], $inv] <: $Heap[f$in, $ownerFrame])) || ($Heap[$Heap[f$in, $ownerRef], $localinv] == $BaseClass($Heap[f$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[f$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[f$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Types.P10$J.array$notnull$B.array$notnull$F.array$notnull(this : ref, a$in : ref, b$in : ref, f$in : ref) {
  var a : ref where $IsNotNull(a, RefArray(J, 1));
  var b : ref where $IsNotNull(b, RefArray(B, 1));
  var f : ref where $IsNotNull(f, RefArray(F, 1));
  var o : ref where $Is(o, System.Object);
  var stack0o : ref;
  entry: assume $IsNotNull(this, Types); goto $$entry~bs;
  $$entry~bs: assume ($Heap[this, $allocated] == true); goto $$entry~br;
  $$entry~br: a := a$in; goto $$entry~bq;
  $$entry~bq: b := b$in; goto $$entry~bp;
  $$entry~bp: f := f$in; goto block27098;
  block27098: goto block27302;
  block27302: o := a; goto $$block27302~a;
  $$block27302~a: assert !$IsNotNull(o, RefArray(F, 1)); goto block27489;
  block27489: o := b; goto $$block27489~a;
  $$block27489~a: assert !$IsNotNull(o, RefArray(F, 1)); goto block27676;
  block27676: assert (a != f); goto block27761;
  block27761: assert (b != f); goto block27846;
  block27846: return;
  
}

axiom (T <: T);
axiom ($BaseClass(T) == System.Object);
axiom ((T <: $BaseClass(T)) && (AsDirectSubClass(T, $BaseClass(T)) == T));
axiom (!$IsImmutable(T) && ($AsMutable(T) == T));
axiom (forall $K : name :: {(T <: $K)} ((T <: $K) <==> ((T == $K) || (System.Object <: $K))));
procedure Types.Q$T$T(this : ref, t$in : ref where $Is(t$in, T), tn$in : ref where $Is(tn$in, T));
  free requires ($Heap[t$in, $allocated] == true);
  free requires ($Heap[tn$in, $allocated] == true);
  requires ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == Types)) && ($Heap[this, $localinv] == $typeof(this)));
  requires ((t$in == null) || (((($Heap[t$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[t$in, $ownerRef], $inv] <: $Heap[t$in, $ownerFrame])) || ($Heap[$Heap[t$in, $ownerRef], $localinv] == $BaseClass($Heap[t$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[t$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[t$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))));
  requires ((tn$in == null) || ((((($Heap[tn$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[tn$in, $ownerRef], $inv] <: $Heap[tn$in, $ownerFrame])) || ($Heap[$Heap[tn$in, $ownerRef], $localinv] == $BaseClass($Heap[tn$in, $ownerFrame]))) && ($Heap[tn$in, $inv] == $typeof(tn$in))) && ($Heap[tn$in, $localinv] == $typeof(tn$in))));
  requires (tn$in != t$in);
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation Types.Q$T$T(this : ref, t$in : ref, tn$in : ref) {
  var t : ref where $Is(t, T);
  var tn : ref where $Is(tn, T);
  var stack0o : ref;
  var stack0b : bool;
  var local11 : ref where $Is(local11, T);
  var stack1s : struct;
  var stack1o : ref;
  var temp0 : exposeVersionType;
  var n : ref where $Is(n, T);
  entry: assume $IsNotNull(this, Types); goto $$entry~bv;
  $$entry~bv: assume ($Heap[this, $allocated] == true); goto $$entry~bu;
  $$entry~bu: t := t$in; goto $$entry~bt;
  $$entry~bt: tn := tn$in; goto block31773;
  block31773: goto block32147;
  block32147: stack0o := null; goto true32147to32946, false32147to32164;
  true32147to32946: assume (t == stack0o); goto block32946;
  false32147to32164: assume (t != stack0o); goto block32164;
  block32946: stack0o := null; goto true32946to33082, false32946to32963;
  block32164: assert ($Heap[t, T.x] == $Heap[t, T.x]); goto block32249;
  true32946to33082: assume (t == stack0o); goto block33082;
  false32946to32963: assume (t != stack0o); goto block32963;
  block33082: stack0o := null; goto true33082to33881, false33082to33099;
  block32963: assume ((((($Heap[t, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[t, $ownerRef], $inv] <: $Heap[t, $ownerFrame])) || ($Heap[$Heap[t, $ownerRef], $localinv] == $BaseClass($Heap[t, $ownerFrame]))) && ($Heap[t, $inv] == T)) && ($Heap[t, $localinv] == $typeof(t))); goto block33048;
  block32249: assert $IsNotNull($Heap[t, T.y], D); goto block32334;
  true33082to33881: assume (t == stack0o); goto block33881;
  false33082to33099: assume (t != stack0o); goto block33099;
  block33881: stack0o := null; goto true33881to33915, false33881to33898;
  block33099: assert ($Heap[t, T.x] == $Heap[t, T.x]); goto block33184;
  block32334: assert $IsNotNull($Heap[t, T.y], D); goto block32419;
  block33048: local11 := t; goto $$block33048~j;
  $$block33048~j: stack0o := local11; goto $$block33048~i;
  $$block33048~i: havoc stack1s; goto $$block33048~h;
  $$block33048~h: assume $IsTokenForType(stack1s, T); goto $$block33048~g;
  $$block33048~g: stack1o := TypeObject(T); goto $$block33048~f;
  $$block33048~f: assert (stack0o != null); goto $$block33048~e;
  $$block33048~e: assert ((((($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame])) || ($Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]))) && ($Heap[stack0o, $inv] <: T)) && ($Heap[stack0o, $localinv] == $typeof(stack0o))); goto $$block33048~d;
  $$block33048~d: $Heap := $Heap[stack0o, $localinv := System.Object]; goto $$block33048~c;
  $$block33048~c: havoc temp0; goto $$block33048~b;
  $$block33048~b: $Heap := $Heap[stack0o, $exposeVersion := temp0]; goto $$block33048~a;
  $$block33048~a: assume IsHeap($Heap); goto block33065;
  true33881to33915: assume (t == stack0o); goto block33915;
  false33881to33898: assume (t != stack0o); goto block33898;
  block33915: stack0o := null; goto true33915to34714, false33915to33932;
  block33898: assert (t != null); goto $$block33898~a;
  $$block33898~a: call T.M(t); goto block33915;
  block32419: assert (t != null); goto $$block32419~b;
  $$block32419~b: stack0o := $Heap[t, T.next]; goto $$block32419~a;
  $$block32419~a: stack0o := $As(stack0o, T); goto true32419to32827, false32419to32436;
  true32419to32827: assume (stack0o == null); goto block32827;
  false32419to32436: assume (stack0o != null); goto block32436;
  block32827: assert (($Heap[ClassRepr(T), T.g] == null) || $IsNotNull($Heap[ClassRepr(T), T.g], C)); goto block32929;
  block32436: assert ($Heap[t, T.next] != null); goto block32521;
  block33065: assert (t != null); goto $$block33065~c;
  $$block33065~c: assert (!($Heap[t, $inv] <: T) || ($Heap[t, $localinv] == System.Object)); goto $$block33065~b;
  $$block33065~b: $Heap := $Heap[t, T.next := tn]; goto $$block33065~a;
  $$block33065~a: assume IsHeap($Heap); goto block34748;
  true33915to34714: assume (t == stack0o); goto block34714;
  false33915to33932: assume (t != stack0o); goto block33932;
  block34714: return;
  block33932: assert ($Heap[t, T.x] == $Heap[t, T.x]); goto block34017;
  block33184: assert $IsNotNull($Heap[t, T.y], D); goto block33269;
  block34748: stack0o := local11; goto $$block34748~h;
  $$block34748~h: havoc stack1s; goto $$block34748~g;
  $$block34748~g: assume $IsTokenForType(stack1s, T); goto $$block34748~f;
  $$block34748~f: stack1o := TypeObject(T); goto $$block34748~e;
  $$block34748~e: assert (stack0o != null); goto $$block34748~d;
  $$block34748~d: assert ($Heap[stack0o, $localinv] == System.Object); goto $$block34748~c;
  $$block34748~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == stack0o)) && ($Heap[$p, $ownerFrame] == T)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block34748~b;
  $$block34748~b: $Heap := $Heap[stack0o, $localinv := $typeof(stack0o)]; goto $$block34748~a;
  $$block34748~a: assume IsHeap($Heap); goto block33082;
  block33269: assert $IsNotNull($Heap[t, T.y], D); goto block33354;
  block32521: assert $IsNotNull($Heap[t, T.next], System.Object); goto block32606;
  block32929: goto block32946;
  block34017: assert $IsNotNull($Heap[t, T.y], D); goto block34102;
  block33354: assert (t != null); goto $$block33354~b;
  $$block33354~b: stack0o := $Heap[t, T.next]; goto $$block33354~a;
  $$block33354~a: stack0o := $As(stack0o, T); goto true33354to33762, false33354to33371;
  true33354to33762: assume (stack0o == null); goto block33762;
  false33354to33371: assume (stack0o != null); goto block33371;
  block33762: assert (($Heap[ClassRepr(T), T.g] == null) || $IsNotNull($Heap[ClassRepr(T), T.g], C)); goto block33864;
  block33371: assert ($Heap[t, T.next] != null); goto block33456;
  block32606: assert $IsNotNull($Heap[$Heap[t, T.next], T.y], D); goto block32691;
  block34102: assert $IsNotNull($Heap[t, T.y], D); goto block34187;
  block32691: assert (t != null); goto $$block32691~d;
  $$block32691~d: stack0o := $Heap[t, T.next]; goto $$block32691~c;
  $$block32691~c: assert (stack0o != null); goto $$block32691~b;
  $$block32691~b: n := $Heap[stack0o, T.next]; goto $$block32691~a;
  $$block32691~a: assert (((n == null) || $IsNotNull($Heap[n, T.x], D)) || ($Heap[n, T.x] == null)); goto block32810;
  block34187: assert (t != null); goto $$block34187~b;
  $$block34187~b: stack0o := $Heap[t, T.next]; goto $$block34187~a;
  $$block34187~a: stack0o := $As(stack0o, T); goto true34187to34595, false34187to34204;
  true34187to34595: assume (stack0o == null); goto block34595;
  false34187to34204: assume (stack0o != null); goto block34204;
  block34595: assert (($Heap[ClassRepr(T), T.g] == null) || $IsNotNull($Heap[ClassRepr(T), T.g], C)); goto block34697;
  block34204: assert ($Heap[t, T.next] != null); goto block34289;
  block33456: assert $IsNotNull($Heap[t, T.next], System.Object); goto block33541;
  block33864: goto block33881;
  block32810: goto block32827;
  block33541: assert $IsNotNull($Heap[$Heap[t, T.next], T.y], D); goto block33626;
  block34697: goto block34714;
  block34289: assert $IsNotNull($Heap[t, T.next], System.Object); goto block34374;
  block33626: assert (t != null); goto $$block33626~d;
  $$block33626~d: stack0o := $Heap[t, T.next]; goto $$block33626~c;
  $$block33626~c: assert (stack0o != null); goto $$block33626~b;
  $$block33626~b: n := $Heap[stack0o, T.next]; goto $$block33626~a;
  $$block33626~a: assert (((n == null) || $IsNotNull($Heap[n, T.x], D)) || ($Heap[n, T.x] == null)); goto block33745;
  block34374: assert $IsNotNull($Heap[$Heap[t, T.next], T.y], D); goto block34459;
  block33745: goto block33762;
  block34459: assert (t != null); goto $$block34459~d;
  $$block34459~d: stack0o := $Heap[t, T.next]; goto $$block34459~c;
  $$block34459~c: assert (stack0o != null); goto $$block34459~b;
  $$block34459~b: n := $Heap[stack0o, T.next]; goto $$block34459~a;
  $$block34459~a: assert (((n == null) || $IsNotNull($Heap[n, T.x], D)) || ($Heap[n, T.x] == null)); goto block34578;
  block34578: goto block34595;
  
}

axiom (System.Type <: System.Type);
axiom (System.Reflection.MemberInfo <: System.Reflection.MemberInfo);
axiom ($BaseClass(System.Reflection.MemberInfo) == System.Object);
axiom ((System.Reflection.MemberInfo <: $BaseClass(System.Reflection.MemberInfo)) && (AsDirectSubClass(System.Reflection.MemberInfo, $BaseClass(System.Reflection.MemberInfo)) == System.Reflection.MemberInfo));
axiom ($IsImmutable(System.Reflection.MemberInfo) && ($AsImmutable(System.Reflection.MemberInfo) == System.Reflection.MemberInfo));
axiom (System.Reflection.ICustomAttributeProvider <: System.Object);
axiom (forall $K : name :: {(System.Reflection.ICustomAttributeProvider <: $K)} ((System.Reflection.ICustomAttributeProvider <: $K) <==> ((System.Reflection.ICustomAttributeProvider == $K) || (System.Object == $K))));
axiom $IsMemberlessType(System.Reflection.ICustomAttributeProvider);
axiom (System.Reflection.MemberInfo <: System.Reflection.ICustomAttributeProvider);
axiom (System.Runtime.InteropServices._MemberInfo <: System.Object);
axiom (forall $K : name :: {(System.Runtime.InteropServices._MemberInfo <: $K)} ((System.Runtime.InteropServices._MemberInfo <: $K) <==> ((System.Runtime.InteropServices._MemberInfo == $K) || (System.Object == $K))));
axiom $IsMemberlessType(System.Runtime.InteropServices._MemberInfo);
axiom (System.Reflection.MemberInfo <: System.Runtime.InteropServices._MemberInfo);
axiom (forall $K : name :: {(System.Reflection.MemberInfo <: $K)} ((System.Reflection.MemberInfo <: $K) <==> ((((System.Reflection.MemberInfo == $K) || (System.Object <: $K)) || (System.Reflection.ICustomAttributeProvider <: $K)) || (System.Runtime.InteropServices._MemberInfo <: $K))));
axiom $IsMemberlessType(System.Reflection.MemberInfo);
axiom ($BaseClass(System.Type) == System.Reflection.MemberInfo);
axiom ((System.Type <: $BaseClass(System.Type)) && (AsDirectSubClass(System.Type, $BaseClass(System.Type)) == System.Type));
axiom ($IsImmutable(System.Type) && ($AsImmutable(System.Type) == System.Type));
axiom (System.Runtime.InteropServices._Type <: System.Object);
axiom (forall $K : name :: {(System.Runtime.InteropServices._Type <: $K)} ((System.Runtime.InteropServices._Type <: $K) <==> ((System.Runtime.InteropServices._Type == $K) || (System.Object == $K))));
axiom $IsMemberlessType(System.Runtime.InteropServices._Type);
axiom (System.Type <: System.Runtime.InteropServices._Type);
axiom (System.Reflection.IReflect <: System.Object);
axiom (forall $K : name :: {(System.Reflection.IReflect <: $K)} ((System.Reflection.IReflect <: $K) <==> ((System.Reflection.IReflect == $K) || (System.Object == $K))));
axiom $IsMemberlessType(System.Reflection.IReflect);
axiom (System.Type <: System.Reflection.IReflect);
axiom (forall $K : name :: {(System.Type <: $K)} ((System.Type <: $K) <==> ((((System.Type == $K) || (System.Reflection.MemberInfo <: $K)) || (System.Runtime.InteropServices._Type <: $K)) || (System.Reflection.IReflect <: $K))));
axiom $IsMemberlessType(System.Type);
procedure T.M(this : ref);
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
  

procedure Types..ctor(this : ref);
  free requires (forall $o : ref :: (($o != this) ==> ($Heap[$o, $ownerRef] != this)));
  free requires (($Heap[this, $ownerRef] == this) && ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder));
  free requires (forall $o : ref :: ((($Heap[$o, $ownerRef] == $Heap[this, $ownerRef]) && ($Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame])) ==> ($o == this)));
  free requires ($BeingConstructed == this);
  modifies $Heap;
  ensures ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == Types)) && ($Heap[this, $localinv] == $typeof(this)));
  ensures (($Heap[this, $ownerRef] == old($Heap)[this, $ownerRef]) && ($Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame]));
  ensures ($Heap[this, $sharingMode] == $SharingMode_Unshared);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(Types <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

implementation Types..ctor(this : ref) {
  entry: assume $IsNotNull(this, Types); goto $$entry~bx;
  $$entry~bx: assume ($Heap[this, $allocated] == true); goto $$entry~bw;
  $$entry~bw: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto block37876;
  block37876: goto block37893;
  block37893: assert (this != null); goto $$block37893~f;
  $$block37893~f: call System.Object..ctor(this); goto $$block37893~e;
  $$block37893~e: assert (this != null); goto $$block37893~d;
  $$block37893~d: assert (($Heap[this, $inv] == System.Object) && ($Heap[this, $localinv] == $typeof(this))); goto $$block37893~c;
  $$block37893~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == Types)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block37893~b;
  $$block37893~b: $Heap := $Heap[this, $inv := Types]; goto $$block37893~a;
  $$block37893~a: assume IsHeap($Heap); return;
  
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
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(A <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

implementation A..ctor(this : ref) {
  entry: assume $IsNotNull(this, A); goto $$entry~bz;
  $$entry~bz: assume ($Heap[this, $allocated] == true); goto $$entry~by;
  $$entry~by: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto block38063;
  block38063: goto block38080;
  block38080: assert (this != null); goto $$block38080~f;
  $$block38080~f: call System.Object..ctor(this); goto $$block38080~e;
  $$block38080~e: assert (this != null); goto $$block38080~d;
  $$block38080~d: assert (($Heap[this, $inv] == System.Object) && ($Heap[this, $localinv] == $typeof(this))); goto $$block38080~c;
  $$block38080~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == A)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block38080~b;
  $$block38080~b: $Heap := $Heap[this, $inv := A]; goto $$block38080~a;
  $$block38080~a: assume IsHeap($Heap); return;
  
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
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(B <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

implementation B..ctor(this : ref) {
  entry: assume $IsNotNull(this, B); goto $$entry~cb;
  $$entry~cb: assume ($Heap[this, $allocated] == true); goto $$entry~ca;
  $$entry~ca: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto block38250;
  block38250: goto block38267;
  block38267: assert (this != null); goto $$block38267~f;
  $$block38267~f: call A..ctor(this); goto $$block38267~e;
  $$block38267~e: assert (this != null); goto $$block38267~d;
  $$block38267~d: assert (($Heap[this, $inv] == A) && ($Heap[this, $localinv] == $typeof(this))); goto $$block38267~c;
  $$block38267~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == B)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block38267~b;
  $$block38267~b: $Heap := $Heap[this, $inv := B]; goto $$block38267~a;
  $$block38267~a: assume IsHeap($Heap); return;
  
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
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(C <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

implementation C..ctor(this : ref) {
  entry: assume $IsNotNull(this, C); goto $$entry~cd;
  $$entry~cd: assume ($Heap[this, $allocated] == true); goto $$entry~cc;
  $$entry~cc: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto block38437;
  block38437: goto block38454;
  block38454: assert (this != null); goto $$block38454~f;
  $$block38454~f: call B..ctor(this); goto $$block38454~e;
  $$block38454~e: assert (this != null); goto $$block38454~d;
  $$block38454~d: assert (($Heap[this, $inv] == B) && ($Heap[this, $localinv] == $typeof(this))); goto $$block38454~c;
  $$block38454~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == C)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block38454~b;
  $$block38454~b: $Heap := $Heap[this, $inv := C]; goto $$block38454~a;
  $$block38454~a: assume IsHeap($Heap); return;
  
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
  entry: assume $IsNotNull(this, D); goto $$entry~cf;
  $$entry~cf: assume ($Heap[this, $allocated] == true); goto $$entry~ce;
  $$entry~ce: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto block38624;
  block38624: goto block38641;
  block38641: assert (this != null); goto $$block38641~f;
  $$block38641~f: call A..ctor(this); goto $$block38641~e;
  $$block38641~e: assert (this != null); goto $$block38641~d;
  $$block38641~d: assert (($Heap[this, $inv] == A) && ($Heap[this, $localinv] == $typeof(this))); goto $$block38641~c;
  $$block38641~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == D)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block38641~b;
  $$block38641~b: $Heap := $Heap[this, $inv := D]; goto $$block38641~a;
  $$block38641~a: assume IsHeap($Heap); return;
  
}

procedure F..ctor(this : ref);
  free requires (forall $o : ref :: (($o != this) ==> ($Heap[$o, $ownerRef] != this)));
  free requires (($Heap[this, $ownerRef] == this) && ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder));
  free requires (forall $o : ref :: ((($Heap[$o, $ownerRef] == $Heap[this, $ownerRef]) && ($Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame])) ==> ($o == this)));
  free requires ($BeingConstructed == this);
  modifies $Heap;
  ensures ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == F)) && ($Heap[this, $localinv] == $typeof(this)));
  ensures (($Heap[this, $ownerRef] == old($Heap)[this, $ownerRef]) && ($Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame]));
  ensures ($Heap[this, $sharingMode] == $SharingMode_Unshared);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(F <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

implementation F..ctor(this : ref) {
  entry: assume $IsNotNull(this, F); goto $$entry~ch;
  $$entry~ch: assume ($Heap[this, $allocated] == true); goto $$entry~cg;
  $$entry~cg: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto block38811;
  block38811: goto block38828;
  block38828: assert (this != null); goto $$block38828~f;
  $$block38828~f: call A..ctor(this); goto $$block38828~e;
  $$block38828~e: assert (this != null); goto $$block38828~d;
  $$block38828~d: assert (($Heap[this, $inv] == A) && ($Heap[this, $localinv] == $typeof(this))); goto $$block38828~c;
  $$block38828~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == F)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block38828~b;
  $$block38828~b: $Heap := $Heap[this, $inv := F]; goto $$block38828~a;
  $$block38828~a: assume IsHeap($Heap); return;
  
}

procedure T..ctor$D$notnull(this : ref, d$in : ref where $IsNotNull(d$in, D));
  free requires ($Heap[d$in, $allocated] == true);
  requires (((($Heap[d$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[d$in, $ownerRef], $inv] <: $Heap[d$in, $ownerFrame])) || ($Heap[$Heap[d$in, $ownerRef], $localinv] == $BaseClass($Heap[d$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[d$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[d$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
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
  

implementation T..ctor$D$notnull(this : ref, d$in : ref) {
  var d : ref where $IsNotNull(d, D);
  entry: assume $IsNotNull(this, T); goto $$entry~cm;
  $$entry~cm: assume ($Heap[this, $allocated] == true); goto $$entry~cl;
  $$entry~cl: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto $$entry~ck;
  $$entry~ck: d := d$in; goto $$entry~cj;
  $$entry~cj: assume ($Heap[this, T.x] == null); goto $$entry~ci;
  $$entry~ci: assume ($Heap[this, T.next] == null); goto block39083;
  block39083: goto block39185;
  block39185: assert (this != null); goto $$block39185~j;
  $$block39185~j: assert (!($Heap[this, $inv] <: T) || ($Heap[this, $localinv] == System.Object)); goto $$block39185~i;
  $$block39185~i: $Heap := $Heap[this, T.y := d]; goto $$block39185~h;
  $$block39185~h: assume IsHeap($Heap); goto $$block39185~g;
  $$block39185~g: assert (this != null); goto $$block39185~f;
  $$block39185~f: call System.Object..ctor(this); goto $$block39185~e;
  $$block39185~e: assert (this != null); goto $$block39185~d;
  $$block39185~d: assert (($Heap[this, $inv] == System.Object) && ($Heap[this, $localinv] == $typeof(this))); goto $$block39185~c;
  $$block39185~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == T)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block39185~b;
  $$block39185~b: $Heap := $Heap[this, $inv := T]; goto $$block39185~a;
  $$block39185~a: assume IsHeap($Heap); return;
  
}

implementation T.M(this : ref) {
  entry: assume $IsNotNull(this, T); goto $$entry~cn;
  $$entry~cn: assume ($Heap[this, $allocated] == true); goto block39423;
  block39423: goto block39440;
  block39440: return;
  
}

axiom (MoreTypes <: MoreTypes);
axiom ($BaseClass(MoreTypes) == System.Object);
axiom ((MoreTypes <: $BaseClass(MoreTypes)) && (AsDirectSubClass(MoreTypes, $BaseClass(MoreTypes)) == MoreTypes));
axiom (!$IsImmutable(MoreTypes) && ($AsMutable(MoreTypes) == MoreTypes));
axiom (forall $K : name :: {(MoreTypes <: $K)} ((MoreTypes <: $K) <==> ((MoreTypes == $K) || (System.Object <: $K))));
procedure MoreTypes.M$System.Object(this : ref, t$in : ref where $Is(t$in, System.Object));
  free requires ($Heap[t$in, $allocated] == true);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires ((t$in == null) || (((($Heap[t$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[t$in, $ownerRef], $inv] <: $Heap[t$in, $ownerFrame])) || ($Heap[$Heap[t$in, $ownerRef], $localinv] == $BaseClass($Heap[t$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[t$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[t$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation MoreTypes.M$System.Object(this : ref, t$in : ref) {
  var t : ref where $Is(t, System.Object);
  var stack0o : ref;
  entry: assume $IsNotNull(this, MoreTypes); goto $$entry~cp;
  $$entry~cp: assume ($Heap[this, $allocated] == true); goto $$entry~co;
  $$entry~co: t := t$in; goto block39763;
  block39763: goto block39780;
  block39780: assume $IsNotNull(t, MoreTypes); goto block39865;
  block39865: assert (t != null); goto block39950;
  block39950: return;
  
}

procedure MoreTypes.N$System.Object(this : ref, t$in : ref where $Is(t$in, System.Object));
  free requires ($Heap[t$in, $allocated] == true);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires ((t$in == null) || (((($Heap[t$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[t$in, $ownerRef], $inv] <: $Heap[t$in, $ownerFrame])) || ($Heap[$Heap[t$in, $ownerRef], $localinv] == $BaseClass($Heap[t$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[t$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[t$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation MoreTypes.N$System.Object(this : ref, t$in : ref) {
  var t : ref where $Is(t, System.Object);
  var stack0o : ref;
  var stack0b : bool;
  entry: assume $IsNotNull(this, MoreTypes); goto $$entry~cr;
  $$entry~cr: assume ($Heap[this, $allocated] == true); goto $$entry~cq;
  $$entry~cq: t := t$in; goto block40392;
  block40392: goto block40409;
  block40409: stack0o := $As(t, MoreTypes); goto true40409to40528, false40409to40426;
  true40409to40528: assume (stack0o == null); goto block40528;
  false40409to40426: assume (stack0o != null); goto block40426;
  block40528: return;
  block40426: assert (t != null); goto block40511;
  block40511: goto block40528;
  
}

procedure MoreTypes.P$System.Object(this : ref, t$in : ref where $Is(t$in, System.Object));
  free requires ($Heap[t$in, $allocated] == true);
  requires (((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[this, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc))))));
  requires ((t$in == null) || (((($Heap[t$in, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[t$in, $ownerRef], $inv] <: $Heap[t$in, $ownerFrame])) || ($Heap[$Heap[t$in, $ownerRef], $localinv] == $BaseClass($Heap[t$in, $ownerFrame]))) && (forall $pc : ref :: ((((($pc != null) && ($Heap[$pc, $allocated] == true)) && ($Heap[$pc, $ownerRef] == $Heap[t$in, $ownerRef])) && ($Heap[$pc, $ownerFrame] == $Heap[t$in, $ownerFrame])) ==> (($Heap[$pc, $inv] == $typeof($pc)) && ($Heap[$pc, $localinv] == $typeof($pc)))))));
  free requires ($BeingConstructed == null);
  modifies $Heap;
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && old(true)) && old((($o != this) || ($f != $exposeVersion)))) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: (((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv])) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]));
  

implementation MoreTypes.P$System.Object(this : ref, t$in : ref) {
  var t : ref where $Is(t, System.Object);
  var stack0o : ref;
  var stack1o : ref;
  var stack0b : bool;
  var b : bool where true;
  entry: assume $IsNotNull(this, MoreTypes); goto $$entry~ct;
  $$entry~ct: assume ($Heap[this, $allocated] == true); goto $$entry~cs;
  $$entry~cs: t := t$in; goto block40987;
  block40987: goto block41004;
  block41004: stack0o := $As(t, MoreTypes); goto $$block41004~a;
  $$block41004~a: stack1o := null; goto true41004to41038, false41004to41021;
  true41004to41038: assume (stack0o != stack1o); goto block41038;
  false41004to41021: assume (stack0o == stack1o); goto block41021;
  block41038: stack0b := true; goto block41055;
  block41021: stack0b := false; goto block41055;
  block41055: b := stack0b; goto $$block41055~a;
  $$block41055~a: stack0b := b; goto true41055to41174, false41055to41072;
  true41055to41174: assume !stack0b; goto block41174;
  false41055to41072: assume stack0b; goto block41072;
  block41174: return;
  block41072: assert (t != null); goto block41157;
  block41157: goto block41174;
  
}

procedure MoreTypes..ctor(this : ref);
  free requires (forall $o : ref :: (($o != this) ==> ($Heap[$o, $ownerRef] != this)));
  free requires (($Heap[this, $ownerRef] == this) && ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder));
  free requires (forall $o : ref :: ((($Heap[$o, $ownerRef] == $Heap[this, $ownerRef]) && ($Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame])) ==> ($o == this)));
  free requires ($BeingConstructed == this);
  modifies $Heap;
  ensures ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == MoreTypes)) && ($Heap[this, $localinv] == $typeof(this)));
  ensures (($Heap[this, $ownerRef] == old($Heap)[this, $ownerRef]) && ($Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame]));
  ensures ($Heap[this, $sharingMode] == $SharingMode_Unshared);
  free ensures (forall $o : ref :: (((($o != null) && (old($Heap)[$o, $allocated] != true)) && ($Heap[$o, $allocated] == true)) ==> (($Heap[$o, $inv] == $typeof($o)) && ($Heap[$o, $localinv] == $typeof($o)))));
  free ensures (forall $o : ref :: {$Heap[$o, $FirstConsistentOwner]} ((old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion]) ==> (old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner])));
  ensures (forall $o : ref :: ((($o != null) && (old($Heap)[$o, $allocated] == true)) ==> ((old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef]) && (old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]))));
  free ensures (forall $o : ref, $f : name :: {$Heap[$o, $f]} (((((((((($f != $inv) && ($f != $localinv)) && ($f != $FirstConsistentOwner)) && (!IsStaticField($f) || !IsDirectlyModifiableField($f))) && ($o != null)) && (old($Heap)[$o, $allocated] == true)) && (((old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder) || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame])) || (old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])))) && (($o != this) || !(MoreTypes <: DeclType($f)))) && old(true)) ==> (old($Heap)[$o, $f] == $Heap[$o, $f])));
  free ensures (forall $o : ref :: ((($o == this) || ((old($Heap)[$o, $inv] == $Heap[$o, $inv]) && (old($Heap)[$o, $localinv] == $Heap[$o, $localinv]))) || (old($Heap)[$o, $allocated] != true)));
  free ensures (((forall $o : ref :: ((old($Heap)[$o, $allocated] == true) ==> ($Heap[$o, $allocated] == true))) && (forall $ot : ref :: (((old($Heap)[$ot, $allocated] == true) && (old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder)) ==> (($Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef]) && ($Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]))))) && (old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized]));
  free ensures (forall $o : ref :: (($o == this) || (old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode])));
  

implementation MoreTypes..ctor(this : ref) {
  entry: assume $IsNotNull(this, MoreTypes); goto $$entry~cv;
  $$entry~cv: assume ($Heap[this, $allocated] == true); goto $$entry~cu;
  $$entry~cu: assume ((((($Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame])) || ($Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) && ($Heap[this, $inv] == System.Object)) && ($Heap[this, $localinv] == $typeof(this))); goto block41599;
  block41599: goto block41616;
  block41616: assert (this != null); goto $$block41616~f;
  $$block41616~f: call System.Object..ctor(this); goto $$block41616~e;
  $$block41616~e: assert (this != null); goto $$block41616~d;
  $$block41616~d: assert (($Heap[this, $inv] == System.Object) && ($Heap[this, $localinv] == $typeof(this))); goto $$block41616~c;
  $$block41616~c: assert (forall $p : ref :: ((((($p != null) && ($Heap[$p, $allocated] == true)) && ($Heap[$p, $ownerRef] == this)) && ($Heap[$p, $ownerFrame] == MoreTypes)) ==> (($Heap[$p, $inv] == $typeof($p)) && ($Heap[$p, $localinv] == $typeof($p))))); goto $$block41616~b;
  $$block41616~b: $Heap := $Heap[this, $inv := MoreTypes]; goto $$block41616~a;
  $$block41616~a: assume IsHeap($Heap); return;
  
}

