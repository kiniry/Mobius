package java.util;

public class Collections {
    
    /*synthetic*/ static boolean access$000(Object x0, Object x1) {
        return eq(x0, x1);
    }
    
    private Collections() {
        
    }
    private static final int BINARYSEARCH_THRESHOLD = 5000;
    private static final int REVERSE_THRESHOLD = 18;
    private static final int SHUFFLE_THRESHOLD = 5;
    private static final int FILL_THRESHOLD = 25;
    private static final int ROTATE_THRESHOLD = 100;
    private static final int COPY_THRESHOLD = 10;
    private static final int REPLACEALL_THRESHOLD = 11;
    private static final int INDEXOFSUBLIST_THRESHOLD = 35;
    
    public static void sort(List list) {
        Object[] a = list.toArray();
        Arrays.sort(a);
        ListIterator i = list.listIterator();
        for (int j = 0; j < a.length; j++) {
            i.next();
            i.set((Comparable)(Comparable)a[j]);
        }
    }
    
    public static void sort(List list, Comparator c) {
        Object[] a = list.toArray();
        Arrays.sort(a, (Comparator)c);
        ListIterator i = list.listIterator();
        for (int j = 0; j < a.length; j++) {
            i.next();
            i.set(a[j]);
        }
    }
    
    public static int binarySearch(List list, Object key) {
        if (list instanceof RandomAccess || list.size() < BINARYSEARCH_THRESHOLD) return Collections.indexedBinarySearch(list, key); else return Collections.iteratorBinarySearch(list, key);
    }
    
    private static int indexedBinarySearch(List list, Object key) {
        int low = 0;
        int high = list.size() - 1;
        while (low <= high) {
            int mid = (low + high) >> 1;
            Comparable midVal = (Comparable)list.get(mid);
            int cmp = midVal.compareTo(key);
            if (cmp < 0) low = mid + 1; else if (cmp > 0) high = mid - 1; else return mid;
        }
        return -(low + 1);
    }
    
    private static int iteratorBinarySearch(List list, Object key) {
        int low = 0;
        int high = list.size() - 1;
        ListIterator i = list.listIterator();
        while (low <= high) {
            int mid = (low + high) >> 1;
            Comparable midVal = (Comparable)get(i, mid);
            int cmp = midVal.compareTo(key);
            if (cmp < 0) low = mid + 1; else if (cmp > 0) high = mid - 1; else return mid;
        }
        return -(low + 1);
    }
    
    private static Object get(ListIterator i, int index) {
        Object obj = null;
        int pos = i.nextIndex();
        if (pos <= index) {
            do {
                obj = i.next();
            }             while (pos++ < index);
        } else {
            do {
                obj = i.previous();
            }             while (--pos > index);
        }
        return obj;
    }
    
    public static int binarySearch(List list, Object key, Comparator c) {
        if (c == null) return binarySearch((List)list, key);
        if (list instanceof RandomAccess || list.size() < BINARYSEARCH_THRESHOLD) return Collections.indexedBinarySearch(list, key, c); else return Collections.iteratorBinarySearch(list, key, c);
    }
    
    private static int indexedBinarySearch(List l, Object key, Comparator c) {
        int low = 0;
        int high = l.size() - 1;
        while (low <= high) {
            int mid = (low + high) >> 1;
            Object midVal = l.get(mid);
            int cmp = c.compare(midVal, key);
            if (cmp < 0) low = mid + 1; else if (cmp > 0) high = mid - 1; else return mid;
        }
        return -(low + 1);
    }
    
    private static int iteratorBinarySearch(List l, Object key, Comparator c) {
        int low = 0;
        int high = l.size() - 1;
        ListIterator i = l.listIterator();
        while (low <= high) {
            int mid = (low + high) >> 1;
            Object midVal = get(i, mid);
            int cmp = c.compare(midVal, key);
            if (cmp < 0) low = mid + 1; else if (cmp > 0) high = mid - 1; else return mid;
        }
        return -(low + 1);
    }
    {
    }
    
    public static void reverse(List list) {
        int size = list.size();
        if (size < REVERSE_THRESHOLD || list instanceof RandomAccess) {
            for (int i = 0, mid = size >> 1, j = size - 1; i < mid; i++, j--) swap(list, i, j);
        } else {
            ListIterator fwd = list.listIterator();
            ListIterator rev = list.listIterator(size);
            for (int i = 0, mid = list.size() >> 1; i < mid; i++) {
                Object tmp = fwd.next();
                fwd.set(rev.previous());
                rev.set(tmp);
            }
        }
    }
    
    public static void shuffle(List list) {
        shuffle(list, r);
    }
    private static Random r = new Random();
    
    public static void shuffle(List list, Random rnd) {
        int size = list.size();
        if (size < SHUFFLE_THRESHOLD || list instanceof RandomAccess) {
            for (int i = size; i > 1; i--) swap(list, i - 1, rnd.nextInt(i));
        } else {
            Object[] arr = list.toArray();
            for (int i = size; i > 1; i--) swap(arr, i - 1, rnd.nextInt(i));
            ListIterator it = list.listIterator();
            for (int i = 0; i < arr.length; i++) {
                it.next();
                it.set(arr[i]);
            }
        }
    }
    
    public static void swap(List list, int i, int j) {
        final List l = list;
        l.set(i, l.set(j, l.get(i)));
    }
    
    private static void swap(Object[] arr, int i, int j) {
        Object tmp = arr[i];
        arr[i] = arr[j];
        arr[j] = tmp;
    }
    
    public static void fill(List list, Object obj) {
        int size = list.size();
        if (size < FILL_THRESHOLD || list instanceof RandomAccess) {
            for (int i = 0; i < size; i++) list.set(i, obj);
        } else {
            ListIterator itr = list.listIterator();
            for (int i = 0; i < size; i++) {
                itr.next();
                itr.set(obj);
            }
        }
    }
    
    public static void copy(List dest, List src) {
        int srcSize = src.size();
        if (srcSize > dest.size()) throw new IndexOutOfBoundsException("Source does not fit in dest");
        if (srcSize < COPY_THRESHOLD || (src instanceof RandomAccess && dest instanceof RandomAccess)) {
            for (int i = 0; i < srcSize; i++) dest.set(i, src.get(i));
        } else {
            ListIterator di = dest.listIterator();
            ListIterator si = src.listIterator();
            for (int i = 0; i < srcSize; i++) {
                di.next();
                di.set(si.next());
            }
        }
    }
    
    public static Object min(Collection coll) {
        Iterator i = coll.iterator();
        Object candidate = i.next();
        while (i.hasNext()) {
            Object next = i.next();
            if (((Comparable)next).compareTo(candidate) < 0) candidate = next;
        }
        return candidate;
    }
    
    public static Object min(Collection coll, Comparator comp) {
        if (comp == null) return (Object)min((Collection)(Collection)coll);
        Iterator i = coll.iterator();
        Object candidate = i.next();
        while (i.hasNext()) {
            Object next = i.next();
            if (comp.compare(next, candidate) < 0) candidate = next;
        }
        return candidate;
    }
    
    public static Object max(Collection coll) {
        Iterator i = coll.iterator();
        Object candidate = i.next();
        while (i.hasNext()) {
            Object next = i.next();
            if (((Comparable)next).compareTo(candidate) > 0) candidate = next;
        }
        return candidate;
    }
    
    public static Object max(Collection coll, Comparator comp) {
        if (comp == null) return (Object)max((Collection)(Collection)coll);
        Iterator i = coll.iterator();
        Object candidate = i.next();
        while (i.hasNext()) {
            Object next = i.next();
            if (comp.compare(next, candidate) > 0) candidate = next;
        }
        return candidate;
    }
    
    public static void rotate(List list, int distance) {
        if (list instanceof RandomAccess || list.size() < ROTATE_THRESHOLD) rotate1((List)list, distance); else rotate2((List)list, distance);
    }
    
    private static void rotate1(List list, int distance) {
        int size = list.size();
        if (size == 0) return;
        distance = distance % size;
        if (distance < 0) distance += size;
        if (distance == 0) return;
        for (int cycleStart = 0, nMoved = 0; nMoved != size; cycleStart++) {
            Object displaced = list.get(cycleStart);
            int i = cycleStart;
            do {
                i += distance;
                if (i >= size) i -= size;
                displaced = list.set(i, displaced);
                nMoved++;
            }             while (i != cycleStart);
        }
    }
    
    private static void rotate2(List list, int distance) {
        int size = list.size();
        if (size == 0) return;
        int mid = -distance % size;
        if (mid < 0) mid += size;
        if (mid == 0) return;
        reverse(list.subList(0, mid));
        reverse(list.subList(mid, size));
        reverse(list);
    }
    
    public static boolean replaceAll(List list, Object oldVal, Object newVal) {
        boolean result = false;
        int size = list.size();
        if (size < REPLACEALL_THRESHOLD || list instanceof RandomAccess) {
            if (oldVal == null) {
                for (int i = 0; i < size; i++) {
                    if (list.get(i) == null) {
                        list.set(i, newVal);
                        result = true;
                    }
                }
            } else {
                for (int i = 0; i < size; i++) {
                    if (oldVal.equals(list.get(i))) {
                        list.set(i, newVal);
                        result = true;
                    }
                }
            }
        } else {
            ListIterator itr = list.listIterator();
            if (oldVal == null) {
                for (int i = 0; i < size; i++) {
                    if (itr.next() == null) {
                        itr.set(newVal);
                        result = true;
                    }
                }
            } else {
                for (int i = 0; i < size; i++) {
                    if (oldVal.equals(itr.next())) {
                        itr.set(newVal);
                        result = true;
                    }
                }
            }
        }
        return result;
    }
    
    public static int indexOfSubList(List source, List target) {
        int sourceSize = source.size();
        int targetSize = target.size();
        int maxCandidate = sourceSize - targetSize;
        if (sourceSize < INDEXOFSUBLIST_THRESHOLD || (source instanceof RandomAccess && target instanceof RandomAccess)) {
            nextCand: for (int candidate = 0; candidate <= maxCandidate; candidate++) {
                for (int i = 0, j = candidate; i < targetSize; i++, j++) if (!eq(target.get(i), source.get(j))) continue nextCand;
                return candidate;
            }
        } else {
            ListIterator si = source.listIterator();
            nextCand: for (int candidate = 0; candidate <= maxCandidate; candidate++) {
                ListIterator ti = target.listIterator();
                for (int i = 0; i < targetSize; i++) {
                    if (!eq(ti.next(), si.next())) {
                        for (int j = 0; j < i; j++) si.previous();
                        continue nextCand;
                    }
                }
                return candidate;
            }
        }
        return -1;
    }
    
    public static int lastIndexOfSubList(List source, List target) {
        int sourceSize = source.size();
        int targetSize = target.size();
        int maxCandidate = sourceSize - targetSize;
        if (sourceSize < INDEXOFSUBLIST_THRESHOLD || source instanceof RandomAccess) {
            nextCand: for (int candidate = maxCandidate; candidate >= 0; candidate--) {
                for (int i = 0, j = candidate; i < targetSize; i++, j++) if (!eq(target.get(i), source.get(j))) continue nextCand;
                return candidate;
            }
        } else {
            if (maxCandidate < 0) return -1;
            ListIterator si = source.listIterator(maxCandidate);
            nextCand: for (int candidate = maxCandidate; candidate >= 0; candidate--) {
                ListIterator ti = target.listIterator();
                for (int i = 0; i < targetSize; i++) {
                    if (!eq(ti.next(), si.next())) {
                        if (candidate != 0) {
                            for (int j = 0; j <= i + 1; j++) si.previous();
                        }
                        continue nextCand;
                    }
                }
                return candidate;
            }
        }
        return -1;
    }
    
    public static Collection unmodifiableCollection(Collection c) {
        return new Collections$UnmodifiableCollection(c);
    }
    {
    }
    
    public static Set unmodifiableSet(Set s) {
        return new Collections$UnmodifiableSet(s);
    }
    {
    }
    
    public static SortedSet unmodifiableSortedSet(SortedSet s) {
        return new Collections$UnmodifiableSortedSet(s);
    }
    {
    }
    
    public static List unmodifiableList(List list) {
        return (list instanceof RandomAccess ? new Collections$UnmodifiableRandomAccessList(list) : new Collections$UnmodifiableList(list));
    }
    {
    }
    {
    }
    
    public static Map unmodifiableMap(Map m) {
        return new Collections$UnmodifiableMap(m);
    }
    {
    }
    
    public static SortedMap unmodifiableSortedMap(SortedMap m) {
        return new Collections$UnmodifiableSortedMap(m);
    }
    {
    }
    
    public static Collection synchronizedCollection(Collection c) {
        return new Collections$SynchronizedCollection(c);
    }
    
    static Collection synchronizedCollection(Collection c, Object mutex) {
        return new Collections$SynchronizedCollection(c, mutex);
    }
    {
    }
    
    public static Set synchronizedSet(Set s) {
        return new Collections$SynchronizedSet(s);
    }
    
    static Set synchronizedSet(Set s, Object mutex) {
        return new Collections$SynchronizedSet(s, mutex);
    }
    {
    }
    
    public static SortedSet synchronizedSortedSet(SortedSet s) {
        return new Collections$SynchronizedSortedSet(s);
    }
    {
    }
    
    public static List synchronizedList(List list) {
        return (list instanceof RandomAccess ? new Collections$SynchronizedRandomAccessList(list) : new Collections$SynchronizedList(list));
    }
    
    static List synchronizedList(List list, Object mutex) {
        return (list instanceof RandomAccess ? new Collections$SynchronizedRandomAccessList(list, mutex) : new Collections$SynchronizedList(list, mutex));
    }
    {
    }
    {
    }
    
    public static Map synchronizedMap(Map m) {
        return new Collections$SynchronizedMap(m);
    }
    {
    }
    
    public static SortedMap synchronizedSortedMap(SortedMap m) {
        return new Collections$SynchronizedSortedMap(m);
    }
    {
    }
    
    public static Collection checkedCollection(Collection c, Class type) {
        return new Collections$CheckedCollection(c, type);
    }
    {
    }
    
    public static Set checkedSet(Set s, Class type) {
        return new Collections$CheckedSet(s, type);
    }
    {
    }
    
    public static SortedSet checkedSortedSet(SortedSet s, Class type) {
        return new Collections$CheckedSortedSet(s, type);
    }
    {
    }
    
    public static List checkedList(List list, Class type) {
        return (list instanceof RandomAccess ? new Collections$CheckedRandomAccessList(list, type) : new Collections$CheckedList(list, type));
    }
    {
    }
    {
    }
    
    public static Map checkedMap(Map m, Class keyType, Class valueType) {
        return new Collections$CheckedMap(m, keyType, valueType);
    }
    {
    }
    
    public static SortedMap checkedSortedMap(SortedMap m, Class keyType, Class valueType) {
        return new Collections$CheckedSortedMap(m, keyType, valueType);
    }
    {
    }
    public static final Set EMPTY_SET = new Collections$EmptySet(null);
    
    public static final Set emptySet() {
        return (Set)EMPTY_SET;
    }
    {
    }
    public static final List EMPTY_LIST = new Collections$EmptyList(null);
    
    public static final List emptyList() {
        return (List)EMPTY_LIST;
    }
    {
    }
    public static final Map EMPTY_MAP = new Collections$EmptyMap(null);
    
    public static final Map emptyMap() {
        return (Map)EMPTY_MAP;
    }
    {
    }
    
    public static Set singleton(Object o) {
        return new Collections$SingletonSet(o);
    }
    {
    }
    
    public static List singletonList(Object o) {
        return new Collections$SingletonList(o);
    }
    {
    }
    
    public static Map singletonMap(Object key, Object value) {
        return new Collections$SingletonMap(key, value);
    }
    {
    }
    
    public static List nCopies(int n, Object o) {
        return new Collections$CopiesList(n, o);
    }
    {
    }
    
    public static Comparator reverseOrder() {
        return (Comparator)REVERSE_ORDER;
    }
    private static final Comparator REVERSE_ORDER = new Collections$ReverseComparator(null);
    {
    }
    
    public static Comparator reverseOrder(Comparator cmp) {
        if (cmp == null) return new Collections$ReverseComparator(null);
        return new Collections$ReverseComparator2(cmp);
    }
    {
    }
    
    public static Enumeration enumeration(final Collection c) {
        return new Collections$1(c);
    }
    
    public static ArrayList list(Enumeration e) {
        ArrayList l = new ArrayList();
        while (e.hasMoreElements()) l.add(e.nextElement());
        return l;
    }
    
    private static boolean eq(Object o1, Object o2) {
        return (o1 == null ? o2 == null : o1.equals(o2));
    }
    
    public static int frequency(Collection c, Object o) {
        int result = 0;
        if (o == null) {
            for (Iterator i$ = c.iterator(); i$.hasNext(); ) {
                Object e = (Object)i$.next();
                if (e == null) result++;
            }
        } else {
            for (Iterator i$ = c.iterator(); i$.hasNext(); ) {
                Object e = (Object)i$.next();
                if (o.equals(e)) result++;
            }
        }
        return result;
    }
    
    public static boolean disjoint(Collection c1, Collection c2) {
        if ((c1 instanceof Set) && !(c2 instanceof Set) || (c1.size() > c2.size())) {
            Collection tmp = c1;
            c1 = c2;
            c2 = tmp;
        }
        for (Iterator i$ = c1.iterator(); i$.hasNext(); ) {
            Object e = (Object)i$.next();
            if (c2.contains(e)) return false;
        }
        return true;
    }
    
    public static boolean addAll(Collection c, Object[] a) {
        boolean result = false;
        for (Object[] arr$ = a, len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
            Object e = arr$[i$];
            result |= c.add(e);
        }
        return result;
    }
}
