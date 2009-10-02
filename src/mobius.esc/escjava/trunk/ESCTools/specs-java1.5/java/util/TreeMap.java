package java.util;

public class TreeMap extends AbstractMap implements SortedMap, Cloneable, java.io.Serializable {
    
    /*synthetic*/ static int access$1600(TreeMap x0) {
        return x0.modCount;
    }
    
    /*synthetic*/ static TreeMap$Entry access$1400(TreeMap x0, Object x1) {
        return x0.getPrecedingEntry(x1);
    }
    
    /*synthetic*/ static TreeMap$Entry access$1300(TreeMap x0) {
        return x0.lastEntry();
    }
    
    /*synthetic*/ static Object access$1200(TreeMap$Entry x0) {
        return key(x0);
    }
    
    /*synthetic*/ static TreeMap$Entry access$1100(TreeMap x0, Object x1) {
        return x0.getCeilEntry(x1);
    }
    
    /*synthetic*/ static Comparator access$1000(TreeMap x0) {
        return x0.comparator;
    }
    
    /*synthetic*/ static int access$900(TreeMap x0, Object x1, Object x2) {
        return x0.compare(x1, x2);
    }
    
    /*synthetic*/ static TreeMap$Entry access$800(TreeMap x0, Object x1) {
        return x0.getEntry(x1);
    }
    
    /*synthetic*/ static void access$600(TreeMap x0, TreeMap$Entry x1) {
        x0.deleteEntry(x1);
    }
    
    /*synthetic*/ static boolean access$500(Object x0, Object x1) {
        return valEquals(x0, x1);
    }
    
    /*synthetic*/ static TreeMap$Entry access$400(TreeMap x0, TreeMap$Entry x1) {
        return x0.successor(x1);
    }
    
    /*synthetic*/ static TreeMap$Entry access$300(TreeMap x0) {
        return x0.firstEntry();
    }
    
    /*synthetic*/ static int access$100(TreeMap x0) {
        return x0.size;
    }
    private Comparator comparator = null;
    private transient TreeMap$Entry root = null;
    private transient int size = 0;
    private transient int modCount = 0;
    
    private void incrementSize() {
        modCount++;
        size++;
    }
    
    private void decrementSize() {
        modCount++;
        size--;
    }
    
    public TreeMap() {
        
    }
    
    public TreeMap(Comparator c) {
        
        this.comparator = c;
    }
    
    public TreeMap(Map m) {
        
        putAll(m);
    }
    
    public TreeMap(SortedMap m) {
        
        comparator = m.comparator();
        try {
            buildFromSorted(m.size(), m.entrySet().iterator(), null, null);
        } catch (java.io.IOException cannotHappen) {
        } catch (ClassNotFoundException cannotHappen) {
        }
    }
    
    public int size() {
        return size;
    }
    
    public boolean containsKey(Object key) {
        return getEntry(key) != null;
    }
    
    public boolean containsValue(Object value) {
        return (root == null ? false : (value == null ? valueSearchNull(root) : valueSearchNonNull(root, value)));
    }
    
    private boolean valueSearchNull(TreeMap$Entry n) {
        if (n.value == null) return true;
        return (n.left != null && valueSearchNull(n.left)) || (n.right != null && valueSearchNull(n.right));
    }
    
    private boolean valueSearchNonNull(TreeMap$Entry n, Object value) {
        if (value.equals(n.value)) return true;
        return (n.left != null && valueSearchNonNull(n.left, value)) || (n.right != null && valueSearchNonNull(n.right, value));
    }
    
    public Object get(Object key) {
        TreeMap$Entry p = getEntry(key);
        return (p == null ? null : p.value);
    }
    
    public Comparator comparator() {
        return comparator;
    }
    
    public Object firstKey() {
        return key(firstEntry());
    }
    
    public Object lastKey() {
        return key(lastEntry());
    }
    
    public void putAll(Map map) {
        int mapSize = map.size();
        if (size == 0 && mapSize != 0 && map instanceof SortedMap) {
            Comparator c = ((SortedMap)(SortedMap)map).comparator();
            if (c == comparator || (c != null && c.equals(comparator))) {
                ++modCount;
                try {
                    buildFromSorted(mapSize, map.entrySet().iterator(), null, null);
                } catch (java.io.IOException cannotHappen) {
                } catch (ClassNotFoundException cannotHappen) {
                }
                return;
            }
        }
        super.putAll(map);
    }
    
    private TreeMap$Entry getEntry(Object key) {
        TreeMap$Entry p = root;
        Object k = (Object)key;
        while (p != null) {
            int cmp = compare(k, p.key);
            if (cmp == 0) return p; else if (cmp < 0) p = p.left; else p = p.right;
        }
        return null;
    }
    
    private TreeMap$Entry getCeilEntry(Object key) {
        TreeMap$Entry p = root;
        if (p == null) return null;
        while (true) {
            int cmp = compare(key, p.key);
            if (cmp == 0) {
                return p;
            } else if (cmp < 0) {
                if (p.left != null) p = p.left; else return p;
            } else {
                if (p.right != null) {
                    p = p.right;
                } else {
                    TreeMap$Entry parent = p.parent;
                    TreeMap$Entry ch = p;
                    while (parent != null && ch == parent.right) {
                        ch = parent;
                        parent = parent.parent;
                    }
                    return parent;
                }
            }
        }
    }
    
    private TreeMap$Entry getPrecedingEntry(Object key) {
        TreeMap$Entry p = root;
        if (p == null) return null;
        while (true) {
            int cmp = compare(key, p.key);
            if (cmp > 0) {
                if (p.right != null) p = p.right; else return p;
            } else {
                if (p.left != null) {
                    p = p.left;
                } else {
                    TreeMap$Entry parent = p.parent;
                    TreeMap$Entry ch = p;
                    while (parent != null && ch == parent.left) {
                        ch = parent;
                        parent = parent.parent;
                    }
                    return parent;
                }
            }
        }
    }
    
    private static Object key(TreeMap$Entry e) {
        if (e == null) throw new NoSuchElementException();
        return e.key;
    }
    
    public Object put(Object key, Object value) {
        TreeMap$Entry t = root;
        if (t == null) {
            incrementSize();
            root = new TreeMap$Entry(key, value, null);
            return null;
        }
        while (true) {
            int cmp = compare(key, t.key);
            if (cmp == 0) {
                return t.setValue(value);
            } else if (cmp < 0) {
                if (t.left != null) {
                    t = t.left;
                } else {
                    incrementSize();
                    t.left = new TreeMap$Entry(key, value, t);
                    fixAfterInsertion(t.left);
                    return null;
                }
            } else {
                if (t.right != null) {
                    t = t.right;
                } else {
                    incrementSize();
                    t.right = new TreeMap$Entry(key, value, t);
                    fixAfterInsertion(t.right);
                    return null;
                }
            }
        }
    }
    
    public Object remove(Object key) {
        TreeMap$Entry p = getEntry(key);
        if (p == null) return null;
        Object oldValue = p.value;
        deleteEntry(p);
        return oldValue;
    }
    
    public void clear() {
        modCount++;
        size = 0;
        root = null;
    }
    
    public Object clone() {
        TreeMap clone = null;
        try {
            clone = (TreeMap)(TreeMap)super.clone();
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
        clone.root = null;
        clone.size = 0;
        clone.modCount = 0;
        clone.entrySet = null;
        try {
            clone.buildFromSorted(size, entrySet().iterator(), null, null);
        } catch (java.io.IOException cannotHappen) {
        } catch (ClassNotFoundException cannotHappen) {
        }
        return clone;
    }
    private volatile transient Set entrySet = null;
    
    public Set keySet() {
        if (keySet == null) {
            keySet = new TreeMap$1(this);
        }
        return keySet;
    }
    
    public Collection values() {
        if (values == null) {
            values = new TreeMap$2(this);
        }
        return values;
    }
    
    public Set entrySet() {
        if (entrySet == null) {
            entrySet = new TreeMap$3(this);
        }
        return entrySet;
    }
    
    public SortedMap subMap(Object fromKey, Object toKey) {
        return new TreeMap$SubMap(this, fromKey, toKey);
    }
    
    public SortedMap headMap(Object toKey) {
        return new TreeMap$SubMap(this, toKey, true);
    }
    
    public SortedMap tailMap(Object fromKey) {
        return new TreeMap$SubMap(this, fromKey, false);
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    
    private int compare(Object k1, Object k2) {
        return (comparator == null ? ((Comparable)(Comparable)k1).compareTo(k2) : comparator.compare((Object)k1, (Object)k2));
    }
    
    private static boolean valEquals(Object o1, Object o2) {
        return (o1 == null ? o2 == null : o1.equals(o2));
    }
    private static final boolean RED = false;
    private static final boolean BLACK = true;
    {
    }
    
    private TreeMap$Entry firstEntry() {
        TreeMap$Entry p = root;
        if (p != null) while (p.left != null) p = p.left;
        return p;
    }
    
    private TreeMap$Entry lastEntry() {
        TreeMap$Entry p = root;
        if (p != null) while (p.right != null) p = p.right;
        return p;
    }
    
    private TreeMap$Entry successor(TreeMap$Entry t) {
        if (t == null) return null; else if (t.right != null) {
            TreeMap$Entry p = t.right;
            while (p.left != null) p = p.left;
            return p;
        } else {
            TreeMap$Entry p = t.parent;
            TreeMap$Entry ch = t;
            while (p != null && ch == p.right) {
                ch = p;
                p = p.parent;
            }
            return p;
        }
    }
    
    private static boolean colorOf(TreeMap$Entry p) {
        return (p == null ? BLACK : p.color);
    }
    
    private static TreeMap$Entry parentOf(TreeMap$Entry p) {
        return (p == null ? null : p.parent);
    }
    
    private static void setColor(TreeMap$Entry p, boolean c) {
        if (p != null) p.color = c;
    }
    
    private static TreeMap$Entry leftOf(TreeMap$Entry p) {
        return (p == null) ? null : p.left;
    }
    
    private static TreeMap$Entry rightOf(TreeMap$Entry p) {
        return (p == null) ? null : p.right;
    }
    
    private void rotateLeft(TreeMap$Entry p) {
        TreeMap$Entry r = p.right;
        p.right = r.left;
        if (r.left != null) r.left.parent = p;
        r.parent = p.parent;
        if (p.parent == null) root = r; else if (p.parent.left == p) p.parent.left = r; else p.parent.right = r;
        r.left = p;
        p.parent = r;
    }
    
    private void rotateRight(TreeMap$Entry p) {
        TreeMap$Entry l = p.left;
        p.left = l.right;
        if (l.right != null) l.right.parent = p;
        l.parent = p.parent;
        if (p.parent == null) root = l; else if (p.parent.right == p) p.parent.right = l; else p.parent.left = l;
        l.right = p;
        p.parent = l;
    }
    
    private void fixAfterInsertion(TreeMap$Entry x) {
        x.color = RED;
        while (x != null && x != root && x.parent.color == RED) {
            if (parentOf(x) == leftOf(parentOf(parentOf(x)))) {
                TreeMap$Entry y = rightOf(parentOf(parentOf(x)));
                if (colorOf(y) == RED) {
                    setColor(parentOf(x), BLACK);
                    setColor(y, BLACK);
                    setColor(parentOf(parentOf(x)), RED);
                    x = parentOf(parentOf(x));
                } else {
                    if (x == rightOf(parentOf(x))) {
                        x = parentOf(x);
                        rotateLeft(x);
                    }
                    setColor(parentOf(x), BLACK);
                    setColor(parentOf(parentOf(x)), RED);
                    if (parentOf(parentOf(x)) != null) rotateRight(parentOf(parentOf(x)));
                }
            } else {
                TreeMap$Entry y = leftOf(parentOf(parentOf(x)));
                if (colorOf(y) == RED) {
                    setColor(parentOf(x), BLACK);
                    setColor(y, BLACK);
                    setColor(parentOf(parentOf(x)), RED);
                    x = parentOf(parentOf(x));
                } else {
                    if (x == leftOf(parentOf(x))) {
                        x = parentOf(x);
                        rotateRight(x);
                    }
                    setColor(parentOf(x), BLACK);
                    setColor(parentOf(parentOf(x)), RED);
                    if (parentOf(parentOf(x)) != null) rotateLeft(parentOf(parentOf(x)));
                }
            }
        }
        root.color = BLACK;
    }
    
    private void deleteEntry(TreeMap$Entry p) {
        decrementSize();
        if (p.left != null && p.right != null) {
            TreeMap$Entry s = successor(p);
            p.key = s.key;
            p.value = s.value;
            p = s;
        }
        TreeMap$Entry replacement = (p.left != null ? p.left : p.right);
        if (replacement != null) {
            replacement.parent = p.parent;
            if (p.parent == null) root = replacement; else if (p == p.parent.left) p.parent.left = replacement; else p.parent.right = replacement;
            p.left = p.right = p.parent = null;
            if (p.color == BLACK) fixAfterDeletion(replacement);
        } else if (p.parent == null) {
            root = null;
        } else {
            if (p.color == BLACK) fixAfterDeletion(p);
            if (p.parent != null) {
                if (p == p.parent.left) p.parent.left = null; else if (p == p.parent.right) p.parent.right = null;
                p.parent = null;
            }
        }
    }
    
    private void fixAfterDeletion(TreeMap$Entry x) {
        while (x != root && colorOf(x) == BLACK) {
            if (x == leftOf(parentOf(x))) {
                TreeMap$Entry sib = rightOf(parentOf(x));
                if (colorOf(sib) == RED) {
                    setColor(sib, BLACK);
                    setColor(parentOf(x), RED);
                    rotateLeft(parentOf(x));
                    sib = rightOf(parentOf(x));
                }
                if (colorOf(leftOf(sib)) == BLACK && colorOf(rightOf(sib)) == BLACK) {
                    setColor(sib, RED);
                    x = parentOf(x);
                } else {
                    if (colorOf(rightOf(sib)) == BLACK) {
                        setColor(leftOf(sib), BLACK);
                        setColor(sib, RED);
                        rotateRight(sib);
                        sib = rightOf(parentOf(x));
                    }
                    setColor(sib, colorOf(parentOf(x)));
                    setColor(parentOf(x), BLACK);
                    setColor(rightOf(sib), BLACK);
                    rotateLeft(parentOf(x));
                    x = root;
                }
            } else {
                TreeMap$Entry sib = leftOf(parentOf(x));
                if (colorOf(sib) == RED) {
                    setColor(sib, BLACK);
                    setColor(parentOf(x), RED);
                    rotateRight(parentOf(x));
                    sib = leftOf(parentOf(x));
                }
                if (colorOf(rightOf(sib)) == BLACK && colorOf(leftOf(sib)) == BLACK) {
                    setColor(sib, RED);
                    x = parentOf(x);
                } else {
                    if (colorOf(leftOf(sib)) == BLACK) {
                        setColor(rightOf(sib), BLACK);
                        setColor(sib, RED);
                        rotateLeft(sib);
                        sib = leftOf(parentOf(x));
                    }
                    setColor(sib, colorOf(parentOf(x)));
                    setColor(parentOf(x), BLACK);
                    setColor(leftOf(sib), BLACK);
                    rotateRight(parentOf(x));
                    x = root;
                }
            }
        }
        setColor(x, BLACK);
    }
    private static final long serialVersionUID = 919286545866124006L;
    
    private void writeObject(java.io.ObjectOutputStream s) throws java.io.IOException {
        s.defaultWriteObject();
        s.writeInt(size);
        for (Iterator i = entrySet().iterator(); i.hasNext(); ) {
            Map$Entry e = (Map$Entry)i.next();
            s.writeObject(e.getKey());
            s.writeObject(e.getValue());
        }
    }
    
    private void readObject(final java.io.ObjectInputStream s) throws java.io.IOException, ClassNotFoundException {
        s.defaultReadObject();
        int size = s.readInt();
        buildFromSorted(size, null, s, null);
    }
    
    void readTreeSet(int size, java.io.ObjectInputStream s, Object defaultVal) throws java.io.IOException, ClassNotFoundException {
        buildFromSorted(size, null, s, defaultVal);
    }
    
    void addAllForTreeSet(SortedSet set, Object defaultVal) {
        try {
            buildFromSorted(set.size(), set.iterator(), null, defaultVal);
        } catch (java.io.IOException cannotHappen) {
        } catch (ClassNotFoundException cannotHappen) {
        }
    }
    
    private void buildFromSorted(int size, Iterator it, java.io.ObjectInputStream str, Object defaultVal) throws java.io.IOException, ClassNotFoundException {
        this.size = size;
        root = buildFromSorted(0, 0, size - 1, computeRedLevel(size), it, str, defaultVal);
    }
    
    private final TreeMap$Entry buildFromSorted(int level, int lo, int hi, int redLevel, Iterator it, java.io.ObjectInputStream str, Object defaultVal) throws java.io.IOException, ClassNotFoundException {
        if (hi < lo) return null;
        int mid = (lo + hi) / 2;
        TreeMap$Entry left = null;
        if (lo < mid) left = buildFromSorted(level + 1, lo, mid - 1, redLevel, it, str, defaultVal);
        Object key;
        Object value;
        if (it != null) {
            if (defaultVal == null) {
                Map$Entry entry = (Map$Entry)(Map$Entry)it.next();
                key = entry.getKey();
                value = entry.getValue();
            } else {
                key = (Object)it.next();
                value = defaultVal;
            }
        } else {
            key = (Object)str.readObject();
            value = (defaultVal != null ? defaultVal : (Object)str.readObject());
        }
        TreeMap$Entry middle = new TreeMap$Entry(key, value, null);
        if (level == redLevel) middle.color = RED;
        if (left != null) {
            middle.left = left;
            left.parent = middle;
        }
        if (mid < hi) {
            TreeMap$Entry right = buildFromSorted(level + 1, mid + 1, hi, redLevel, it, str, defaultVal);
            middle.right = right;
            right.parent = middle;
        }
        return middle;
    }
    
    private static int computeRedLevel(int sz) {
        int level = 0;
        for (int m = sz - 1; m >= 0; m = m / 2 - 1) level++;
        return level;
    }
}
