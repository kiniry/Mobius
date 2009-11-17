package java.util;

class JumboEnumSet extends EnumSet {
    
    /*synthetic*/ static int access$110(JumboEnumSet x0) {
        return x0.size--;
    }
    
    /*synthetic*/ static long[] access$000(JumboEnumSet x0) {
        return x0.elements;
    }
    private long[] elements;
    private int size = 0;
    
    JumboEnumSet(Class elementType, Enum[] universe) {
        super(elementType, universe);
        elements = new long[(universe.length + 63) >>> 6];
    }
    
    void addRange(Enum from, Enum to) {
        int fromIndex = from.ordinal() >>> 6;
        int toIndex = to.ordinal() >>> 6;
        if (fromIndex == toIndex) {
            elements[fromIndex] = (-1L >>> (from.ordinal() - to.ordinal() - 1)) << from.ordinal();
        } else {
            elements[fromIndex] = (-1L << from.ordinal());
            for (int i = fromIndex + 1; i < toIndex; i++) elements[i] = -1;
            elements[toIndex] = -1L >>> (63 - to.ordinal());
        }
        size = to.ordinal() - from.ordinal() + 1;
    }
    
    void addAll() {
        for (int i = 0; i < elements.length; i++) elements[i] = -1;
        elements[elements.length - 1] >>>= -universe.length;
        size = universe.length;
    }
    
    void complement() {
        for (int i = 0; i < elements.length; i++) elements[i] = ~elements[i];
        elements[elements.length - 1] &= (-1L >>> -universe.length);
        size = universe.length - size;
    }
    
    public Iterator iterator() {
        return new JumboEnumSet$EnumSetIterator(this);
    }
    {
    }
    
    public int size() {
        return size;
    }
    
    public boolean isEmpty() {
        return size == 0;
    }
    
    public boolean contains(Object e) {
        if (e == null) return false;
        Class eClass = e.getClass();
        if (eClass != elementType && eClass.getSuperclass() != elementType) return false;
        int eOrdinal = ((Enum)(Enum)e).ordinal();
        return (elements[eOrdinal >>> 6] & (1L << eOrdinal)) != 0;
    }
    
    public boolean add(Enum e) {
        typeCheck(e);
        int eOrdinal = e.ordinal();
        int eWordNum = eOrdinal >>> 6;
        long oldElements = elements[eWordNum];
        elements[eWordNum] |= (1L << eOrdinal);
        boolean result = (elements[eWordNum] != oldElements);
        if (result) size++;
        return result;
    }
    
    public boolean remove(Object e) {
        if (e == null) return false;
        Class eClass = e.getClass();
        if (eClass != elementType && eClass.getSuperclass() != elementType) return false;
        int eOrdinal = ((Enum)(Enum)e).ordinal();
        int eWordNum = eOrdinal >>> 6;
        long oldElements = elements[eWordNum];
        elements[eWordNum] &= ~(1L << eOrdinal);
        boolean result = (elements[eWordNum] != oldElements);
        if (result) size--;
        return result;
    }
    
    public boolean containsAll(Collection c) {
        if (!(c instanceof JumboEnumSet)) return super.containsAll(c);
        JumboEnumSet es = (JumboEnumSet)(JumboEnumSet)c;
        if (es.elementType != elementType) return es.isEmpty();
        for (int i = 0; i < elements.length; i++) if ((es.elements[i] & ~elements[i]) != 0) return false;
        return true;
    }
    
    public boolean addAll(Collection c) {
        if (!(c instanceof JumboEnumSet)) return super.addAll(c);
        JumboEnumSet es = (JumboEnumSet)(JumboEnumSet)c;
        if (es.elementType != elementType) {
            if (es.isEmpty()) return false; else throw new ClassCastException(es.elementType + " != " + elementType);
        }
        for (int i = 0; i < elements.length; i++) elements[i] |= es.elements[i];
        return recalculateSize();
    }
    
    public boolean removeAll(Collection c) {
        if (!(c instanceof JumboEnumSet)) return super.removeAll(c);
        JumboEnumSet es = (JumboEnumSet)(JumboEnumSet)c;
        if (es.elementType != elementType) return false;
        for (int i = 0; i < elements.length; i++) elements[i] &= ~es.elements[i];
        return recalculateSize();
    }
    
    public boolean retainAll(Collection c) {
        if (!(c instanceof JumboEnumSet)) return super.retainAll(c);
        JumboEnumSet es = (JumboEnumSet)(JumboEnumSet)c;
        if (es.elementType != elementType) {
            clear();
            return true;
        }
        for (int i = 0; i < elements.length; i++) elements[i] &= es.elements[i];
        return recalculateSize();
    }
    
    public void clear() {
        Arrays.fill(elements, 0);
        size = 0;
    }
    
    public boolean equals(Object o) {
        if (!(o instanceof JumboEnumSet)) return super.equals(o);
        JumboEnumSet es = (JumboEnumSet)(JumboEnumSet)o;
        if (es.elementType != elementType) return size == 0 && es.size == 0;
        return Arrays.equals(es.elements, elements);
    }
    
    private boolean recalculateSize() {
        int oldSize = size;
        size = 0;
        for (long[] arr$ = elements, len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
            long elt = arr$[i$];
            size += Long.bitCount(elt);
        }
        return size != oldSize;
    }
    
    public EnumSet clone() {
        JumboEnumSet result = (JumboEnumSet)(JumboEnumSet)super.clone();
        result.elements = (long[])(long[])result.elements.clone();
        return result;
    }
    
    /*synthetic  public boolean add(Object x0) {
        return this.add((Enum)x0);
    } */
    
    /*synthetic public Object clone() throws CloneNotSupportedException {
        return this.clone();
    } */
}
