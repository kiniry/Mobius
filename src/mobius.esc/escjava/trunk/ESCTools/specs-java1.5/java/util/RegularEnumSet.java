package java.util;

class RegularEnumSet extends EnumSet {
    
    /*synthetic*/ static long access$022(RegularEnumSet x0, long x1) {
        return x0.elements -= x1;
    }
    
    /*synthetic*/ static long access$000(RegularEnumSet x0) {
        return x0.elements;
    }
    private long elements = 0L;
    
    RegularEnumSet(Class elementType, Enum[] universe) {
        super(elementType, universe);
    }
    
    void addRange(Enum from, Enum to) {
        elements = (-1L >>> (from.ordinal() - to.ordinal() - 1)) << from.ordinal();
    }
    
    void addAll() {
        if (universe.length != 0) elements = -1L >>> -universe.length;
    }
    
    void complement() {
        if (universe.length != 0) {
            elements = ~elements;
            elements &= -1L >>> -universe.length;
        }
    }
    
    public Iterator iterator() {
        return new RegularEnumSet$EnumSetIterator(this);
    }
    {
    }
    
    public int size() {
        return Long.bitCount(elements);
    }
    
    public boolean isEmpty() {
        return elements == 0;
    }
    
    public boolean contains(Object e) {
        if (e == null) return false;
        Class eClass = e.getClass();
        if (eClass != elementType && eClass.getSuperclass() != elementType) return false;
        return (elements & (1L << ((Enum)(Enum)e).ordinal())) != 0;
    }
    
    public boolean add(Enum e) {
        typeCheck(e);
        long oldElements = elements;
        elements |= (1L << ((Enum)e).ordinal());
        return elements != oldElements;
    }
    
    public boolean remove(Object e) {
        if (e == null) return false;
        Class eClass = e.getClass();
        if (eClass != elementType && eClass.getSuperclass() != elementType) return false;
        long oldElements = elements;
        elements &= ~(1L << ((Enum)(Enum)e).ordinal());
        return elements != oldElements;
    }
    
    public boolean containsAll(Collection c) {
        if (!(c instanceof RegularEnumSet)) return super.containsAll(c);
        RegularEnumSet es = (RegularEnumSet)(RegularEnumSet)c;
        if (es.elementType != elementType) return es.isEmpty();
        return (es.elements & ~elements) == 0;
    }
    
    public boolean addAll(Collection c) {
        if (!(c instanceof RegularEnumSet)) return super.addAll(c);
        RegularEnumSet es = (RegularEnumSet)(RegularEnumSet)c;
        if (es.elementType != elementType) {
            if (es.isEmpty()) return false; else throw new ClassCastException(es.elementType + " != " + elementType);
        }
        long oldElements = elements;
        elements |= es.elements;
        return elements != oldElements;
    }
    
    public boolean removeAll(Collection c) {
        if (!(c instanceof RegularEnumSet)) return super.removeAll(c);
        RegularEnumSet es = (RegularEnumSet)(RegularEnumSet)c;
        if (es.elementType != elementType) return false;
        long oldElements = elements;
        elements &= ~es.elements;
        return elements != oldElements;
    }
    
    public boolean retainAll(Collection c) {
        if (!(c instanceof RegularEnumSet)) return super.retainAll(c);
        RegularEnumSet es = (RegularEnumSet)(RegularEnumSet)c;
        if (es.elementType != elementType) {
            elements = 0;
            return true;
        }
        long oldElements = elements;
        elements &= es.elements;
        return elements != oldElements;
    }
    
    public void clear() {
        elements = 0;
    }
    
    public boolean equals(Object o) {
        if (!(o instanceof RegularEnumSet)) return super.equals(o);
        RegularEnumSet es = (RegularEnumSet)(RegularEnumSet)o;
        if (es.elementType != elementType) return elements == 0 && es.elements == 0;
        return es.elements == elements;
    }
    
    /*synthetic*/ public boolean add(Object x0) {
        return this.add((Enum)x0);
    }
}
