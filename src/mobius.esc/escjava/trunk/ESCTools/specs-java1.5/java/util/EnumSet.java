package java.util;

public abstract class EnumSet extends AbstractSet implements Cloneable, java.io.Serializable {
    
    /*synthetic*/ static Enum[] access$000() {
        return ZERO_LENGTH_ENUM_ARRAY;
    }
    final Class elementType;
    final Enum[] universe;
    private static Enum[] ZERO_LENGTH_ENUM_ARRAY = new Enum[0];
    
    EnumSet(Class elementType, Enum[] universe) {
        
        this.elementType = elementType;
        this.universe = universe;
    }
    
    public static EnumSet noneOf(Class elementType) {
        Enum[] universe = (Enum[])elementType.getEnumConstants();
        if (universe == null) throw new ClassCastException(elementType + " not an enum");
        if (universe.length <= 64) return new RegularEnumSet(elementType, universe); else return new JumboEnumSet(elementType, universe);
    }
    
    public static EnumSet allOf(Class elementType) {
        EnumSet result = noneOf(elementType);
        result.addAll();
        return result;
    }
    
    abstract void addAll();
    
    public static EnumSet copyOf(EnumSet s) {
        return s.clone();
    }
    
    public static EnumSet copyOf(Collection c) {
        if (c instanceof EnumSet) {
            return ((EnumSet)(EnumSet)c).clone();
        } else {
            if (c.isEmpty()) throw new IllegalArgumentException("Collection is empty");
            Iterator i = c.iterator();
            Enum first = (Enum)i.next();
            EnumSet result = EnumSet.of(first);
            while (i.hasNext()) result.add(i.next());
            return result;
        }
    }
    
    public static EnumSet complementOf(EnumSet s) {
        EnumSet result = copyOf(s);
        result.complement();
        return result;
    }
    
    public static EnumSet of(Enum e) {
        EnumSet result = noneOf(e.getDeclaringClass());
        result.add(e);
        return result;
    }
    
    public static EnumSet of(Enum e1, Enum e2) {
        EnumSet result = noneOf(e1.getDeclaringClass());
        result.add(e1);
        result.add(e2);
        return result;
    }
    
    public static EnumSet of(Enum e1, Enum e2, Enum e3) {
        EnumSet result = noneOf(e1.getDeclaringClass());
        result.add(e1);
        result.add(e2);
        result.add(e3);
        return result;
    }
    
    public static EnumSet of(Enum e1, Enum e2, Enum e3, Enum e4) {
        EnumSet result = noneOf(e1.getDeclaringClass());
        result.add(e1);
        result.add(e2);
        result.add(e3);
        result.add(e4);
        return result;
    }
    
    public static EnumSet of(Enum e1, Enum e2, Enum e3, Enum e4, Enum e5) {
        EnumSet result = noneOf(e1.getDeclaringClass());
        result.add(e1);
        result.add(e2);
        result.add(e3);
        result.add(e4);
        result.add(e5);
        return result;
    }
    
    public static EnumSet of(Enum first, Enum[] rest) {
        EnumSet result = noneOf(first.getDeclaringClass());
        result.add(first);
        for (Enum[] arr$ = rest, len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
            Enum e = arr$[i$];
            result.add(e);
        }
        return result;
    }
    
    public static EnumSet range(Enum from, Enum to) {
        if (from.compareTo(to) > 0) throw new IllegalArgumentException(from + " > " + to);
        EnumSet result = noneOf(from.getDeclaringClass());
        result.addRange(from, to);
        return result;
    }
    
    abstract void addRange(Enum from, Enum to);
    
    public EnumSet clone() {
        try {
            return (EnumSet)(EnumSet)super.clone();
        } catch (CloneNotSupportedException e) {
            throw new AssertionError(e);
        }
    }
    
    abstract void complement();
    
    final void typeCheck(Enum e) {
        Class eClass = e.getClass();
        if (eClass != elementType && eClass.getSuperclass() != elementType) throw new ClassCastException(eClass + " != " + elementType);
    }
    {
    }
    
    Object writeReplace() {
        return new EnumSet$SerializationProxy(this);
    }
    
    /*synthetic public Object clone() throws CloneNotSupportedException {
        return this.clone();
    } */
}
