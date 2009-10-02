package java.util;

class EnumSet$SerializationProxy implements java.io.Serializable {
    private final Class elementType;
    private final Enum[] elements;
    
    EnumSet$SerializationProxy(EnumSet set) {
        
        elementType = set.elementType;
        elements = (Enum[])(Enum[])set.toArray(EnumSet.access$000());
    }
    
    private Object readResolve() {
        EnumSet result = EnumSet.noneOf(elementType);
        for (Enum[] arr$ = elements, len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
            Enum e = arr$[i$];
            result.add((Enum)e);
        }
        return result;
    }
    private static final long serialVersionUID = 362491234563181265L;
}
