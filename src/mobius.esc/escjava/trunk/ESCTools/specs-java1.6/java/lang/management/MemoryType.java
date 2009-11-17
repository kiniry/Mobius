package java.lang.management;

public class MemoryType extends Enum {
    public static final MemoryType HEAP = new MemoryType("HEAP", 0, "Heap memory");
    public static final MemoryType NON_HEAP = new MemoryType("NON_HEAP", 1, "Non-heap memory");
    /*synthetic*/ private static final MemoryType[] $VALUES = new MemoryType[]{MemoryType.HEAP, MemoryType.NON_HEAP};
    
    public static final MemoryType[] values() {
        return (MemoryType[])$VALUES.clone();
    }
    
    public static MemoryType valueOf(String name) {
        return (MemoryType)Enum.valueOf(MemoryType.class, name);
    }
    private final String description;
    
    private MemoryType(/*synthetic*/ String $enum$name, /*synthetic*/ int $enum$ordinal, String s) {
        super($enum$name, $enum$ordinal);
        this.description = s;
    }
    
    public String toString() {
        return description;
    }
    private static final long serialVersionUID = 6992337162326171013L;
}
