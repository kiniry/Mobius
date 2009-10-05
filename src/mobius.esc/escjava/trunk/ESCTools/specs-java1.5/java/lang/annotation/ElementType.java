package java.lang.annotation;

public class ElementType extends Enum {
    public static final ElementType TYPE = new ElementType("TYPE", 0);
    public static final ElementType FIELD  = new ElementType("FIELD", 1);
    public static final ElementType METHOD  = new ElementType("METHOD", 2);
    public static final ElementType PARAMETER  = new ElementType("PARAMETER", 3);
    public static final ElementType CONSTRUCTOR  = new ElementType("CONSTRUCTOR", 4);
    public static final ElementType LOCAL_VARIABLE  = new ElementType("LOCAL_VARIABLE", 5);
    public static final ElementType ANNOTATION_TYPE  = new ElementType("ANNOTATION_TYPE", 6);
    public static final ElementType PACKAGE = new ElementType("PACKAGE", 7);
    /*synthetic*/ private static final ElementType[] $VALUES = new ElementType[]{ElementType.TYPE, ElementType.FIELD, ElementType.METHOD, ElementType.PARAMETER, ElementType.CONSTRUCTOR, ElementType.LOCAL_VARIABLE, ElementType.ANNOTATION_TYPE, ElementType.PACKAGE};
    
    public static final ElementType[] values() {
        return (ElementType[])$VALUES.clone();
    }
    
    public static ElementType valueOf(String name) {
        return (ElementType)Enum.valueOf(ElementType.class, name);
    }
    
    private ElementType(/*synthetic*/ String $enum$name, /*synthetic*/ int $enum$ordinal) {
        super($enum$name, $enum$ordinal);
    }
}
