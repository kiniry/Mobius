package java.lang;

public class EnumConstantNotPresentException extends RuntimeException {
    private Class enumType;
    private String constantName;
    
    public EnumConstantNotPresentException(Class enumType, String constantName) {
        super(enumType.getName() + "." + constantName);
        this.enumType = enumType;
        this.constantName = constantName;
    }
    
    public Class enumType() {
        return enumType;
    }
    
    public String constantName() {
        return constantName;
    }
}
