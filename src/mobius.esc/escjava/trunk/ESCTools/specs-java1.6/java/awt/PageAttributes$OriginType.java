package java.awt;

public final class PageAttributes$OriginType extends AttributeValue {
    private static final int I_PHYSICAL = 0;
    private static final int I_PRINTABLE = 1;
    private static final String[] NAMES = {"physical", "printable"};
    public static final PageAttributes$OriginType PHYSICAL = new PageAttributes$OriginType(I_PHYSICAL);
    public static final PageAttributes$OriginType PRINTABLE = new PageAttributes$OriginType(I_PRINTABLE);
    
    private PageAttributes$OriginType(int type) {
        super(type, NAMES);
    }
}
