package java.awt;

public final class PageAttributes$ColorType extends AttributeValue {
    private static final int I_COLOR = 0;
    private static final int I_MONOCHROME = 1;
    private static final String[] NAMES = {"color", "monochrome"};
    public static final PageAttributes$ColorType COLOR = new PageAttributes$ColorType(I_COLOR);
    public static final PageAttributes$ColorType MONOCHROME = new PageAttributes$ColorType(I_MONOCHROME);
    
    private PageAttributes$ColorType(int type) {
        super(type, NAMES);
    }
}
