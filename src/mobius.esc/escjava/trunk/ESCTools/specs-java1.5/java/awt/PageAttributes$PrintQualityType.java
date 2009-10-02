package java.awt;

public final class PageAttributes$PrintQualityType extends AttributeValue {
    private static final int I_HIGH = 0;
    private static final int I_NORMAL = 1;
    private static final int I_DRAFT = 2;
    private static final String[] NAMES = {"high", "normal", "draft"};
    public static final PageAttributes$PrintQualityType HIGH = new PageAttributes$PrintQualityType(I_HIGH);
    public static final PageAttributes$PrintQualityType NORMAL = new PageAttributes$PrintQualityType(I_NORMAL);
    public static final PageAttributes$PrintQualityType DRAFT = new PageAttributes$PrintQualityType(I_DRAFT);
    
    private PageAttributes$PrintQualityType(int type) {
        super(type, NAMES);
    }
}
