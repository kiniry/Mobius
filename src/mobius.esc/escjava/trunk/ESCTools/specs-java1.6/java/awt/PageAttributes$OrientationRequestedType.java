package java.awt;

public final class PageAttributes$OrientationRequestedType extends AttributeValue {
    private static final int I_PORTRAIT = 0;
    private static final int I_LANDSCAPE = 1;
    private static final String[] NAMES = {"portrait", "landscape"};
    public static final PageAttributes$OrientationRequestedType PORTRAIT = new PageAttributes$OrientationRequestedType(I_PORTRAIT);
    public static final PageAttributes$OrientationRequestedType LANDSCAPE = new PageAttributes$OrientationRequestedType(I_LANDSCAPE);
    
    private PageAttributes$OrientationRequestedType(int type) {
        super(type, NAMES);
    }
}
