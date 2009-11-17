package java.awt;

public final class JobAttributes$DefaultSelectionType extends AttributeValue {
    private static final int I_ALL = 0;
    private static final int I_RANGE = 1;
    private static final int I_SELECTION = 2;
    private static final String[] NAMES = {"all", "range", "selection"};
    public static final JobAttributes$DefaultSelectionType ALL = new JobAttributes$DefaultSelectionType(I_ALL);
    public static final JobAttributes$DefaultSelectionType RANGE = new JobAttributes$DefaultSelectionType(I_RANGE);
    public static final JobAttributes$DefaultSelectionType SELECTION = new JobAttributes$DefaultSelectionType(I_SELECTION);
    
    private JobAttributes$DefaultSelectionType(int type) {
        super(type, NAMES);
    }
}
