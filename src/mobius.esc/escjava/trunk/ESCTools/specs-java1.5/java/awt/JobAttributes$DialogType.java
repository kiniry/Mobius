package java.awt;

public final class JobAttributes$DialogType extends AttributeValue {
    private static final int I_COMMON = 0;
    private static final int I_NATIVE = 1;
    private static final int I_NONE = 2;
    private static final String[] NAMES = {"common", "native", "none"};
    public static final JobAttributes$DialogType COMMON = new JobAttributes$DialogType(I_COMMON);
    public static final JobAttributes$DialogType NATIVE = new JobAttributes$DialogType(I_NATIVE);
    public static final JobAttributes$DialogType NONE = new JobAttributes$DialogType(I_NONE);
    
    private JobAttributes$DialogType(int type) {
        super(type, NAMES);
    }
}
