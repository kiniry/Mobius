package java.awt;

public final class JobAttributes$SidesType extends AttributeValue {
    private static final int I_ONE_SIDED = 0;
    private static final int I_TWO_SIDED_LONG_EDGE = 1;
    private static final int I_TWO_SIDED_SHORT_EDGE = 2;
    private static final String[] NAMES = {"one-sided", "two-sided-long-edge", "two-sided-short-edge"};
    public static final JobAttributes$SidesType ONE_SIDED = new JobAttributes$SidesType(I_ONE_SIDED);
    public static final JobAttributes$SidesType TWO_SIDED_LONG_EDGE = new JobAttributes$SidesType(I_TWO_SIDED_LONG_EDGE);
    public static final JobAttributes$SidesType TWO_SIDED_SHORT_EDGE = new JobAttributes$SidesType(I_TWO_SIDED_SHORT_EDGE);
    
    private JobAttributes$SidesType(int type) {
        super(type, NAMES);
    }
}
