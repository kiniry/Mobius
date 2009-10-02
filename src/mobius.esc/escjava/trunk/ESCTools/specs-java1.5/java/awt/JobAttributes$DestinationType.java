package java.awt;

public final class JobAttributes$DestinationType extends AttributeValue {
    private static final int I_FILE = 0;
    private static final int I_PRINTER = 1;
    private static final String[] NAMES = {"file", "printer"};
    public static final JobAttributes$DestinationType FILE = new JobAttributes$DestinationType(I_FILE);
    public static final JobAttributes$DestinationType PRINTER = new JobAttributes$DestinationType(I_PRINTER);
    
    private JobAttributes$DestinationType(int type) {
        super(type, NAMES);
    }
}
