package java.awt;

public final class BufferCapabilities$FlipContents extends AttributeValue {
    private static int I_UNDEFINED = 0;
    private static int I_BACKGROUND = 1;
    private static int I_PRIOR = 2;
    private static int I_COPIED = 3;
    private static final String[] NAMES = {"undefined", "background", "prior", "copied"};
    public static final BufferCapabilities$FlipContents UNDEFINED = new BufferCapabilities$FlipContents(I_UNDEFINED);
    public static final BufferCapabilities$FlipContents BACKGROUND = new BufferCapabilities$FlipContents(I_BACKGROUND);
    public static final BufferCapabilities$FlipContents PRIOR = new BufferCapabilities$FlipContents(I_PRIOR);
    public static final BufferCapabilities$FlipContents COPIED = new BufferCapabilities$FlipContents(I_COPIED);
    
    private BufferCapabilities$FlipContents(int type) {
        super(type, NAMES);
    }
}
