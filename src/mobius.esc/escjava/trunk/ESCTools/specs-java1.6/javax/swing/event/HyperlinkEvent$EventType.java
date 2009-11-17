package javax.swing.event;

public final class HyperlinkEvent$EventType {
    
    private HyperlinkEvent$EventType(String s) {
        
        typeString = s;
    }
    public static final HyperlinkEvent$EventType ENTERED = new HyperlinkEvent$EventType("ENTERED");
    public static final HyperlinkEvent$EventType EXITED = new HyperlinkEvent$EventType("EXITED");
    public static final HyperlinkEvent$EventType ACTIVATED = new HyperlinkEvent$EventType("ACTIVATED");
    
    public String toString() {
        return typeString;
    }
    private String typeString;
}
