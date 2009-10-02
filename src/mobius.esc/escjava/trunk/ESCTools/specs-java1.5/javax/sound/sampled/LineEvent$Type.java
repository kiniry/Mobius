package javax.sound.sampled;

public class LineEvent$Type {
    private String name;
    
    protected LineEvent$Type(String name) {
        
        this.name = name;
    }
    
    public final boolean equals(Object obj) {
        return super.equals(obj);
    }
    
    public final int hashCode() {
        return super.hashCode();
    }
    
    public String toString() {
        return name;
    }
    public static final LineEvent$Type OPEN = new LineEvent$Type("Open");
    public static final LineEvent$Type CLOSE = new LineEvent$Type("Close");
    public static final LineEvent$Type START = new LineEvent$Type("Start");
    public static final LineEvent$Type STOP = new LineEvent$Type("Stop");
}
