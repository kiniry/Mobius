package javax.sound.sampled;

public class LineEvent extends java.util.EventObject {
    private final LineEvent$Type type;
    private final long position;
    
    public LineEvent(Line line, LineEvent$Type type, long position) {
        super(line);
        this.type = type;
        this.position = position;
    }
    
    public final Line getLine() {
        return (Line)(Line)getSource();
    }
    
    public final LineEvent$Type getType() {
        return type;
    }
    
    public final long getFramePosition() {
        return position;
    }
    
    public String toString() {
        String sType = "";
        if (type != null) sType = type.toString() + " ";
        String sLine;
        if (getLine() == null) {
            sLine = "null";
        } else {
            sLine = getLine().toString();
        }
        return new String(sType + "event from line " + sLine);
    }
    {
    }
}
