package javax.swing.text;

import javax.swing.event.*;

public class DefaultStyledDocument$ElementSpec {
    public static final short StartTagType = 1;
    public static final short EndTagType = 2;
    public static final short ContentType = 3;
    public static final short JoinPreviousDirection = 4;
    public static final short JoinNextDirection = 5;
    public static final short OriginateDirection = 6;
    public static final short JoinFractureDirection = 7;
    
    public DefaultStyledDocument$ElementSpec(AttributeSet a, short type) {
        this(a, type, null, 0, 0);
    }
    
    public DefaultStyledDocument$ElementSpec(AttributeSet a, short type, int len) {
        this(a, type, null, 0, len);
    }
    
    public DefaultStyledDocument$ElementSpec(AttributeSet a, short type, char[] txt, int offs, int len) {
        
        attr = a;
        this.type = type;
        this.data = txt;
        this.offs = offs;
        this.len = len;
        this.direction = OriginateDirection;
    }
    
    public void setType(short type) {
        this.type = type;
    }
    
    public short getType() {
        return type;
    }
    
    public void setDirection(short direction) {
        this.direction = direction;
    }
    
    public short getDirection() {
        return direction;
    }
    
    public AttributeSet getAttributes() {
        return attr;
    }
    
    public char[] getArray() {
        return data;
    }
    
    public int getOffset() {
        return offs;
    }
    
    public int getLength() {
        return len;
    }
    
    public String toString() {
        String tlbl = "??";
        String plbl = "??";
        switch (type) {
        case StartTagType: 
            tlbl = "StartTag";
            break;
        
        case ContentType: 
            tlbl = "Content";
            break;
        
        case EndTagType: 
            tlbl = "EndTag";
            break;
        
        }
        switch (direction) {
        case JoinPreviousDirection: 
            plbl = "JoinPrevious";
            break;
        
        case JoinNextDirection: 
            plbl = "JoinNext";
            break;
        
        case OriginateDirection: 
            plbl = "Originate";
            break;
        
        case JoinFractureDirection: 
            plbl = "Fracture";
            break;
        
        }
        return tlbl + ":" + plbl + ":" + getLength();
    }
    private AttributeSet attr;
    private int len;
    private short type;
    private short direction;
    private int offs;
    private char[] data;
}
