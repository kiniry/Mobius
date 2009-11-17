package java.awt.event;

import java.awt.AWTEvent;

public class TextEvent extends AWTEvent {
    public static final int TEXT_FIRST = 900;
    public static final int TEXT_LAST = 900;
    public static final int TEXT_VALUE_CHANGED = TEXT_FIRST;
    private static final long serialVersionUID = 6269902291250941179L;
    
    public TextEvent(Object source, int id) {
        super(source, id);
    }
    
    public String paramString() {
        String typeStr;
        switch (id) {
        case TEXT_VALUE_CHANGED: 
            typeStr = "TEXT_VALUE_CHANGED";
            break;
        
        default: 
            typeStr = "unknown type";
        
        }
        return typeStr;
    }
}
