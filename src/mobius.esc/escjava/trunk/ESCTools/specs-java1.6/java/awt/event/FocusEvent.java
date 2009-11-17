package java.awt.event;

import java.awt.Component;
import sun.awt.AppContext;
import sun.awt.SunToolkit;

public class FocusEvent extends ComponentEvent {
    public static final int FOCUS_FIRST = 1004;
    public static final int FOCUS_LAST = 1005;
    public static final int FOCUS_GAINED = FOCUS_FIRST;
    public static final int FOCUS_LOST = 1 + FOCUS_FIRST;
    boolean temporary;
    transient Component opposite;
    private static final long serialVersionUID = 523753786457416396L;
    
    public FocusEvent(Component source, int id, boolean temporary, Component opposite) {
        super(source, id);
        this.temporary = temporary;
        this.opposite = opposite;
    }
    
    public FocusEvent(Component source, int id, boolean temporary) {
        this(source, id, temporary, null);
    }
    
    public FocusEvent(Component source, int id) {
        this(source, id, false);
    }
    
    public boolean isTemporary() {
        return temporary;
    }
    
    public Component getOppositeComponent() {
        if (opposite == null) {
            return null;
        }
        return (SunToolkit.targetToAppContext(opposite) == AppContext.getAppContext()) ? opposite : null;
    }
    
    public String paramString() {
        String typeStr;
        switch (id) {
        case FOCUS_GAINED: 
            typeStr = "FOCUS_GAINED";
            break;
        
        case FOCUS_LOST: 
            typeStr = "FOCUS_LOST";
            break;
        
        default: 
            typeStr = "unknown type";
        
        }
        return typeStr + (temporary ? ",temporary" : ",permanent") + ",opposite=" + getOppositeComponent();
    }
}
