package javax.swing.event;

import java.util.EventObject;
import javax.swing.*;

public class ListSelectionEvent extends EventObject {
    private int firstIndex;
    private int lastIndex;
    private boolean isAdjusting;
    
    public ListSelectionEvent(Object source, int firstIndex, int lastIndex, boolean isAdjusting) {
        super(source);
        this.firstIndex = firstIndex;
        this.lastIndex = lastIndex;
        this.isAdjusting = isAdjusting;
    }
    
    public int getFirstIndex() {
        return firstIndex;
    }
    
    public int getLastIndex() {
        return lastIndex;
    }
    
    public boolean getValueIsAdjusting() {
        return isAdjusting;
    }
    
    public String toString() {
        String properties = " source=" + getSource() + " firstIndex= " + firstIndex + " lastIndex= " + lastIndex + " isAdjusting= " + isAdjusting + " ";
        return getClass().getName() + "[" + properties + "]";
    }
}
