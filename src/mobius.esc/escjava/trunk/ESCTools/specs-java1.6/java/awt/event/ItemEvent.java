package java.awt.event;

import java.awt.AWTEvent;
import java.awt.ItemSelectable;

public class ItemEvent extends AWTEvent {
    public static final int ITEM_FIRST = 701;
    public static final int ITEM_LAST = 701;
    public static final int ITEM_STATE_CHANGED = ITEM_FIRST;
    public static final int SELECTED = 1;
    public static final int DESELECTED = 2;
    Object item;
    int stateChange;
    private static final long serialVersionUID = -608708132447206933L;
    
    public ItemEvent(ItemSelectable source, int id, Object item, int stateChange) {
        super(source, id);
        this.item = item;
        this.stateChange = stateChange;
    }
    
    public ItemSelectable getItemSelectable() {
        return (ItemSelectable)(ItemSelectable)source;
    }
    
    public Object getItem() {
        return item;
    }
    
    public int getStateChange() {
        return stateChange;
    }
    
    public String paramString() {
        String typeStr;
        switch (id) {
        case ITEM_STATE_CHANGED: 
            typeStr = "ITEM_STATE_CHANGED";
            break;
        
        default: 
            typeStr = "unknown type";
        
        }
        String stateStr;
        switch (stateChange) {
        case SELECTED: 
            stateStr = "SELECTED";
            break;
        
        case DESELECTED: 
            stateStr = "DESELECTED";
            break;
        
        default: 
            stateStr = "unknown type";
        
        }
        return typeStr + ",item=" + item + ",stateChange=" + stateStr;
    }
}
