package java.awt.event;

import java.awt.Adjustable;
import java.awt.AWTEvent;

public class AdjustmentEvent extends AWTEvent {
    public static final int ADJUSTMENT_FIRST = 601;
    public static final int ADJUSTMENT_LAST = 601;
    public static final int ADJUSTMENT_VALUE_CHANGED = ADJUSTMENT_FIRST;
    public static final int UNIT_INCREMENT = 1;
    public static final int UNIT_DECREMENT = 2;
    public static final int BLOCK_DECREMENT = 3;
    public static final int BLOCK_INCREMENT = 4;
    public static final int TRACK = 5;
    Adjustable adjustable;
    int value;
    int adjustmentType;
    boolean isAdjusting;
    private static final long serialVersionUID = 5700290645205279921L;
    
    public AdjustmentEvent(Adjustable source, int id, int type, int value) {
        this(source, id, type, value, false);
    }
    
    public AdjustmentEvent(Adjustable source, int id, int type, int value, boolean isAdjusting) {
        super(source, id);
        adjustable = source;
        this.adjustmentType = type;
        this.value = value;
        this.isAdjusting = isAdjusting;
    }
    
    public Adjustable getAdjustable() {
        return adjustable;
    }
    
    public int getValue() {
        return value;
    }
    
    public int getAdjustmentType() {
        return adjustmentType;
    }
    
    public boolean getValueIsAdjusting() {
        return isAdjusting;
    }
    
    public String paramString() {
        String typeStr;
        switch (id) {
        case ADJUSTMENT_VALUE_CHANGED: 
            typeStr = "ADJUSTMENT_VALUE_CHANGED";
            break;
        
        default: 
            typeStr = "unknown type";
        
        }
        String adjTypeStr;
        switch (adjustmentType) {
        case UNIT_INCREMENT: 
            adjTypeStr = "UNIT_INCREMENT";
            break;
        
        case UNIT_DECREMENT: 
            adjTypeStr = "UNIT_DECREMENT";
            break;
        
        case BLOCK_INCREMENT: 
            adjTypeStr = "BLOCK_INCREMENT";
            break;
        
        case BLOCK_DECREMENT: 
            adjTypeStr = "BLOCK_DECREMENT";
            break;
        
        case TRACK: 
            adjTypeStr = "TRACK";
            break;
        
        default: 
            adjTypeStr = "unknown type";
        
        }
        return typeStr + ",adjType=" + adjTypeStr + ",value=" + value + ",isAdjusting=" + isAdjusting;
    }
}
