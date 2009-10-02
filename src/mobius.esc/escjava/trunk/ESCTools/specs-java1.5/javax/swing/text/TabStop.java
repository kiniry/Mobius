package javax.swing.text;

import java.io.Serializable;

public class TabStop implements Serializable {
    public static final int ALIGN_LEFT = 0;
    public static final int ALIGN_RIGHT = 1;
    public static final int ALIGN_CENTER = 2;
    public static final int ALIGN_DECIMAL = 4;
    public static final int ALIGN_BAR = 5;
    public static final int LEAD_NONE = 0;
    public static final int LEAD_DOTS = 1;
    public static final int LEAD_HYPHENS = 2;
    public static final int LEAD_UNDERLINE = 3;
    public static final int LEAD_THICKLINE = 4;
    public static final int LEAD_EQUALS = 5;
    private int alignment;
    private float position;
    private int leader;
    
    public TabStop(float pos) {
        this(pos, ALIGN_LEFT, LEAD_NONE);
    }
    
    public TabStop(float pos, int align, int leader) {
        
        alignment = align;
        this.leader = leader;
        position = pos;
    }
    
    public float getPosition() {
        return position;
    }
    
    public int getAlignment() {
        return alignment;
    }
    
    public int getLeader() {
        return leader;
    }
    
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if (other instanceof TabStop) {
            TabStop o = (TabStop)(TabStop)other;
            return ((alignment == o.alignment) && (leader == o.leader) && (position == o.position));
        }
        return false;
    }
    
    public int hashCode() {
        return alignment ^ leader ^ Math.round(position);
    }
    
    public String toString() {
        String buf;
        switch (alignment) {
        default: 
        
        case ALIGN_LEFT: 
            buf = "";
            break;
        
        case ALIGN_RIGHT: 
            buf = "right ";
            break;
        
        case ALIGN_CENTER: 
            buf = "center ";
            break;
        
        case ALIGN_DECIMAL: 
            buf = "decimal ";
            break;
        
        case ALIGN_BAR: 
            buf = "bar ";
            break;
        
        }
        buf = buf + "tab @" + String.valueOf(position);
        if (leader != LEAD_NONE) buf = buf + " (w/leaders)";
        return buf;
    }
}
