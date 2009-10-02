package java.awt.event;

import java.awt.Component;
import sun.awt.DebugHelper;

public class MouseWheelEvent extends MouseEvent {
    private static final DebugHelper dbg = DebugHelper.create(MouseWheelEvent.class);
    public static final int WHEEL_UNIT_SCROLL = 0;
    public static final int WHEEL_BLOCK_SCROLL = 1;
    int scrollType;
    int scrollAmount;
    int wheelRotation;
    
    public MouseWheelEvent(Component source, int id, long when, int modifiers, int x, int y, int clickCount, boolean popupTrigger, int scrollType, int scrollAmount, int wheelRotation) {
        super(source, id, when, modifiers, x, y, clickCount, popupTrigger);
        this.scrollType = scrollType;
        this.scrollAmount = scrollAmount;
        this.wheelRotation = wheelRotation;
        if (dbg.on) {
            dbg.println("MouseWheelEvent constructor");
        }
    }
    
    public int getScrollType() {
        return scrollType;
    }
    
    public int getScrollAmount() {
        return scrollAmount;
    }
    
    public int getWheelRotation() {
        return wheelRotation;
    }
    
    public int getUnitsToScroll() {
        return scrollAmount * wheelRotation;
    }
    
    public String paramString() {
        String scrollTypeStr = null;
        if (getScrollType() == WHEEL_UNIT_SCROLL) {
            scrollTypeStr = "WHEEL_UNIT_SCROLL";
        } else if (getScrollType() == WHEEL_BLOCK_SCROLL) {
            scrollTypeStr = "WHEEL_BLOCK_SCROLL";
        } else {
            scrollTypeStr = "unknown scroll type";
        }
        return super.paramString() + ",scrollType=" + scrollTypeStr + ",scrollAmount=" + getScrollAmount() + ",wheelRotation=" + getWheelRotation();
    }
}
