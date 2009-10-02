package java.awt.dnd;

import java.awt.event.InputEvent;

public class DragSourceDragEvent extends DragSourceEvent {
    private static final long serialVersionUID = 481346297933902471L;
    
    public DragSourceDragEvent(DragSourceContext dsc, int dropAction, int action, int modifiers) {
        super(dsc);
        targetActions = action;
        gestureModifiers = modifiers;
        this.dropAction = dropAction;
        if ((modifiers & ~(JDK_1_3_MODIFIERS | JDK_1_4_MODIFIERS)) != 0) {
            invalidModifiers = true;
        } else if ((getGestureModifiers() != 0) && (getGestureModifiersEx() == 0)) {
            setNewModifiers();
        } else if ((getGestureModifiers() == 0) && (getGestureModifiersEx() != 0)) {
            setOldModifiers();
        } else {
            invalidModifiers = true;
        }
    }
    
    public DragSourceDragEvent(DragSourceContext dsc, int dropAction, int action, int modifiers, int x, int y) {
        super(dsc, x, y);
        targetActions = action;
        gestureModifiers = modifiers;
        this.dropAction = dropAction;
        if ((modifiers & ~(JDK_1_3_MODIFIERS | JDK_1_4_MODIFIERS)) != 0) {
            invalidModifiers = true;
        } else if ((getGestureModifiers() != 0) && (getGestureModifiersEx() == 0)) {
            setNewModifiers();
        } else if ((getGestureModifiers() == 0) && (getGestureModifiersEx() != 0)) {
            setOldModifiers();
        } else {
            invalidModifiers = true;
        }
    }
    
    public int getTargetActions() {
        return targetActions;
    }
    private static final int JDK_1_3_MODIFIERS = InputEvent.SHIFT_DOWN_MASK - 1;
    private static final int JDK_1_4_MODIFIERS = ((InputEvent.ALT_GRAPH_DOWN_MASK << 1) - 1) & ~JDK_1_3_MODIFIERS;
    
    public int getGestureModifiers() {
        return invalidModifiers ? gestureModifiers : gestureModifiers & JDK_1_3_MODIFIERS;
    }
    
    public int getGestureModifiersEx() {
        return invalidModifiers ? gestureModifiers : gestureModifiers & JDK_1_4_MODIFIERS;
    }
    
    public int getUserAction() {
        return dropAction;
    }
    
    public int getDropAction() {
        return dropAction & targetActions & getDragSourceContext().getSourceActions();
    }
    private int targetActions = DnDConstants.ACTION_NONE;
    private int dropAction = DnDConstants.ACTION_NONE;
    private int gestureModifiers = 0;
    private boolean invalidModifiers;
    
    private void setNewModifiers() {
        if ((gestureModifiers & InputEvent.BUTTON1_MASK) != 0) {
            gestureModifiers |= InputEvent.BUTTON1_DOWN_MASK;
        }
        if ((gestureModifiers & InputEvent.BUTTON2_MASK) != 0) {
            gestureModifiers |= InputEvent.BUTTON2_DOWN_MASK;
        }
        if ((gestureModifiers & InputEvent.BUTTON3_MASK) != 0) {
            gestureModifiers |= InputEvent.BUTTON3_DOWN_MASK;
        }
        if ((gestureModifiers & InputEvent.SHIFT_MASK) != 0) {
            gestureModifiers |= InputEvent.SHIFT_DOWN_MASK;
        }
        if ((gestureModifiers & InputEvent.CTRL_MASK) != 0) {
            gestureModifiers |= InputEvent.CTRL_DOWN_MASK;
        }
        if ((gestureModifiers & InputEvent.ALT_GRAPH_MASK) != 0) {
            gestureModifiers |= InputEvent.ALT_GRAPH_DOWN_MASK;
        }
    }
    
    private void setOldModifiers() {
        if ((gestureModifiers & InputEvent.BUTTON1_DOWN_MASK) != 0) {
            gestureModifiers |= InputEvent.BUTTON1_MASK;
        }
        if ((gestureModifiers & InputEvent.BUTTON2_DOWN_MASK) != 0) {
            gestureModifiers |= InputEvent.BUTTON2_MASK;
        }
        if ((gestureModifiers & InputEvent.BUTTON3_DOWN_MASK) != 0) {
            gestureModifiers |= InputEvent.BUTTON3_MASK;
        }
        if ((gestureModifiers & InputEvent.SHIFT_DOWN_MASK) != 0) {
            gestureModifiers |= InputEvent.SHIFT_MASK;
        }
        if ((gestureModifiers & InputEvent.CTRL_DOWN_MASK) != 0) {
            gestureModifiers |= InputEvent.CTRL_MASK;
        }
        if ((gestureModifiers & InputEvent.ALT_GRAPH_DOWN_MASK) != 0) {
            gestureModifiers |= InputEvent.ALT_GRAPH_MASK;
        }
    }
}
