package javax.swing;

import java.awt.*;
import java.awt.event.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

public class JToggleButton$ToggleButtonModel extends DefaultButtonModel {
    
    public JToggleButton$ToggleButtonModel() {
        
    }
    
    public boolean isSelected() {
        return (stateMask & SELECTED) != 0;
    }
    
    public void setSelected(boolean b) {
        ButtonGroup group = getGroup();
        if (group != null) {
            group.setSelected(this, b);
            b = group.isSelected(this);
        }
        if (isSelected() == b) {
            return;
        }
        if (b) {
            stateMask |= SELECTED;
        } else {
            stateMask &= ~SELECTED;
        }
        fireStateChanged();
        fireItemStateChanged(new ItemEvent(this, ItemEvent.ITEM_STATE_CHANGED, this, this.isSelected() ? ItemEvent.SELECTED : ItemEvent.DESELECTED));
    }
    
    public void setPressed(boolean b) {
        if ((isPressed() == b) || !isEnabled()) {
            return;
        }
        if (b == false && isArmed()) {
            setSelected(!this.isSelected());
        }
        if (b) {
            stateMask |= PRESSED;
        } else {
            stateMask &= ~PRESSED;
        }
        fireStateChanged();
        if (!isPressed() && isArmed()) {
            int modifiers = 0;
            AWTEvent currentEvent = EventQueue.getCurrentEvent();
            if (currentEvent instanceof InputEvent) {
                modifiers = ((InputEvent)(InputEvent)currentEvent).getModifiers();
            } else if (currentEvent instanceof ActionEvent) {
                modifiers = ((ActionEvent)(ActionEvent)currentEvent).getModifiers();
            }
            fireActionPerformed(new ActionEvent(this, ActionEvent.ACTION_PERFORMED, getActionCommand(), EventQueue.getMostRecentEventTime(), modifiers));
        }
    }
}
