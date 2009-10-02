package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.awt.image.*;
import javax.swing.plaf.*;
import javax.swing.plaf.basic.*;
import javax.swing.event.*;
import javax.accessibility.*;

public class JMenuItem$AccessibleJMenuItem extends AbstractButton$AccessibleAbstractButton implements ChangeListener {
    /*synthetic*/ final JMenuItem this$0;
    private boolean isArmed = false;
    private boolean hasFocus = false;
    private boolean isPressed = false;
    private boolean isSelected = false;
    
    JMenuItem$AccessibleJMenuItem(/*synthetic*/ final JMenuItem this$0) {
        this.this$0 = this$0;
        super(this$0);
        this$0.addChangeListener(this);
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.MENU_ITEM;
    }
    
    private void fireAccessibilityFocusedEvent(JMenuItem toCheck) {
        MenuElement[] path = MenuSelectionManager.defaultManager().getSelectedPath();
        if (path.length > 0) {
            Object menuItem = path[path.length - 1];
            if (toCheck == menuItem) {
                firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, null, AccessibleState.FOCUSED);
            }
        }
    }
    
    public void stateChanged(ChangeEvent e) {
        firePropertyChange(AccessibleContext.ACCESSIBLE_VISIBLE_DATA_PROPERTY, Boolean.valueOf(false), Boolean.valueOf(true));
        if (this$0.getModel().isArmed()) {
            if (!isArmed) {
                isArmed = true;
                firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, null, AccessibleState.ARMED);
                fireAccessibilityFocusedEvent(this$0);
            }
        } else {
            if (isArmed) {
                isArmed = false;
                firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, AccessibleState.ARMED, null);
            }
        }
        if (this$0.isFocusOwner()) {
            if (!hasFocus) {
                hasFocus = true;
                firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, null, AccessibleState.FOCUSED);
            }
        } else {
            if (hasFocus) {
                hasFocus = false;
                firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, AccessibleState.FOCUSED, null);
            }
        }
        if (this$0.getModel().isPressed()) {
            if (!isPressed) {
                isPressed = true;
                firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, null, AccessibleState.PRESSED);
            }
        } else {
            if (isPressed) {
                isPressed = false;
                firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, AccessibleState.PRESSED, null);
            }
        }
        if (this$0.getModel().isSelected()) {
            if (!isSelected) {
                isSelected = true;
                firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, null, AccessibleState.CHECKED);
                fireAccessibilityFocusedEvent(this$0);
            }
        } else {
            if (isSelected) {
                isSelected = false;
                firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, AccessibleState.CHECKED, null);
            }
        }
    }
}
