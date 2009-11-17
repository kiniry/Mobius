package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.awt.image.*;
import java.io.Serializable;
import java.util.EventListener;
import javax.swing.event.*;

public class DefaultButtonModel implements ButtonModel, Serializable {
    protected int stateMask = 0;
    protected String actionCommand = null;
    protected ButtonGroup group = null;
    protected int mnemonic = 0;
    protected transient ChangeEvent changeEvent = null;
    protected EventListenerList listenerList = new EventListenerList();
    
    public DefaultButtonModel() {
        
        stateMask = 0;
        setEnabled(true);
    }
    public static final int ARMED = 1 << 0;
    public static final int SELECTED = 1 << 1;
    public static final int PRESSED = 1 << 2;
    public static final int ENABLED = 1 << 3;
    public static final int ROLLOVER = 1 << 4;
    
    public void setActionCommand(String actionCommand) {
        this.actionCommand = actionCommand;
    }
    
    public String getActionCommand() {
        return actionCommand;
    }
    
    public boolean isArmed() {
        return (stateMask & ARMED) != 0;
    }
    
    public boolean isSelected() {
        return (stateMask & SELECTED) != 0;
    }
    
    public boolean isEnabled() {
        return (stateMask & ENABLED) != 0;
    }
    
    public boolean isPressed() {
        return (stateMask & PRESSED) != 0;
    }
    
    public boolean isRollover() {
        return (stateMask & ROLLOVER) != 0;
    }
    
    public void setArmed(boolean b) {
        if ((isArmed() == b) || !isEnabled()) {
            return;
        }
        if (b) {
            stateMask |= ARMED;
        } else {
            stateMask &= ~ARMED;
        }
        fireStateChanged();
    }
    
    public void setEnabled(boolean b) {
        if (isEnabled() == b) {
            return;
        }
        if (b) {
            stateMask |= ENABLED;
        } else {
            stateMask &= ~ENABLED;
            stateMask &= ~ARMED;
            stateMask &= ~PRESSED;
        }
        fireStateChanged();
    }
    
    public void setSelected(boolean b) {
        if (this.isSelected() == b) {
            return;
        }
        if (b) {
            stateMask |= SELECTED;
        } else {
            stateMask &= ~SELECTED;
        }
        fireItemStateChanged(new ItemEvent(this, ItemEvent.ITEM_STATE_CHANGED, this, b ? ItemEvent.SELECTED : ItemEvent.DESELECTED));
        fireStateChanged();
    }
    
    public void setPressed(boolean b) {
        if ((isPressed() == b) || !isEnabled()) {
            return;
        }
        if (b) {
            stateMask |= PRESSED;
        } else {
            stateMask &= ~PRESSED;
        }
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
        fireStateChanged();
    }
    
    public void setRollover(boolean b) {
        if ((isRollover() == b) || !isEnabled()) {
            return;
        }
        if (b) {
            stateMask |= ROLLOVER;
        } else {
            stateMask &= ~ROLLOVER;
        }
        fireStateChanged();
    }
    
    public void setMnemonic(int key) {
        mnemonic = key;
        fireStateChanged();
    }
    
    public int getMnemonic() {
        return mnemonic;
    }
    
    public void addChangeListener(ChangeListener l) {
        listenerList.add(ChangeListener.class, l);
    }
    
    public void removeChangeListener(ChangeListener l) {
        listenerList.remove(ChangeListener.class, l);
    }
    
    public ChangeListener[] getChangeListeners() {
        return (ChangeListener[])(ChangeListener[])listenerList.getListeners(ChangeListener.class);
    }
    
    protected void fireStateChanged() {
        Object[] listeners = listenerList.getListenerList();
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == ChangeListener.class) {
                if (changeEvent == null) changeEvent = new ChangeEvent(this);
                ((ChangeListener)(ChangeListener)listeners[i + 1]).stateChanged(changeEvent);
            }
        }
    }
    
    public void addActionListener(ActionListener l) {
        listenerList.add(ActionListener.class, l);
    }
    
    public void removeActionListener(ActionListener l) {
        listenerList.remove(ActionListener.class, l);
    }
    
    public ActionListener[] getActionListeners() {
        return (ActionListener[])(ActionListener[])listenerList.getListeners(ActionListener.class);
    }
    
    protected void fireActionPerformed(ActionEvent e) {
        Object[] listeners = listenerList.getListenerList();
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == ActionListener.class) {
                ((ActionListener)(ActionListener)listeners[i + 1]).actionPerformed(e);
            }
        }
    }
    
    public void addItemListener(ItemListener l) {
        listenerList.add(ItemListener.class, l);
    }
    
    public void removeItemListener(ItemListener l) {
        listenerList.remove(ItemListener.class, l);
    }
    
    public ItemListener[] getItemListeners() {
        return (ItemListener[])(ItemListener[])listenerList.getListeners(ItemListener.class);
    }
    
    protected void fireItemStateChanged(ItemEvent e) {
        Object[] listeners = listenerList.getListenerList();
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == ItemListener.class) {
                ((ItemListener)(ItemListener)listeners[i + 1]).itemStateChanged(e);
            }
        }
    }
    
    public EventListener[] getListeners(Class listenerType) {
        return listenerList.getListeners(listenerType);
    }
    
    public Object[] getSelectedObjects() {
        return null;
    }
    
    public void setGroup(ButtonGroup group) {
        this.group = group;
    }
    
    public ButtonGroup getGroup() {
        return group;
    }
}
