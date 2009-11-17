package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.swing.border.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

final class JComponent$ActionStandin implements Action {
    
    /*synthetic*/ static ActionListener access$000(JComponent$ActionStandin x0) {
        return x0.actionListener;
    }
    /*synthetic*/ final JComponent this$0;
    private final ActionListener actionListener;
    private final String command;
    private final Action action;
    
    JComponent$ActionStandin(/*synthetic*/ final JComponent this$0, ActionListener actionListener, String command) {
        this.this$0 = this$0;
        
        this.actionListener = actionListener;
        if (actionListener instanceof Action) {
            this.action = (Action)(Action)actionListener;
        } else {
            this.action = null;
        }
        this.command = command;
    }
    
    public Object getValue(String key) {
        if (key != null) {
            if (key.equals(Action.ACTION_COMMAND_KEY)) {
                return command;
            }
            if (action != null) {
                return action.getValue(key);
            }
            if (key.equals(NAME)) {
                return "ActionStandin";
            }
        }
        return null;
    }
    
    public boolean isEnabled() {
        if (actionListener == null) {
            return false;
        }
        if (action == null) {
            return true;
        }
        return action.isEnabled();
    }
    
    public void actionPerformed(ActionEvent ae) {
        if (actionListener != null) {
            actionListener.actionPerformed(ae);
        }
    }
    
    public void putValue(String key, Object value) {
    }
    
    public void setEnabled(boolean b) {
    }
    
    public void addPropertyChangeListener(PropertyChangeListener listener) {
    }
    
    public void removePropertyChangeListener(PropertyChangeListener listener) {
    }
}
