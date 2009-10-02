package javax.swing;

import java.awt.event.*;
import java.beans.*;
import java.util.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.plaf.basic.*;
import javax.accessibility.*;
import java.lang.ref.WeakReference;

class JMenu$ActionChangedListener implements PropertyChangeListener {
    /*synthetic*/ final JMenu this$0;
    WeakReference menuItem;
    
    JMenu$ActionChangedListener(/*synthetic*/ final JMenu this$0, JMenuItem mi) {
        this.this$0 = this$0;
        
        setTarget(mi);
    }
    
    public void propertyChange(PropertyChangeEvent e) {
        String propertyName = e.getPropertyName();
        JMenuItem mi = (JMenuItem)getTarget();
        if (mi == null) {
            Action action = (Action)(Action)e.getSource();
            action.removePropertyChangeListener(this);
        } else {
            if (propertyName.equals(Action.NAME)) {
                String text = (String)(String)e.getNewValue();
                mi.setText(text);
            } else if (propertyName.equals("enabled")) {
                Boolean enabledState = (Boolean)(Boolean)e.getNewValue();
                mi.setEnabled(enabledState.booleanValue());
            } else if (propertyName.equals(Action.SMALL_ICON)) {
                Icon icon = (Icon)(Icon)e.getNewValue();
                mi.setIcon(icon);
                mi.invalidate();
                mi.repaint();
            } else if (propertyName.equals(Action.ACTION_COMMAND_KEY)) {
                mi.setActionCommand((String)(String)e.getNewValue());
            }
        }
    }
    
    public void setTarget(JMenuItem b) {
        menuItem = new WeakReference(b);
    }
    
    public JMenuItem getTarget() {
        return (JMenuItem)(JMenuItem)menuItem.get();
    }
}
