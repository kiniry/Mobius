package javax.swing.text;

import java.awt.event.ActionEvent;
import java.util.Hashtable;
import java.util.Enumeration;
import javax.swing.Action;
import javax.swing.AbstractAction;

public abstract class TextAction extends AbstractAction {
    
    public TextAction(String name) {
        super(name);
    }
    
    protected final JTextComponent getTextComponent(ActionEvent e) {
        if (e != null) {
            Object o = e.getSource();
            if (o instanceof JTextComponent) {
                return (JTextComponent)(JTextComponent)o;
            }
        }
        return getFocusedComponent();
    }
    
    public static final Action[] augmentList(Action[] list1, Action[] list2) {
        Hashtable h = new Hashtable();
        for (int i = 0; i < list1.length; i++) {
            Action a = list1[i];
            String value = (String)(String)a.getValue(Action.NAME);
            h.put((value != null ? value : ""), a);
        }
        for (int i = 0; i < list2.length; i++) {
            Action a = list2[i];
            String value = (String)(String)a.getValue(Action.NAME);
            h.put((value != null ? value : ""), a);
        }
        Action[] actions = new Action[h.size()];
        int index = 0;
        for (Enumeration e = h.elements(); e.hasMoreElements(); ) {
            actions[index++] = (Action)(Action)e.nextElement();
        }
        return actions;
    }
    
    protected final JTextComponent getFocusedComponent() {
        return JTextComponent.getFocusedComponent();
    }
}
