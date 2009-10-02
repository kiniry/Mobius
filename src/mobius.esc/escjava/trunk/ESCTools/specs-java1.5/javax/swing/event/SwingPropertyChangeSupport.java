package javax.swing.event;

import java.beans.PropertyChangeSupport;

public final class SwingPropertyChangeSupport extends PropertyChangeSupport {
    
    public SwingPropertyChangeSupport(Object sourceBean) {
        super(sourceBean);
    }
    static final long serialVersionUID = 7162625831330845068L;
}
