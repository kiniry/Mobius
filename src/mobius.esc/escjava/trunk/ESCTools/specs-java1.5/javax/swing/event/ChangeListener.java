package javax.swing.event;

import java.util.EventListener;

public interface ChangeListener extends EventListener {
    
    void stateChanged(ChangeEvent e);
}
