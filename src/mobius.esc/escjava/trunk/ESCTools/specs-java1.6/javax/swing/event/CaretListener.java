package javax.swing.event;

import java.util.EventListener;

public interface CaretListener extends EventListener {
    
    void caretUpdate(CaretEvent e);
}
