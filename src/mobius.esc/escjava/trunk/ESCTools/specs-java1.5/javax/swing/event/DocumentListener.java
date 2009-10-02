package javax.swing.event;

import java.util.EventListener;

public interface DocumentListener extends EventListener {
    
    public void insertUpdate(DocumentEvent e);
    
    public void removeUpdate(DocumentEvent e);
    
    public void changedUpdate(DocumentEvent e);
}
