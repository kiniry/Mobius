package javax.swing;

import javax.swing.event.ListDataListener;

public interface ListModel {
    
    int getSize();
    
    Object getElementAt(int index);
    
    void addListDataListener(ListDataListener l);
    
    void removeListDataListener(ListDataListener l);
}
