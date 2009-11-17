package javax.swing;

import javax.swing.event.*;

public interface SingleSelectionModel {
    
    public int getSelectedIndex();
    
    public void setSelectedIndex(int index);
    
    public void clearSelection();
    
    public boolean isSelected();
    
    void addChangeListener(ChangeListener listener);
    
    void removeChangeListener(ChangeListener listener);
}
