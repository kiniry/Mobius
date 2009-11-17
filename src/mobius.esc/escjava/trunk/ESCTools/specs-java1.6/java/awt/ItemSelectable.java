package java.awt;

import java.awt.event.*;

public interface ItemSelectable {
    
    public Object[] getSelectedObjects();
    
    public void addItemListener(ItemListener l);
    
    public void removeItemListener(ItemListener l);
}
