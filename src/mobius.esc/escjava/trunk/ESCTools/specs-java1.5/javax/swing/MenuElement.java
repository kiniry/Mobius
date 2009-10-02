package javax.swing;

import java.awt.*;
import java.awt.event.*;

public interface MenuElement {
    
    public void processMouseEvent(MouseEvent event, MenuElement[] path, MenuSelectionManager manager);
    
    public void processKeyEvent(KeyEvent event, MenuElement[] path, MenuSelectionManager manager);
    
    public void menuSelectionChanged(boolean isIncluded);
    
    public MenuElement[] getSubElements();
    
    public Component getComponent();
}
