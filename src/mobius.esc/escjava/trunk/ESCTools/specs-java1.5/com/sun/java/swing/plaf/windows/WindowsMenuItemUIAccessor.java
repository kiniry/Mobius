package com.sun.java.swing.plaf.windows;

import javax.swing.JMenuItem;
import com.sun.java.swing.plaf.windows.TMSchema.Part;
import com.sun.java.swing.plaf.windows.TMSchema.State;

interface WindowsMenuItemUIAccessor {
    
    JMenuItem getMenuItem();
    
    TMSchema$State getState(JMenuItem menuItem);
    
    TMSchema$Part getPart(JMenuItem menuItem);
}
