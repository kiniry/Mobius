package com.sun.java.swing.plaf.windows;

import java.awt.*;
import javax.swing.*;
import javax.swing.plaf.*;
import javax.swing.plaf.basic.*;
import com.sun.java.swing.plaf.windows.TMSchema.Part;
import com.sun.java.swing.plaf.windows.TMSchema.State;

class WindowsRadioButtonMenuItemUI$1 implements WindowsMenuItemUIAccessor {
    /*synthetic*/ final WindowsRadioButtonMenuItemUI this$0;
    
    WindowsRadioButtonMenuItemUI$1(/*synthetic*/ final WindowsRadioButtonMenuItemUI this$0) {
        this.this$0 = this$0;
        
    }
    
    public JMenuItem getMenuItem() {
        return WindowsRadioButtonMenuItemUI.access$000(this$0);
    }
    
    public TMSchema$State getState(JMenuItem menuItem) {
        return WindowsMenuItemUI.getState(this, menuItem);
    }
    
    public TMSchema$Part getPart(JMenuItem menuItem) {
        return WindowsMenuItemUI.getPart(this, menuItem);
    }
}
