package com.sun.java.swing.plaf.windows;

import java.awt.*;
import java.awt.event.MouseEvent;
import javax.swing.*;

public class WindowsMenuUI$WindowsMouseInputHandler extends BasicMenuUI$MouseInputHandler {
    /*synthetic*/ final WindowsMenuUI this$0;
    
    protected WindowsMenuUI$WindowsMouseInputHandler(/*synthetic*/ final WindowsMenuUI this$0) {
        this.this$0 = this$0;
        super(this$0);
    }
    
    public void mouseEntered(MouseEvent evt) {
        super.mouseEntered(evt);
        JMenu menu = (JMenu)(JMenu)evt.getSource();
        ButtonModel model = menu.getModel();
        if (menu.isRolloverEnabled()) {
            model.setRollover(true);
            WindowsMenuUI.access$100(this$0).repaint();
        }
    }
    
    public void mouseExited(MouseEvent evt) {
        super.mouseExited(evt);
        JMenu menu = (JMenu)(JMenu)evt.getSource();
        ButtonModel model = menu.getModel();
        if (menu.isRolloverEnabled()) {
            model.setRollover(false);
            WindowsMenuUI.access$200(this$0).repaint();
        }
    }
}
