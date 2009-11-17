package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.swing.border.*;
import javax.swing.plaf.*;
import sun.swing.UIAction;

class BasicToolBarUI$Actions extends UIAction {
    private static final String NAVIGATE_RIGHT = "navigateRight";
    private static final String NAVIGATE_LEFT = "navigateLeft";
    private static final String NAVIGATE_UP = "navigateUp";
    private static final String NAVIGATE_DOWN = "navigateDown";
    
    public BasicToolBarUI$Actions(String name) {
        super(name);
    }
    
    public void actionPerformed(ActionEvent evt) {
        String key = getName();
        JToolBar toolBar = (JToolBar)(JToolBar)evt.getSource();
        BasicToolBarUI ui = (BasicToolBarUI)(BasicToolBarUI)BasicLookAndFeel.getUIOfType(toolBar.getUI(), BasicToolBarUI.class);
        if (NAVIGATE_RIGHT == key) {
            ui.navigateFocusedComp(3);
        } else if (NAVIGATE_LEFT == key) {
            ui.navigateFocusedComp(7);
        } else if (NAVIGATE_UP == key) {
            ui.navigateFocusedComp(1);
        } else if (NAVIGATE_DOWN == key) {
            ui.navigateFocusedComp(5);
        }
    }
}
