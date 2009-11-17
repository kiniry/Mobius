package javax.swing.plaf.basic;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.border.*;

public class BasicMenuUI$ChangeHandler implements ChangeListener {
    /*synthetic*/ final BasicMenuUI this$0;
    public JMenu menu;
    public BasicMenuUI ui;
    public boolean isSelected = false;
    public Component wasFocused;
    
    public BasicMenuUI$ChangeHandler(/*synthetic*/ final BasicMenuUI this$0, JMenu m, BasicMenuUI ui) {
        this.this$0 = this$0;
        
        menu = m;
        this.ui = ui;
    }
    
    public void stateChanged(ChangeEvent e) {
    }
}
