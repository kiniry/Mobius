package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.util.*;

public class BasicSplitPaneUI$KeyboardHomeHandler implements ActionListener {
    /*synthetic*/ final BasicSplitPaneUI this$0;
    
    public BasicSplitPaneUI$KeyboardHomeHandler(/*synthetic*/ final BasicSplitPaneUI this$0) {
        this.this$0 = this$0;
        
    }
    
    public void actionPerformed(ActionEvent ev) {
        if (BasicSplitPaneUI.access$200(this$0)) {
            this$0.splitPane.setDividerLocation(0);
        }
    }
}
