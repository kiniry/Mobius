package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.util.*;

public class BasicSplitPaneUI$KeyboardEndHandler implements ActionListener {
    /*synthetic*/ final BasicSplitPaneUI this$0;
    
    public BasicSplitPaneUI$KeyboardEndHandler(/*synthetic*/ final BasicSplitPaneUI this$0) {
        this.this$0 = this$0;
        
    }
    
    public void actionPerformed(ActionEvent ev) {
        if (BasicSplitPaneUI.access$200(this$0)) {
            Insets insets = this$0.splitPane.getInsets();
            int bottomI = (insets != null) ? insets.bottom : 0;
            int rightI = (insets != null) ? insets.right : 0;
            if (BasicSplitPaneUI.access$300(this$0) == JSplitPane.VERTICAL_SPLIT) {
                this$0.splitPane.setDividerLocation(this$0.splitPane.getHeight() - bottomI);
            } else {
                this$0.splitPane.setDividerLocation(this$0.splitPane.getWidth() - rightI);
            }
        }
    }
}
