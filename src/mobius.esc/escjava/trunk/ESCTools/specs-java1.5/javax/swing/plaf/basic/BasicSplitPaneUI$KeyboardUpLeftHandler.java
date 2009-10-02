package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.util.*;

public class BasicSplitPaneUI$KeyboardUpLeftHandler implements ActionListener {
    /*synthetic*/ final BasicSplitPaneUI this$0;
    
    public BasicSplitPaneUI$KeyboardUpLeftHandler(/*synthetic*/ final BasicSplitPaneUI this$0) {
        this.this$0 = this$0;
        
    }
    
    public void actionPerformed(ActionEvent ev) {
        if (BasicSplitPaneUI.access$200(this$0)) {
            this$0.splitPane.setDividerLocation(Math.max(0, this$0.getDividerLocation(this$0.splitPane) - this$0.getKeyboardMoveIncrement()));
        }
    }
}
