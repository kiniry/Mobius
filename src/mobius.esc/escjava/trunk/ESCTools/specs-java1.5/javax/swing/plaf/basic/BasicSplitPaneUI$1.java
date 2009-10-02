package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.util.*;

class BasicSplitPaneUI$1 extends Canvas {
    /*synthetic*/ final BasicSplitPaneUI this$0;
    
    BasicSplitPaneUI$1(/*synthetic*/ final BasicSplitPaneUI this$0) {
        this.this$0 = this$0;
        
    }
    
    public void paint(Graphics g) {
        if (!this$0.isContinuousLayout() && this$0.getLastDragLocation() != -1) {
            Dimension size = this$0.splitPane.getSize();
            g.setColor(BasicSplitPaneUI.access$400(this$0));
            if (BasicSplitPaneUI.access$300(this$0) == JSplitPane.HORIZONTAL_SPLIT) {
                g.fillRect(0, 0, this$0.dividerSize - 1, size.height - 1);
            } else {
                g.fillRect(0, 0, size.width - 1, this$0.dividerSize - 1);
            }
        }
    }
}
