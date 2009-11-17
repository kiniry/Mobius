package javax.swing;

import java.awt.event.*;
import java.applet.*;
import java.awt.*;

class ToolTipManager$MoveBeforeEnterListener extends MouseMotionAdapter {
    
    /*synthetic*/ ToolTipManager$MoveBeforeEnterListener(ToolTipManager x0, javax.swing.ToolTipManager$1 x1) {
        this(x0);
    }
    /*synthetic*/ final ToolTipManager this$0;
    
    private ToolTipManager$MoveBeforeEnterListener(/*synthetic*/ final ToolTipManager this$0) {
        this.this$0 = this$0;
        
    }
    
    public void mouseMoved(MouseEvent e) {
        ToolTipManager.access$300(this$0, e);
    }
}
