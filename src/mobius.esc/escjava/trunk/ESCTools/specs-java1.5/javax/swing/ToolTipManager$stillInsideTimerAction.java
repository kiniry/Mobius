package javax.swing;

import java.awt.event.*;
import java.applet.*;
import java.awt.*;

public class ToolTipManager$stillInsideTimerAction implements ActionListener {
    /*synthetic*/ final ToolTipManager this$0;
    
    protected ToolTipManager$stillInsideTimerAction(/*synthetic*/ final ToolTipManager this$0) {
        this.this$0 = this$0;
        
    }
    
    public void actionPerformed(ActionEvent e) {
        this$0.hideTipWindow();
        this$0.enterTimer.stop();
        this$0.showImmediately = false;
        this$0.insideComponent = null;
        this$0.mouseEvent = null;
    }
}
