package javax.swing;

import java.awt.event.*;
import java.applet.*;
import java.awt.*;

public class ToolTipManager$outsideTimerAction implements ActionListener {
    /*synthetic*/ final ToolTipManager this$0;
    
    protected ToolTipManager$outsideTimerAction(/*synthetic*/ final ToolTipManager this$0) {
        this.this$0 = this$0;
        
    }
    
    public void actionPerformed(ActionEvent e) {
        this$0.showImmediately = false;
    }
}
