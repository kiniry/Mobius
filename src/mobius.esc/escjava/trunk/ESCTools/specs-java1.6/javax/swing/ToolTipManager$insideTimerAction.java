package javax.swing;

import java.awt.event.*;
import java.applet.*;
import java.awt.*;

public class ToolTipManager$insideTimerAction implements ActionListener {
    /*synthetic*/ final ToolTipManager this$0;
    
    protected ToolTipManager$insideTimerAction(/*synthetic*/ final ToolTipManager this$0) {
        this.this$0 = this$0;
        
    }
    
    public void actionPerformed(ActionEvent e) {
        if (this$0.insideComponent != null && this$0.insideComponent.isShowing()) {
            if (this$0.toolTipText == null && this$0.mouseEvent != null) {
                this$0.toolTipText = this$0.insideComponent.getToolTipText(this$0.mouseEvent);
                this$0.preferredLocation = this$0.insideComponent.getToolTipLocation(this$0.mouseEvent);
            }
            if (this$0.toolTipText != null) {
                this$0.showImmediately = true;
                this$0.showTipWindow();
            } else {
                this$0.insideComponent = null;
                this$0.toolTipText = null;
                this$0.preferredLocation = null;
                this$0.mouseEvent = null;
                this$0.hideTipWindow();
            }
        }
    }
}
