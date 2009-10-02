package javax.swing;

import java.awt.event.*;
import java.applet.*;
import java.awt.*;

class ToolTipManager$1 extends FocusAdapter {
    /*synthetic*/ final ToolTipManager this$0;
    
    ToolTipManager$1(/*synthetic*/ final ToolTipManager this$0) {
        this.this$0 = this$0;
        
    }
    
    public void focusLost(FocusEvent evt) {
        this$0.hideTipWindow();
        this$0.insideComponent = null;
        JComponent c = (JComponent)(JComponent)evt.getSource();
        c.removeFocusListener(ToolTipManager.access$400(this$0));
    }
}
