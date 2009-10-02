package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.util.*;

public class BasicSplitPaneUI$FocusHandler extends FocusAdapter {
    /*synthetic*/ final BasicSplitPaneUI this$0;
    
    public BasicSplitPaneUI$FocusHandler(/*synthetic*/ final BasicSplitPaneUI this$0) {
        this.this$0 = this$0;
        
    }
    
    public void focusGained(FocusEvent ev) {
        BasicSplitPaneUI.access$100(this$0).focusGained(ev);
    }
    
    public void focusLost(FocusEvent ev) {
        BasicSplitPaneUI.access$100(this$0).focusLost(ev);
    }
}
