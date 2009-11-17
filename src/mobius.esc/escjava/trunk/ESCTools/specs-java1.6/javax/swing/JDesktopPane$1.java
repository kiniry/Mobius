package javax.swing;

import javax.swing.plaf.*;
import javax.accessibility.*;
import java.awt.Component;
import java.awt.Container;

class JDesktopPane$1 extends LayoutFocusTraversalPolicy {
    /*synthetic*/ final JDesktopPane this$0;
    
    JDesktopPane$1(/*synthetic*/ final JDesktopPane this$0) {
        this.this$0 = this$0;
        
    }
    
    public Component getDefaultComponent(Container c) {
        JInternalFrame[] jifArray = this$0.getAllFrames();
        Component comp = null;
        for (int i = 0; i < jifArray.length; i++) {
            comp = jifArray[i].getFocusTraversalPolicy().getDefaultComponent(jifArray[i]);
            if (comp != null) {
                break;
            }
        }
        return comp;
    }
}
