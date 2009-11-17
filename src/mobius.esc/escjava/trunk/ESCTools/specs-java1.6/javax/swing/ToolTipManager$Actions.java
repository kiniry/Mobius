package javax.swing;

import java.awt.event.*;
import java.applet.*;
import java.awt.*;
import sun.swing.UIAction;

class ToolTipManager$Actions extends UIAction {
    
    /*synthetic*/ static String access$100() {
        return HIDE;
    }
    
    /*synthetic*/ static String access$000() {
        return SHOW;
    }
    private static String SHOW = "SHOW";
    private static String HIDE = "HIDE";
    
    ToolTipManager$Actions(String key) {
        super(key);
    }
    
    public void actionPerformed(ActionEvent e) {
        String key = getName();
        JComponent source = (JComponent)(JComponent)e.getSource();
        if (key == SHOW) {
            ToolTipManager.access$500(ToolTipManager.sharedInstance(), source);
        } else if (key == HIDE) {
            ToolTipManager.access$600(ToolTipManager.sharedInstance(), source);
        }
    }
    
    public boolean isEnabled(Object sender) {
        if (getName() == SHOW) {
            return true;
        }
        return ToolTipManager.access$700(ToolTipManager.sharedInstance());
    }
}
