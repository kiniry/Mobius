package javax.swing;

import java.awt.event.*;
import java.beans.*;
import java.util.*;
import java.io.Serializable;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.plaf.basic.*;
import javax.accessibility.*;

public class JMenu$WinListener extends WindowAdapter implements Serializable {
    /*synthetic*/ final JMenu this$0;
    JPopupMenu popupMenu;
    
    public JMenu$WinListener(/*synthetic*/ final JMenu this$0, JPopupMenu p) {
        this.this$0 = this$0;
        
        this.popupMenu = p;
    }
    
    public void windowClosing(WindowEvent e) {
        this$0.setSelected(false);
    }
}
