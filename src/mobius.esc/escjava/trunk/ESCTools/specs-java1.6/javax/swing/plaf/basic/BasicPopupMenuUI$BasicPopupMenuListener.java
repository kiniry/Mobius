package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.plaf.basic.*;
import javax.swing.border.*;
import java.awt.event.*;
import java.util.*;

class BasicPopupMenuUI$BasicPopupMenuListener implements PopupMenuListener {
    
    /*synthetic*/ BasicPopupMenuUI$BasicPopupMenuListener(BasicPopupMenuUI x0, javax.swing.plaf.basic.BasicPopupMenuUI$1 x1) {
        this(x0);
    }
    /*synthetic*/ final BasicPopupMenuUI this$0;
    
    private BasicPopupMenuUI$BasicPopupMenuListener(/*synthetic*/ final BasicPopupMenuUI this$0) {
        this.this$0 = this$0;
        
    }
    
    public void popupMenuCanceled(PopupMenuEvent e) {
    }
    
    public void popupMenuWillBecomeInvisible(PopupMenuEvent e) {
    }
    
    public void popupMenuWillBecomeVisible(PopupMenuEvent e) {
        BasicLookAndFeel.playSound((JPopupMenu)(JPopupMenu)e.getSource(), "PopupMenu.popupSound");
    }
}
