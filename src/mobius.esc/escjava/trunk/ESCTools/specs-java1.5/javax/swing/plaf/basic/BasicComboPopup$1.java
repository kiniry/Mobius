package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;

class BasicComboPopup$1 extends JList {
    /*synthetic*/ final BasicComboPopup this$0;
    
    BasicComboPopup$1(/*synthetic*/ final BasicComboPopup this$0, .javax.swing.ListModel x0) {
        this.this$0 = this$0;
        super(x0);
    }
    
    public void processMouseEvent(MouseEvent e) {
        if (e.isControlDown()) {
            e = new MouseEvent((Component)(Component)e.getSource(), e.getID(), e.getWhen(), e.getModifiers() ^ InputEvent.CTRL_MASK, e.getX(), e.getY(), e.getClickCount(), e.isPopupTrigger());
        }
        super.processMouseEvent(e);
    }
}
