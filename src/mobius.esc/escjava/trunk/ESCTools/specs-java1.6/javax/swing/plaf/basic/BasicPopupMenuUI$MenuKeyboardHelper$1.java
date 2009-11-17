package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.plaf.basic.*;
import javax.swing.border.*;
import java.awt.Component;
import java.awt.event.*;
import java.util.*;

class BasicPopupMenuUI$MenuKeyboardHelper$1 extends FocusAdapter {
    /*synthetic*/ final BasicPopupMenuUI$MenuKeyboardHelper this$0;
    
    BasicPopupMenuUI$MenuKeyboardHelper$1(/*synthetic*/ final BasicPopupMenuUI$MenuKeyboardHelper this$0) {
        this.this$0 = this$0;
        
    }
    
    public void focusGained(FocusEvent ev) {
        Component opposite = ev.getOppositeComponent();
        if (opposite != null) {
            BasicPopupMenuUI.MenuKeyboardHelper.access$402(this$0, opposite);
        }
        ev.getComponent().removeFocusListener(this);
    }
}
