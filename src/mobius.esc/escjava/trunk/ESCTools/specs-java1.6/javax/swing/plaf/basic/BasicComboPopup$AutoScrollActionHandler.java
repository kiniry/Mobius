package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;

class BasicComboPopup$AutoScrollActionHandler implements ActionListener {
    /*synthetic*/ final BasicComboPopup this$0;
    private int direction;
    
    BasicComboPopup$AutoScrollActionHandler(/*synthetic*/ final BasicComboPopup this$0, int direction) {
        this.this$0 = this$0;
        
        this.direction = direction;
    }
    
    public void actionPerformed(ActionEvent e) {
        if (direction == 0) {
            this$0.autoScrollUp();
        } else {
            this$0.autoScrollDown();
        }
    }
}
