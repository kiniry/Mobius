package javax.swing;

import java.awt.event.*;
import java.beans.*;
import java.util.*;
import java.io.Serializable;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.plaf.basic.*;
import javax.accessibility.*;

class JMenu$MenuChangeListener implements ChangeListener, Serializable {
    /*synthetic*/ final JMenu this$0;
    
    JMenu$MenuChangeListener(/*synthetic*/ final JMenu this$0) {
        this.this$0 = this$0;
        
    }
    boolean isSelected = false;
    
    public void stateChanged(ChangeEvent e) {
        ButtonModel model = (ButtonModel)(ButtonModel)e.getSource();
        boolean modelSelected = model.isSelected();
        if (modelSelected != isSelected) {
            if (modelSelected == true) {
                this$0.fireMenuSelected();
            } else {
                this$0.fireMenuDeselected();
            }
            isSelected = modelSelected;
        }
    }
}
