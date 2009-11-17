package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.awt.image.*;
import java.text.*;
import java.awt.geom.*;
import java.beans.*;
import java.io.Serializable;
import javax.swing.event.*;
import javax.swing.border.*;
import javax.swing.plaf.*;
import javax.accessibility.*;
import javax.swing.text.*;
import javax.swing.text.html.*;
import javax.swing.plaf.basic.*;
import java.util.*;

class AbstractButton$Handler implements ActionListener, ChangeListener, ItemListener, Serializable {
    /*synthetic*/ final AbstractButton this$0;
    
    AbstractButton$Handler(/*synthetic*/ final AbstractButton this$0) {
        this.this$0 = this$0;
        
    }
    
    public void stateChanged(ChangeEvent e) {
        Object source = e.getSource();
        AbstractButton.access$100(this$0);
        this$0.fireStateChanged();
        this$0.repaint();
    }
    
    public void actionPerformed(ActionEvent event) {
        this$0.fireActionPerformed(event);
    }
    
    public void itemStateChanged(ItemEvent event) {
        this$0.fireItemStateChanged(event);
    }
}
