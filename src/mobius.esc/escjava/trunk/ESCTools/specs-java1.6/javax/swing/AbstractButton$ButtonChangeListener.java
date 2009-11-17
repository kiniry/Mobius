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

public class AbstractButton$ButtonChangeListener implements ChangeListener, Serializable {
    /*synthetic*/ final AbstractButton this$0;
    
    AbstractButton$ButtonChangeListener(/*synthetic*/ final AbstractButton this$0) {
        this.this$0 = this$0;
        
    }
    
    public void stateChanged(ChangeEvent e) {
        AbstractButton.access$000(this$0).stateChanged(e);
    }
}
