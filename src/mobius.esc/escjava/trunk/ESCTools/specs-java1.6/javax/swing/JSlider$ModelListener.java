package javax.swing;

import javax.swing.border.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;
import java.io.Serializable;
import java.util.*;
import java.beans.*;

class JSlider$ModelListener implements ChangeListener, Serializable {
    
    /*synthetic*/ JSlider$ModelListener(JSlider x0, javax.swing.JSlider$1 x1) {
        this(x0);
    }
    /*synthetic*/ final JSlider this$0;
    
    private JSlider$ModelListener(/*synthetic*/ final JSlider this$0) {
        this.this$0 = this$0;
        
    }
    
    public void stateChanged(ChangeEvent e) {
        this$0.fireStateChanged();
    }
}
