package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.awt.image.*;
import java.text.*;
import java.awt.geom.*;
import java.beans.*;
import javax.swing.event.*;
import javax.swing.border.*;
import javax.swing.plaf.*;
import javax.accessibility.*;
import javax.swing.text.*;
import javax.swing.text.html.*;
import javax.swing.plaf.basic.*;
import java.util.*;

class AbstractButton$AccessibleAbstractButton$ButtonKeyBinding implements AccessibleKeyBinding {
    /*synthetic*/ final AbstractButton$AccessibleAbstractButton this$1;
    int mnemonic;
    
    AbstractButton$AccessibleAbstractButton$ButtonKeyBinding(/*synthetic*/ final AbstractButton$AccessibleAbstractButton this$1, int mnemonic) {
        this.this$1 = this$1;
        
        this.mnemonic = mnemonic;
    }
    
    public int getAccessibleKeyBindingCount() {
        return 1;
    }
    
    public java.lang.Object getAccessibleKeyBinding(int i) {
        if (i != 0) {
            throw new IllegalArgumentException();
        }
        return KeyStroke.getKeyStroke(mnemonic, 0);
    }
}
