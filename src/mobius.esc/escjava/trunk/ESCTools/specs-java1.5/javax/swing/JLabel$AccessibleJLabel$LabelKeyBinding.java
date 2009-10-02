package javax.swing;

import java.awt.*;
import java.text.*;
import java.awt.geom.*;
import javax.accessibility.*;
import javax.swing.text.*;
import javax.swing.text.html.*;
import javax.swing.plaf.basic.*;
import java.util.*;

class JLabel$AccessibleJLabel$LabelKeyBinding implements AccessibleKeyBinding {
    /*synthetic*/ final JLabel$AccessibleJLabel this$1;
    int mnemonic;
    
    JLabel$AccessibleJLabel$LabelKeyBinding(/*synthetic*/ final JLabel$AccessibleJLabel this$1, int mnemonic) {
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
