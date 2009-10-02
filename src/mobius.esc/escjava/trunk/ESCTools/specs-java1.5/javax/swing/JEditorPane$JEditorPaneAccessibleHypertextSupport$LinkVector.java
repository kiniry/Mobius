package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.net.*;
import java.util.*;
import java.io.*;
import java.util.*;
import javax.swing.plaf.*;
import javax.swing.text.*;
import javax.swing.event.*;
import javax.swing.text.html.*;
import javax.accessibility.*;

class JEditorPane$JEditorPaneAccessibleHypertextSupport$LinkVector extends Vector {
    
    /*synthetic*/ JEditorPane$JEditorPaneAccessibleHypertextSupport$LinkVector(JEditorPane.JEditorPaneAccessibleHypertextSupport x0, javax.swing.JEditorPane$1 x1) {
        this(x0);
    }
    /*synthetic*/ final JEditorPane$JEditorPaneAccessibleHypertextSupport this$1;
    
    private JEditorPane$JEditorPaneAccessibleHypertextSupport$LinkVector(/*synthetic*/ final JEditorPane$JEditorPaneAccessibleHypertextSupport this$1) {
        this.this$1 = this$1;
        
    }
    
    public int baseElementIndex(Element e) {
        JEditorPane$JEditorPaneAccessibleHypertextSupport$HTMLLink l;
        for (int i = 0; i < elementCount; i++) {
            l = (JEditorPane$JEditorPaneAccessibleHypertextSupport$HTMLLink)(JEditorPane$JEditorPaneAccessibleHypertextSupport$HTMLLink)elementAt(i);
            if (l.element == e) {
                return i;
            }
        }
        return -1;
    }
}
