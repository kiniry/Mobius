package javax.swing.text.html;

import java.util.*;
import java.io.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.swing.undo.*;

class HTMLDocument$HTMLReader$LinkAction extends HTMLDocument$HTMLReader$HiddenAction {
    /*synthetic*/ final HTMLDocument$HTMLReader this$1;
    
    HTMLDocument$HTMLReader$LinkAction(/*synthetic*/ final HTMLDocument$HTMLReader this$1) {
        super(this$1);
        this.this$1 = this$1;
    }
    
    public void start(HTML$Tag t, MutableAttributeSet a) {
        String rel = (String)(String)a.getAttribute(HTML$Attribute.REL);
        if (rel != null) {
            rel = rel.toLowerCase();
            if (rel.equals("stylesheet") || rel.equals("alternate stylesheet")) {
                if (this$1.styles == null) {
                    this$1.styles = new Vector(3);
                }
                this$1.styles.addElement(t);
                this$1.styles.addElement(a.copyAttributes());
            }
        }
        super.start(t, a);
    }
}
