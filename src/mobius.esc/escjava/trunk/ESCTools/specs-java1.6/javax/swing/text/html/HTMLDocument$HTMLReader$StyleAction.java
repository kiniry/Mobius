package javax.swing.text.html;

import java.util.*;
import java.io.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.swing.undo.*;

class HTMLDocument$HTMLReader$StyleAction extends HTMLDocument$HTMLReader$TagAction {
    /*synthetic*/ final HTMLDocument$HTMLReader this$1;
    
    HTMLDocument$HTMLReader$StyleAction(/*synthetic*/ final HTMLDocument$HTMLReader this$1) {
        super(this$1);
        this.this$1 = this$1;
    }
    
    public void start(HTML$Tag t, MutableAttributeSet a) {
        if (this$1.inHead) {
            if (this$1.styles == null) {
                this$1.styles = new Vector(3);
            }
            this$1.styles.addElement(t);
            this$1.styles.addElement(a.getAttribute(HTML$Attribute.TYPE));
            this$1.inStyle = true;
        }
    }
    
    public void end(HTML$Tag t) {
        this$1.inStyle = false;
    }
    
    boolean isEmpty(HTML$Tag t) {
        return false;
    }
}
