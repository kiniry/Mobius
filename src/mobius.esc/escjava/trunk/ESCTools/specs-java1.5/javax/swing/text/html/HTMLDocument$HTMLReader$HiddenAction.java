package javax.swing.text.html;

import java.util.*;
import java.io.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.swing.undo.*;

public class HTMLDocument$HTMLReader$HiddenAction extends HTMLDocument$HTMLReader$TagAction {
    /*synthetic*/ final HTMLDocument$HTMLReader this$1;
    
    public HTMLDocument$HTMLReader$HiddenAction(/*synthetic*/ final HTMLDocument$HTMLReader this$1) {
        this.this$1 = this$1;
        super(this$1);
    }
    
    public void start(HTML$Tag t, MutableAttributeSet a) {
        this$1.addSpecialElement(t, a);
    }
    
    public void end(HTML$Tag t) {
        if (!isEmpty(t)) {
            MutableAttributeSet a = new SimpleAttributeSet();
            a.addAttribute(HTML$Attribute.ENDTAG, "true");
            this$1.addSpecialElement(t, a);
        }
    }
    
    boolean isEmpty(HTML$Tag t) {
        if (t == HTML$Tag.APPLET || t == HTML$Tag.SCRIPT) {
            return false;
        }
        return true;
    }
}
