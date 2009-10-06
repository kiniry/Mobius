package javax.swing.text.html;

import java.util.*;
import java.io.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.swing.undo.*;

class HTMLDocument$HTMLReader$ObjectAction extends HTMLDocument$HTMLReader$SpecialAction {
    /*synthetic*/ final HTMLDocument$HTMLReader this$1;
    
    HTMLDocument$HTMLReader$ObjectAction(/*synthetic*/ final HTMLDocument$HTMLReader this$1) {
        super(this$1);
        this.this$1 = this$1;
    }
    
    public void start(HTML$Tag t, MutableAttributeSet a) {
        if (t == HTML$Tag.PARAM) {
            addParameter(a);
        } else {
            super.start(t, a);
        }
    }
    
    public void end(HTML$Tag t) {
        if (t != HTML$Tag.PARAM) {
            super.end(t);
        }
    }
    
    void addParameter(AttributeSet a) {
        String name = (String)(String)a.getAttribute(HTML$Attribute.NAME);
        String value = (String)(String)a.getAttribute(HTML$Attribute.VALUE);
        if ((name != null) && (value != null)) {
            DefaultStyledDocument$ElementSpec objSpec = (DefaultStyledDocument$ElementSpec)(DefaultStyledDocument$ElementSpec)this$1.parseBuffer.lastElement();
            MutableAttributeSet objAttr = (MutableAttributeSet)(MutableAttributeSet)objSpec.getAttributes();
            objAttr.addAttribute(name, value);
        }
    }
}
