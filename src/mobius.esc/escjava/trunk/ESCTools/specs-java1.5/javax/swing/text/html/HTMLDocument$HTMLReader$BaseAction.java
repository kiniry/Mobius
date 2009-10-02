package javax.swing.text.html;

import java.util.*;
import java.net.URL;
import java.net.MalformedURLException;
import java.io.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.swing.undo.*;

class HTMLDocument$HTMLReader$BaseAction extends HTMLDocument$HTMLReader$TagAction {
    /*synthetic*/ final HTMLDocument$HTMLReader this$1;
    
    HTMLDocument$HTMLReader$BaseAction(/*synthetic*/ final HTMLDocument$HTMLReader this$1) {
        this.this$1 = this$1;
        super(this$1);
    }
    
    public void start(HTML$Tag t, MutableAttributeSet attr) {
        String href = (String)(String)attr.getAttribute(HTML$Attribute.HREF);
        if (href != null) {
            try {
                URL newBase = new URL(this$1.this$0.base, href);
                this$1.this$0.setBase(newBase);
                this$1.this$0.hasBaseTag = true;
            } catch (MalformedURLException ex) {
            }
        }
        HTMLDocument.access$1002(this$1.this$0, (String)(String)attr.getAttribute(HTML$Attribute.TARGET));
    }
}
