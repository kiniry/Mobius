package javax.swing.text.html;

import java.util.*;
import java.io.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.swing.undo.*;

class HTMLDocument$HTMLReader$MapAction extends HTMLDocument$HTMLReader$TagAction {
    /*synthetic*/ final HTMLDocument$HTMLReader this$1;
    
    HTMLDocument$HTMLReader$MapAction(/*synthetic*/ final HTMLDocument$HTMLReader this$1) {
        super(this$1);
        this.this$1 = this$1;
    }
    
    public void start(HTML$Tag t, MutableAttributeSet a) {
        this$1.lastMap = new Map((String)(String)a.getAttribute(HTML$Attribute.NAME));
        this$1.this$0.addMap(this$1.lastMap);
    }
    
    public void end(HTML$Tag t) {
    }
}
