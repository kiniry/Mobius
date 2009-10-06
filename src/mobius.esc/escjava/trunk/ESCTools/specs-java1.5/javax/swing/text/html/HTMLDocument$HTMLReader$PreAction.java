package javax.swing.text.html;

import java.util.*;
import java.io.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.swing.undo.*;

public class HTMLDocument$HTMLReader$PreAction extends HTMLDocument$HTMLReader$BlockAction {
    /*synthetic*/ final HTMLDocument$HTMLReader this$1;
    
    public HTMLDocument$HTMLReader$PreAction(/*synthetic*/ final HTMLDocument$HTMLReader this$1) {
        super(this$1);
        this.this$1 = this$1;
    }
    
    public void start(HTML$Tag t, MutableAttributeSet attr) {
        this$1.inPre = true;
        this$1.blockOpen(t, attr);
        attr.addAttribute(CSS$Attribute.WHITE_SPACE, "pre");
        this$1.blockOpen(HTML$Tag.IMPLIED, attr);
    }
    
    public void end(HTML$Tag t) {
        this$1.blockClose(HTML$Tag.IMPLIED);
        this$1.inPre = false;
        this$1.blockClose(t);
    }
}
