package javax.swing.text.html;

import java.util.*;
import java.io.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.swing.undo.*;

class HTMLDocument$HTMLReader$FormTagAction extends HTMLDocument$HTMLReader$BlockAction {
    
    /*synthetic*/ HTMLDocument$HTMLReader$FormTagAction(HTMLDocument.HTMLReader x0, javax.swing.text.html.HTMLDocument$1 x1) {
        this(x0);
    }
    /*synthetic*/ final HTMLDocument$HTMLReader this$1;
    
    private HTMLDocument$HTMLReader$FormTagAction(/*synthetic*/ final HTMLDocument$HTMLReader this$1) {
        this.this$1 = this$1;
        super(this$1);
    }
    
    public void start(HTML$Tag t, MutableAttributeSet attr) {
        super.start(t, attr);
        HTMLDocument.access$702(this$1.this$0, new HashMap());
    }
    
    public void end(HTML$Tag t) {
        super.end(t);
        HTMLDocument.access$702(this$1.this$0, null);
    }
}
