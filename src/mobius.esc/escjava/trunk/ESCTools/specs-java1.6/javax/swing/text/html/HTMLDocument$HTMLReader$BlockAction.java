package javax.swing.text.html;

import java.util.*;
import java.io.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.swing.undo.*;

public class HTMLDocument$HTMLReader$BlockAction extends HTMLDocument$HTMLReader$TagAction {
    /*synthetic*/ final HTMLDocument$HTMLReader this$1;
    
    public HTMLDocument$HTMLReader$BlockAction(/*synthetic*/ final HTMLDocument$HTMLReader this$1) {
        super(this$1);
        this.this$1 = this$1;
    }
    
    public void start(HTML$Tag t, MutableAttributeSet attr) {
        this$1.blockOpen(t, attr);
    }
    
    public void end(HTML$Tag t) {
        this$1.blockClose(t);
    }
}
