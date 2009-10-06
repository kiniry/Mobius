package javax.swing.text.html;

import java.util.*;
import java.io.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.swing.undo.*;

class HTMLDocument$HTMLReader$TitleAction extends HTMLDocument$HTMLReader$HiddenAction {
    /*synthetic*/ final HTMLDocument$HTMLReader this$1;
    
    HTMLDocument$HTMLReader$TitleAction(/*synthetic*/ final HTMLDocument$HTMLReader this$1) {
        super(this$1);
        this.this$1 = this$1;
    }
    
    public void start(HTML$Tag t, MutableAttributeSet attr) {
        this$1.inTitle = true;
        super.start(t, attr);
    }
    
    public void end(HTML$Tag t) {
        this$1.inTitle = false;
        super.end(t);
    }
    
    boolean isEmpty(HTML$Tag t) {
        return false;
    }
}
