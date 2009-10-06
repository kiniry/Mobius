package javax.swing.text.html;

import java.util.*;
import java.io.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.swing.undo.*;

public class HTMLDocument$HTMLReader$IsindexAction extends HTMLDocument$HTMLReader$TagAction {
    /*synthetic*/ final HTMLDocument$HTMLReader this$1;
    
    public HTMLDocument$HTMLReader$IsindexAction(/*synthetic*/ final HTMLDocument$HTMLReader this$1) {
        super(this$1);
        this.this$1 = this$1;
    }
    
    public void start(HTML$Tag t, MutableAttributeSet a) {
        this$1.blockOpen(HTML$Tag.IMPLIED, new SimpleAttributeSet());
        this$1.addSpecialElement(t, a);
        this$1.blockClose(HTML$Tag.IMPLIED);
    }
}
