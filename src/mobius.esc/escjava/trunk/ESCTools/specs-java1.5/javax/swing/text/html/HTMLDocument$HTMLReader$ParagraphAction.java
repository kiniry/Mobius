package javax.swing.text.html;

import java.util.*;
import java.io.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.swing.undo.*;

public class HTMLDocument$HTMLReader$ParagraphAction extends HTMLDocument$HTMLReader$BlockAction {
    /*synthetic*/ final HTMLDocument$HTMLReader this$1;
    
    public HTMLDocument$HTMLReader$ParagraphAction(/*synthetic*/ final HTMLDocument$HTMLReader this$1) {
        super(this$1);
        this.this$1 = this$1;
    }
    
    public void start(HTML$Tag t, MutableAttributeSet a) {
        super.start(t, a);
        this$1.inParagraph = true;
    }
    
    public void end(HTML$Tag t) {
        super.end(t);
        this$1.inParagraph = false;
    }
}
