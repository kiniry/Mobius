package javax.swing.text.html;

import java.util.*;
import java.io.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.swing.undo.*;

class HTMLDocument$HTMLReader$AnchorAction extends HTMLDocument$HTMLReader$CharacterAction {
    /*synthetic*/ final HTMLDocument$HTMLReader this$1;
    
    HTMLDocument$HTMLReader$AnchorAction(/*synthetic*/ final HTMLDocument$HTMLReader this$1) {
        super(this$1);
        this.this$1 = this$1;
    }
    
    public void start(HTML$Tag t, MutableAttributeSet attr) {
        this$1.emptyAnchor = true;
        super.start(t, attr);
    }
    
    public void end(HTML$Tag t) {
        if (this$1.emptyAnchor) {
            char[] one = new char[1];
            one[0] = '\n';
            this$1.addContent(one, 0, 1);
        }
        super.end(t);
    }
}
