package javax.swing.text.html;

import java.util.*;
import java.io.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.swing.undo.*;

public class HTMLDocument$BlockElement extends AbstractDocument$BranchElement {
    /*synthetic*/ final HTMLDocument this$0;
    
    public HTMLDocument$BlockElement(/*synthetic*/ final HTMLDocument this$0, Element parent, AttributeSet a) {
        super(this$0, parent, a);
        this.this$0 = this$0;
    }
    
    public String getName() {
        Object o = getAttribute(StyleConstants.NameAttribute);
        if (o != null) {
            return o.toString();
        }
        return super.getName();
    }
    
    public AttributeSet getResolveParent() {
        return null;
    }
}
