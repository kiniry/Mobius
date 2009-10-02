package javax.swing.text.html;

import java.util.*;
import java.io.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.swing.undo.*;

public class HTMLDocument$RunElement extends AbstractDocument$LeafElement {
    /*synthetic*/ final HTMLDocument this$0;
    
    public HTMLDocument$RunElement(/*synthetic*/ final HTMLDocument this$0, Element parent, AttributeSet a, int offs0, int offs1) {
        this.this$0 = this$0;
        super(this$0, parent, a, offs0, offs1);
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
