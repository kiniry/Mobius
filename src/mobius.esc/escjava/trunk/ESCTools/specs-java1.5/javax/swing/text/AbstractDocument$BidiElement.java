package javax.swing.text;

import java.util.*;
import java.io.*;
import javax.swing.undo.*;
import javax.swing.event.*;

class AbstractDocument$BidiElement extends AbstractDocument$LeafElement {
    /*synthetic*/ final AbstractDocument this$0;
    
    AbstractDocument$BidiElement(/*synthetic*/ final AbstractDocument this$0, Element parent, int start, int end, int level) {
        this.this$0 = this$0;
        super(this$0, parent, new SimpleAttributeSet(), start, end);
        addAttribute(StyleConstants.BidiLevel, new Integer(level));
    }
    
    public String getName() {
        return "bidi level";
    }
    
    int getLevel() {
        Integer o = (Integer)(Integer)getAttribute(StyleConstants.BidiLevel);
        if (o != null) {
            return o.intValue();
        }
        return 0;
    }
    
    boolean isLeftToRight() {
        return ((getLevel() % 2) == 0);
    }
}
