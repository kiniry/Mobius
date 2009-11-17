package javax.swing.text;

import java.io.*;
import java.awt.*;
import javax.swing.event.*;

class StyledEditorKit$1 extends SimpleAttributeSet {
    /*synthetic*/ final StyledEditorKit this$0;
    
    StyledEditorKit$1(/*synthetic*/ final StyledEditorKit this$0) {
        this.this$0 = this$0;
        
    }
    
    public AttributeSet getResolveParent() {
        return (this$0.currentParagraph != null) ? this$0.currentParagraph.getAttributes() : null;
    }
    
    public Object clone() {
        return new SimpleAttributeSet(this);
    }
}
