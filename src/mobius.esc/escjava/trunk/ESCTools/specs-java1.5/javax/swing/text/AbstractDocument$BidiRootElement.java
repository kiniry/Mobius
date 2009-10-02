package javax.swing.text;

import java.util.*;
import java.io.*;
import javax.swing.undo.*;
import javax.swing.event.*;

class AbstractDocument$BidiRootElement extends AbstractDocument$BranchElement {
    /*synthetic*/ final AbstractDocument this$0;
    
    AbstractDocument$BidiRootElement(/*synthetic*/ final AbstractDocument this$0) {
        this.this$0 = this$0;
        super(this$0, null, null);
    }
    
    public String getName() {
        return "bidi root";
    }
}
