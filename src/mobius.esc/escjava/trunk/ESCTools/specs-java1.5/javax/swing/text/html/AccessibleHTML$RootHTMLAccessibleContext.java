package javax.swing.text.html;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.util.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.accessibility.*;

class AccessibleHTML$RootHTMLAccessibleContext extends AccessibleHTML$HTMLAccessibleContext {
    /*synthetic*/ final AccessibleHTML this$0;
    
    public AccessibleHTML$RootHTMLAccessibleContext(/*synthetic*/ final AccessibleHTML this$0, AccessibleHTML$ElementInfo elementInfo) {
        super(this$0, elementInfo);
        this.this$0 = this$0;
    }
    
    public String getAccessibleName() {
        if (AccessibleHTML.access$200(this$0) != null) {
            return (String)(String)AccessibleHTML.access$200(this$0).getProperty(Document.TitleProperty);
        } else {
            return null;
        }
    }
    
    public String getAccessibleDescription() {
        return AccessibleHTML.access$300(this$0).getContentType();
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.TEXT;
    }
}
