package javax.swing.text.html;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.util.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.accessibility.*;

class AccessibleHTML$TextElementInfo extends AccessibleHTML$ElementInfo implements Accessible {
    /*synthetic*/ final AccessibleHTML this$0;
    
    AccessibleHTML$TextElementInfo(/*synthetic*/ final AccessibleHTML this$0, Element element, AccessibleHTML$ElementInfo parent) {
        super(this$0, element, parent);
        this.this$0 = this$0;
    }
    private AccessibleContext accessibleContext;
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new AccessibleHTML$TextElementInfo$TextAccessibleContext(this, this);
        }
        return accessibleContext;
    }
    {
    }
}
