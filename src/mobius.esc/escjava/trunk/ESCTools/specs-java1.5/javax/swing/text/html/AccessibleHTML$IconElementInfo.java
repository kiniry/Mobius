package javax.swing.text.html;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.util.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.accessibility.*;

class AccessibleHTML$IconElementInfo extends AccessibleHTML$ElementInfo implements Accessible {
    
    /*synthetic*/ static int access$902(AccessibleHTML$IconElementInfo x0, int x1) {
        return x0.height = x1;
    }
    
    /*synthetic*/ static int access$900(AccessibleHTML$IconElementInfo x0) {
        return x0.height;
    }
    
    /*synthetic*/ static int access$800(AccessibleHTML$IconElementInfo x0, Object x1) {
        return x0.getImageSize(x1);
    }
    
    /*synthetic*/ static int access$702(AccessibleHTML$IconElementInfo x0, int x1) {
        return x0.width = x1;
    }
    
    /*synthetic*/ static int access$700(AccessibleHTML$IconElementInfo x0) {
        return x0.width;
    }
    /*synthetic*/ final AccessibleHTML this$0;
    private int width = -1;
    private int height = -1;
    
    AccessibleHTML$IconElementInfo(/*synthetic*/ final AccessibleHTML this$0, Element element, AccessibleHTML$ElementInfo parent) {
        this.this$0 = this$0;
        super(this$0, element, parent);
    }
    
    protected void invalidate(boolean first) {
        super.invalidate(first);
        width = height = -1;
    }
    
    private int getImageSize(Object key) {
        if (validateIfNecessary()) {
            int size = getIntAttr(getAttributes(), key, -1);
            if (size == -1) {
                View v = getView();
                size = 0;
                if (v instanceof ImageView) {
                    Image img = ((ImageView)(ImageView)v).getImage();
                    if (img != null) {
                        if (key == HTML$Attribute.WIDTH) {
                            size = img.getWidth(null);
                        } else {
                            size = img.getHeight(null);
                        }
                    }
                }
            }
            return size;
        }
        return 0;
    }
    private AccessibleContext accessibleContext;
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new AccessibleHTML$IconElementInfo$IconAccessibleContext(this, this);
        }
        return accessibleContext;
    }
    {
    }
}
