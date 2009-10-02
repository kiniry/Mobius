package javax.swing.text.html;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.util.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.accessibility.*;

public class AccessibleHTML$IconElementInfo$IconAccessibleContext extends AccessibleHTML$HTMLAccessibleContext implements AccessibleIcon {
    /*synthetic*/ final AccessibleHTML$IconElementInfo this$1;
    
    public AccessibleHTML$IconElementInfo$IconAccessibleContext(/*synthetic*/ final AccessibleHTML$IconElementInfo this$1, AccessibleHTML$ElementInfo elementInfo) {
        this.this$1 = this$1;
        super(this$1.this$0, elementInfo);
    }
    
    public String getAccessibleName() {
        return getAccessibleIconDescription();
    }
    
    public String getAccessibleDescription() {
        return AccessibleHTML.access$300(this$1.this$0).getContentType();
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.ICON;
    }
    
    public AccessibleIcon[] getAccessibleIcon() {
        AccessibleIcon[] icons = new AccessibleIcon[1];
        icons[0] = this;
        return icons;
    }
    
    public String getAccessibleIconDescription() {
        return ((ImageView)(ImageView)this$1.getView()).getAltText();
    }
    
    public void setAccessibleIconDescription(String description) {
    }
    
    public int getAccessibleIconWidth() {
        if (AccessibleHTML.IconElementInfo.access$700(this$1) == -1) {
            AccessibleHTML.IconElementInfo.access$702(this$1, AccessibleHTML.IconElementInfo.access$800(this$1, HTML$Attribute.WIDTH));
        }
        return AccessibleHTML.IconElementInfo.access$700(this$1);
    }
    
    public int getAccessibleIconHeight() {
        if (AccessibleHTML.IconElementInfo.access$900(this$1) == -1) {
            AccessibleHTML.IconElementInfo.access$902(this$1, AccessibleHTML.IconElementInfo.access$800(this$1, HTML$Attribute.HEIGHT));
        }
        return AccessibleHTML.IconElementInfo.access$900(this$1);
    }
}
