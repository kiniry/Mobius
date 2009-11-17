package javax.swing;

import java.awt.*;
import java.awt.image.*;
import java.io.Serializable;
import java.io.ObjectOutputStream;
import java.io.ObjectInputStream;
import java.io.IOException;
import java.util.Locale;
import javax.accessibility.*;

public class ImageIcon$AccessibleImageIcon extends AccessibleContext implements AccessibleIcon, Serializable {
    /*synthetic*/ final ImageIcon this$0;
    
    protected ImageIcon$AccessibleImageIcon(/*synthetic*/ final ImageIcon this$0) {
        this.this$0 = this$0;
        
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.ICON;
    }
    
    public AccessibleStateSet getAccessibleStateSet() {
        return null;
    }
    
    public Accessible getAccessibleParent() {
        return null;
    }
    
    public int getAccessibleIndexInParent() {
        return -1;
    }
    
    public int getAccessibleChildrenCount() {
        return 0;
    }
    
    public Accessible getAccessibleChild(int i) {
        return null;
    }
    
    public Locale getLocale() throws IllegalComponentStateException {
        return null;
    }
    
    public String getAccessibleIconDescription() {
        return this$0.getDescription();
    }
    
    public void setAccessibleIconDescription(String description) {
        this$0.setDescription(description);
    }
    
    public int getAccessibleIconHeight() {
        return this$0.height;
    }
    
    public int getAccessibleIconWidth() {
        return this$0.width;
    }
    
    private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException {
        s.defaultReadObject();
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
    }
}
