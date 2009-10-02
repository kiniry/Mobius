package javax.swing.text.html;

import javax.swing.text.*;
import java.util.*;

class MuxingAttributeSet$MuxingAttributeNameEnumeration implements Enumeration {
    /*synthetic*/ final MuxingAttributeSet this$0;
    
    MuxingAttributeSet$MuxingAttributeNameEnumeration(/*synthetic*/ final MuxingAttributeSet this$0) {
        this.this$0 = this$0;
        
        updateEnum();
    }
    
    public boolean hasMoreElements() {
        if (currentEnum == null) {
            return false;
        }
        return currentEnum.hasMoreElements();
    }
    
    public Object nextElement() {
        if (currentEnum == null) {
            throw new NoSuchElementException("No more names");
        }
        Object retObject = currentEnum.nextElement();
        if (!currentEnum.hasMoreElements()) {
            updateEnum();
        }
        return retObject;
    }
    
    void updateEnum() {
        AttributeSet[] as = this$0.getAttributes();
        currentEnum = null;
        while (currentEnum == null && attrIndex < as.length) {
            currentEnum = as[attrIndex++].getAttributeNames();
            if (!currentEnum.hasMoreElements()) {
                currentEnum = null;
            }
        }
    }
    private int attrIndex;
    private Enumeration currentEnum;
}
