package javax.swing.text.html;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.util.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.accessibility.*;

class AccessibleHTML$ElementInfo {
    
    /*synthetic*/ static void access$1800(AccessibleHTML$ElementInfo x0, DocumentEvent x1) {
        x0.update(x1);
    }
    /*synthetic*/ final AccessibleHTML this$0;
    private ArrayList children;
    private Element element;
    private AccessibleHTML$ElementInfo parent;
    private boolean isValid;
    private boolean canBeValid;
    
    AccessibleHTML$ElementInfo(/*synthetic*/ final AccessibleHTML this$0, Element element) {
        this(this$0, element, null);
    }
    
    AccessibleHTML$ElementInfo(/*synthetic*/ final AccessibleHTML this$0, Element element, AccessibleHTML$ElementInfo parent) {
        this.this$0 = this$0;
        
        this.element = element;
        this.parent = parent;
        isValid = false;
        canBeValid = true;
    }
    
    protected void validate() {
        isValid = true;
        loadChildren(getElement());
    }
    
    protected void loadChildren(Element parent) {
        if (!parent.isLeaf()) {
            for (int counter = 0, maxCounter = parent.getElementCount(); counter < maxCounter; counter++) {
                Element e = parent.getElement(counter);
                AccessibleHTML$ElementInfo childInfo = this$0.createElementInfo(e, this);
                if (childInfo != null) {
                    addChild(childInfo);
                } else {
                    loadChildren(e);
                }
            }
        }
    }
    
    public int getIndexInParent() {
        if (parent == null || !parent.isValid()) {
            return -1;
        }
        return parent.indexOf(this);
    }
    
    public Element getElement() {
        return element;
    }
    
    public AccessibleHTML$ElementInfo getParent() {
        return parent;
    }
    
    public int indexOf(AccessibleHTML$ElementInfo child) {
        ArrayList children = this.children;
        if (children != null) {
            return children.indexOf(child);
        }
        return -1;
    }
    
    public AccessibleHTML$ElementInfo getChild(int index) {
        if (validateIfNecessary()) {
            ArrayList children = this.children;
            if (children != null && index >= 0 && index < children.size()) {
                return (AccessibleHTML$ElementInfo)(AccessibleHTML$ElementInfo)children.get(index);
            }
        }
        return null;
    }
    
    public int getChildCount() {
        validateIfNecessary();
        return (children == null) ? 0 : children.size();
    }
    
    protected void addChild(AccessibleHTML$ElementInfo child) {
        if (children == null) {
            children = new ArrayList();
        }
        children.add(child);
    }
    
    protected View getView() {
        if (!validateIfNecessary()) {
            return null;
        }
        Object lock = AccessibleHTML.access$1300(this$0);
        try {
            View rootView = AccessibleHTML.access$1400(this$0);
            Element e = getElement();
            int start = e.getStartOffset();
            if (rootView != null) {
                return getView(rootView, e, start);
            }
            return null;
        } finally {
            AccessibleHTML.access$1500(this$0, lock);
        }
    }
    
    public Rectangle getBounds() {
        if (!validateIfNecessary()) {
            return null;
        }
        Object lock = AccessibleHTML.access$1300(this$0);
        try {
            Rectangle bounds = AccessibleHTML.access$1600(this$0);
            View rootView = AccessibleHTML.access$1400(this$0);
            Element e = getElement();
            if (bounds != null && rootView != null) {
                try {
                    return rootView.modelToView(e.getStartOffset(), Position$Bias.Forward, e.getEndOffset(), Position$Bias.Backward, bounds).getBounds();
                } catch (BadLocationException ble) {
                }
            }
        } finally {
            AccessibleHTML.access$1500(this$0, lock);
        }
        return null;
    }
    
    protected boolean isValid() {
        return isValid;
    }
    
    protected AttributeSet getAttributes() {
        if (validateIfNecessary()) {
            return getElement().getAttributes();
        }
        return null;
    }
    
    protected AttributeSet getViewAttributes() {
        if (validateIfNecessary()) {
            View view = getView();
            if (view != null) {
                return view.getElement().getAttributes();
            }
            return getElement().getAttributes();
        }
        return null;
    }
    
    protected int getIntAttr(AttributeSet attrs, Object key, int deflt) {
        if (attrs != null && attrs.isDefined(key)) {
            int i;
            String val = (String)(String)attrs.getAttribute(key);
            if (val == null) {
                i = deflt;
            } else {
                try {
                    i = Math.max(0, Integer.parseInt(val));
                } catch (NumberFormatException x) {
                    i = deflt;
                }
            }
            return i;
        }
        return deflt;
    }
    
    protected boolean validateIfNecessary() {
        if (!isValid() && canBeValid) {
            children = null;
            Object lock = AccessibleHTML.access$1300(this$0);
            try {
                validate();
            } finally {
                AccessibleHTML.access$1500(this$0, lock);
            }
        }
        return isValid();
    }
    
    protected void invalidate(boolean first) {
        if (!isValid()) {
            if (canBeValid && !first) {
                canBeValid = false;
            }
            return;
        }
        isValid = false;
        canBeValid = first;
        if (children != null) {
            for (int counter = 0; counter < children.size(); counter++) {
                ((AccessibleHTML$ElementInfo)(AccessibleHTML$ElementInfo)children.get(counter)).invalidate(false);
            }
            children = null;
        }
    }
    
    private View getView(View parent, Element e, int start) {
        if (parent.getElement() == e) {
            return parent;
        }
        int index = parent.getViewIndex(start, Position$Bias.Forward);
        if (index != -1 && index < parent.getViewCount()) {
            return getView(parent.getView(index), e, start);
        }
        return null;
    }
    
    private int getClosestInfoIndex(int index) {
        for (int counter = 0; counter < getChildCount(); counter++) {
            AccessibleHTML$ElementInfo info = getChild(counter);
            if (index < info.getElement().getEndOffset() || index == info.getElement().getStartOffset()) {
                return counter;
            }
        }
        return -1;
    }
    
    private void update(DocumentEvent e) {
        if (!isValid()) {
            return;
        }
        AccessibleHTML$ElementInfo parent = getParent();
        Element element = getElement();
        do {
            DocumentEvent$ElementChange ec = e.getChange(element);
            if (ec != null) {
                if (element == getElement()) {
                    invalidate(true);
                } else if (parent != null) {
                    parent.invalidate(parent == AccessibleHTML.access$1700(this$0));
                }
                return;
            }
            element = element.getParentElement();
        }         while (parent != null && element != null && element != parent.getElement());
        if (getChildCount() > 0) {
            Element elem = getElement();
            int pos = e.getOffset();
            int index0 = getClosestInfoIndex(pos);
            if (index0 == -1 && e.getType() == DocumentEvent$EventType.REMOVE && pos >= elem.getEndOffset()) {
                index0 = getChildCount() - 1;
            }
            AccessibleHTML$ElementInfo info = (index0 >= 0) ? getChild(index0) : null;
            if (info != null && (info.getElement().getStartOffset() == pos) && (pos > 0)) {
                index0 = Math.max(index0 - 1, 0);
            }
            int index1;
            if (e.getType() != DocumentEvent$EventType.REMOVE) {
                index1 = getClosestInfoIndex(pos + e.getLength());
                if (index1 < 0) {
                    index1 = getChildCount() - 1;
                }
            } else {
                index1 = index0;
                while ((index1 + 1) < getChildCount() && getChild(index1 + 1).getElement().getEndOffset() == getChild(index1 + 1).getElement().getStartOffset()) {
                    index1++;
                }
            }
            index0 = Math.max(index0, 0);
            for (int i = index0; i <= index1 && isValid(); i++) {
                getChild(i).update(e);
            }
        }
    }
}
