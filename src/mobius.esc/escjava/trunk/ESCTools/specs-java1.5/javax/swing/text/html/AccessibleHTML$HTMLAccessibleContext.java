package javax.swing.text.html;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.util.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.accessibility.*;

public abstract class AccessibleHTML$HTMLAccessibleContext extends AccessibleContext implements Accessible, AccessibleComponent {
    /*synthetic*/ final AccessibleHTML this$0;
    protected AccessibleHTML$ElementInfo elementInfo;
    
    public AccessibleHTML$HTMLAccessibleContext(/*synthetic*/ final AccessibleHTML this$0, AccessibleHTML$ElementInfo elementInfo) {
        this.this$0 = this$0;
        
        this.elementInfo = elementInfo;
    }
    
    public AccessibleContext getAccessibleContext() {
        return this;
    }
    
    public AccessibleStateSet getAccessibleStateSet() {
        AccessibleStateSet states = new AccessibleStateSet();
        Component comp = AccessibleHTML.access$400(this$0);
        if (comp.isEnabled()) {
            states.add(AccessibleState.ENABLED);
        }
        if (comp instanceof JTextComponent && ((JTextComponent)(JTextComponent)comp).isEditable()) {
            states.add(AccessibleState.EDITABLE);
            states.add(AccessibleState.FOCUSABLE);
        }
        if (comp.isVisible()) {
            states.add(AccessibleState.VISIBLE);
        }
        if (comp.isShowing()) {
            states.add(AccessibleState.SHOWING);
        }
        return states;
    }
    
    public int getAccessibleIndexInParent() {
        return elementInfo.getIndexInParent();
    }
    
    public int getAccessibleChildrenCount() {
        return elementInfo.getChildCount();
    }
    
    public Accessible getAccessibleChild(int i) {
        AccessibleHTML$ElementInfo childInfo = elementInfo.getChild(i);
        if (childInfo != null && childInfo instanceof Accessible) {
            return (Accessible)(Accessible)childInfo;
        } else {
            return null;
        }
    }
    
    public Locale getLocale() throws IllegalComponentStateException {
        return AccessibleHTML.access$300(this$0).getLocale();
    }
    
    public AccessibleComponent getAccessibleComponent() {
        return this;
    }
    
    public Color getBackground() {
        return AccessibleHTML.access$400(this$0).getBackground();
    }
    
    public void setBackground(Color c) {
        AccessibleHTML.access$400(this$0).setBackground(c);
    }
    
    public Color getForeground() {
        return AccessibleHTML.access$400(this$0).getForeground();
    }
    
    public void setForeground(Color c) {
        AccessibleHTML.access$400(this$0).setForeground(c);
    }
    
    public Cursor getCursor() {
        return AccessibleHTML.access$400(this$0).getCursor();
    }
    
    public void setCursor(Cursor cursor) {
        AccessibleHTML.access$400(this$0).setCursor(cursor);
    }
    
    public Font getFont() {
        return AccessibleHTML.access$400(this$0).getFont();
    }
    
    public void setFont(Font f) {
        AccessibleHTML.access$400(this$0).setFont(f);
    }
    
    public FontMetrics getFontMetrics(Font f) {
        return AccessibleHTML.access$400(this$0).getFontMetrics(f);
    }
    
    public boolean isEnabled() {
        return AccessibleHTML.access$400(this$0).isEnabled();
    }
    
    public void setEnabled(boolean b) {
        AccessibleHTML.access$400(this$0).setEnabled(b);
    }
    
    public boolean isVisible() {
        return AccessibleHTML.access$400(this$0).isVisible();
    }
    
    public void setVisible(boolean b) {
        AccessibleHTML.access$400(this$0).setVisible(b);
    }
    
    public boolean isShowing() {
        return AccessibleHTML.access$400(this$0).isShowing();
    }
    
    public boolean contains(Point p) {
        Rectangle r = getBounds();
        if (r != null) {
            return r.contains(p.x, p.y);
        } else {
            return false;
        }
    }
    
    public Point getLocationOnScreen() {
        Point editorLocation = AccessibleHTML.access$400(this$0).getLocationOnScreen();
        Rectangle r = getBounds();
        if (r != null) {
            return new Point(editorLocation.x + r.x, editorLocation.y + r.y);
        } else {
            return null;
        }
    }
    
    public Point getLocation() {
        Rectangle r = getBounds();
        if (r != null) {
            return new Point(r.x, r.y);
        } else {
            return null;
        }
    }
    
    public void setLocation(Point p) {
    }
    
    public Rectangle getBounds() {
        return elementInfo.getBounds();
    }
    
    public void setBounds(Rectangle r) {
    }
    
    public Dimension getSize() {
        Rectangle r = getBounds();
        if (r != null) {
            return new Dimension(r.width, r.height);
        } else {
            return null;
        }
    }
    
    public void setSize(Dimension d) {
        Component comp = AccessibleHTML.access$400(this$0);
        comp.setSize(d);
    }
    
    public Accessible getAccessibleAt(Point p) {
        AccessibleHTML$ElementInfo innerMostElement = getElementInfoAt(AccessibleHTML.access$500(this$0), p);
        if (innerMostElement instanceof Accessible) {
            return (Accessible)(Accessible)innerMostElement;
        } else {
            return null;
        }
    }
    
    private AccessibleHTML$ElementInfo getElementInfoAt(AccessibleHTML$ElementInfo elementInfo, Point p) {
        if (elementInfo.getBounds() == null) {
            return null;
        }
        if (elementInfo.getChildCount() == 0 && elementInfo.getBounds().contains(p)) {
            return elementInfo;
        } else {
            if (elementInfo instanceof AccessibleHTML$TableElementInfo) {
                AccessibleHTML$ElementInfo captionInfo = ((AccessibleHTML$TableElementInfo)(AccessibleHTML$TableElementInfo)elementInfo).getCaptionInfo();
                if (captionInfo != null) {
                    Rectangle bounds = captionInfo.getBounds();
                    if (bounds != null && bounds.contains(p)) {
                        return captionInfo;
                    }
                }
            }
            for (int i = 0; i < elementInfo.getChildCount(); i++) {
                AccessibleHTML$ElementInfo childInfo = elementInfo.getChild(i);
                AccessibleHTML$ElementInfo retValue = getElementInfoAt(childInfo, p);
                if (retValue != null) {
                    return retValue;
                }
            }
        }
        return null;
    }
    
    public boolean isFocusTraversable() {
        Component comp = AccessibleHTML.access$400(this$0);
        if (comp instanceof JTextComponent) {
            if (((JTextComponent)(JTextComponent)comp).isEditable()) {
                return true;
            }
        }
        return false;
    }
    
    public void requestFocus() {
        if (!isFocusTraversable()) {
            return;
        }
        Component comp = AccessibleHTML.access$400(this$0);
        if (comp instanceof JTextComponent) {
            comp.requestFocusInWindow();
            try {
                if (elementInfo.validateIfNecessary()) {
                    Element elem = elementInfo.getElement();
                    ((JTextComponent)(JTextComponent)comp).setCaretPosition(elem.getStartOffset());
                    AccessibleContext ac = AccessibleHTML.access$300(this$0).getAccessibleContext();
                    PropertyChangeEvent pce = new PropertyChangeEvent(this, AccessibleContext.ACCESSIBLE_STATE_PROPERTY, null, AccessibleState.FOCUSED);
                    ac.firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, null, pce);
                }
            } catch (IllegalArgumentException e) {
            }
        }
    }
    
    public void addFocusListener(FocusListener l) {
        AccessibleHTML.access$400(this$0).addFocusListener(l);
    }
    
    public void removeFocusListener(FocusListener l) {
        AccessibleHTML.access$400(this$0).removeFocusListener(l);
    }
}
