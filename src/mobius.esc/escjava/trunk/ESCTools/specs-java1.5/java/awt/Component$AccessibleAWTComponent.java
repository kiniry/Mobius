package java.awt;

import java.util.Locale;
import java.awt.event.*;
import java.io.Serializable;
import java.beans.PropertyChangeListener;
import javax.accessibility.*;
import javax.accessibility.*;
import java.util.logging.*;

public abstract class Component$AccessibleAWTComponent extends AccessibleContext implements Serializable, AccessibleComponent {
    /*synthetic*/ final Component this$0;
    private static final long serialVersionUID = 642321655757800191L;
    
    protected Component$AccessibleAWTComponent(/*synthetic*/ final Component this$0) {
        this.this$0 = this$0;
        
    }
    protected ComponentListener accessibleAWTComponentHandler = null;
    protected FocusListener accessibleAWTFocusHandler = null;
    {
    }
    {
    }
    
    public void addPropertyChangeListener(PropertyChangeListener listener) {
        if (accessibleAWTComponentHandler == null) {
            accessibleAWTComponentHandler = new Component$AccessibleAWTComponent$AccessibleAWTComponentHandler(this);
            this$0.addComponentListener(accessibleAWTComponentHandler);
        }
        if (accessibleAWTFocusHandler == null) {
            accessibleAWTFocusHandler = new Component$AccessibleAWTComponent$AccessibleAWTFocusHandler(this);
            this$0.addFocusListener(accessibleAWTFocusHandler);
        }
        super.addPropertyChangeListener(listener);
    }
    
    public void removePropertyChangeListener(PropertyChangeListener listener) {
        if (accessibleAWTComponentHandler != null) {
            this$0.removeComponentListener(accessibleAWTComponentHandler);
            accessibleAWTComponentHandler = null;
        }
        if (accessibleAWTFocusHandler != null) {
            this$0.removeFocusListener(accessibleAWTFocusHandler);
            accessibleAWTFocusHandler = null;
        }
        super.removePropertyChangeListener(listener);
    }
    
    public String getAccessibleName() {
        return accessibleName;
    }
    
    public String getAccessibleDescription() {
        return accessibleDescription;
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.AWT_COMPONENT;
    }
    
    public AccessibleStateSet getAccessibleStateSet() {
        return this$0.getAccessibleStateSet();
    }
    
    public Accessible getAccessibleParent() {
        if (accessibleParent != null) {
            return accessibleParent;
        } else {
            Container parent = this$0.getParent();
            if (parent instanceof Accessible) {
                return (Accessible)(javax.accessibility.Accessible)parent;
            }
        }
        return null;
    }
    
    public int getAccessibleIndexInParent() {
        return this$0.getAccessibleIndexInParent();
    }
    
    public int getAccessibleChildrenCount() {
        return 0;
    }
    
    public Accessible getAccessibleChild(int i) {
        return null;
    }
    
    public Locale getLocale() {
        return this$0.getLocale();
    }
    
    public AccessibleComponent getAccessibleComponent() {
        return this;
    }
    
    public Color getBackground() {
        return this$0.getBackground();
    }
    
    public void setBackground(Color c) {
        this$0.setBackground(c);
    }
    
    public Color getForeground() {
        return this$0.getForeground();
    }
    
    public void setForeground(Color c) {
        this$0.setForeground(c);
    }
    
    public Cursor getCursor() {
        return this$0.getCursor();
    }
    
    public void setCursor(Cursor cursor) {
        this$0.setCursor(cursor);
    }
    
    public Font getFont() {
        return this$0.getFont();
    }
    
    public void setFont(Font f) {
        this$0.setFont(f);
    }
    
    public FontMetrics getFontMetrics(Font f) {
        if (f == null) {
            return null;
        } else {
            return this$0.getFontMetrics(f);
        }
    }
    
    public boolean isEnabled() {
        return this$0.isEnabled();
    }
    
    public void setEnabled(boolean b) {
        boolean old = this$0.isEnabled();
        this$0.setEnabled(b);
        if (b != old) {
            if (this$0.accessibleContext != null) {
                if (b) {
                    this$0.accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, null, AccessibleState.ENABLED);
                } else {
                    this$0.accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, AccessibleState.ENABLED, null);
                }
            }
        }
    }
    
    public boolean isVisible() {
        return this$0.isVisible();
    }
    
    public void setVisible(boolean b) {
        boolean old = this$0.isVisible();
        this$0.setVisible(b);
        if (b != old) {
            if (this$0.accessibleContext != null) {
                if (b) {
                    this$0.accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, null, AccessibleState.VISIBLE);
                } else {
                    this$0.accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, AccessibleState.VISIBLE, null);
                }
            }
        }
    }
    
    public boolean isShowing() {
        return this$0.isShowing();
    }
    
    public boolean contains(Point p) {
        return this$0.contains(p);
    }
    
    public Point getLocationOnScreen() {
        synchronized (this$0.getTreeLock()) {
            if (this$0.isShowing()) {
                return this$0.getLocationOnScreen();
            } else {
                return null;
            }
        }
    }
    
    public Point getLocation() {
        return this$0.getLocation();
    }
    
    public void setLocation(Point p) {
        this$0.setLocation(p);
    }
    
    public Rectangle getBounds() {
        return this$0.getBounds();
    }
    
    public void setBounds(Rectangle r) {
        this$0.setBounds(r);
    }
    
    public Dimension getSize() {
        return this$0.getSize();
    }
    
    public void setSize(Dimension d) {
        this$0.setSize(d);
    }
    
    public Accessible getAccessibleAt(Point p) {
        return null;
    }
    
    public boolean isFocusTraversable() {
        return this$0.isFocusTraversable();
    }
    
    public void requestFocus() {
        this$0.requestFocus();
    }
    
    public void addFocusListener(FocusListener l) {
        this$0.addFocusListener(l);
    }
    
    public void removeFocusListener(FocusListener l) {
        this$0.removeFocusListener(l);
    }
}
