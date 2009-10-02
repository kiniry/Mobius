package java.awt;

import javax.accessibility.*;

public abstract class MenuComponent$AccessibleAWTMenuComponent extends AccessibleContext implements java.io.Serializable, AccessibleComponent, AccessibleSelection {
    /*synthetic*/ final MenuComponent this$0;
    private static final long serialVersionUID = -4269533416223798698L;
    
    protected MenuComponent$AccessibleAWTMenuComponent(/*synthetic*/ final MenuComponent this$0) {
        this.this$0 = this$0;
        
    }
    
    public AccessibleSelection getAccessibleSelection() {
        return this;
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
            MenuContainer parent = this$0.getParent();
            if (parent instanceof Accessible) {
                return (Accessible)(Accessible)parent;
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
    
    public java.util.Locale getLocale() {
        MenuContainer parent = this$0.getParent();
        if (parent instanceof Component) return ((Component)(Component)parent).getLocale(); else return java.util.Locale.getDefault();
    }
    
    public AccessibleComponent getAccessibleComponent() {
        return this;
    }
    
    public Color getBackground() {
        return null;
    }
    
    public void setBackground(Color c) {
    }
    
    public Color getForeground() {
        return null;
    }
    
    public void setForeground(Color c) {
    }
    
    public Cursor getCursor() {
        return null;
    }
    
    public void setCursor(Cursor cursor) {
    }
    
    public Font getFont() {
        return this$0.getFont();
    }
    
    public void setFont(Font f) {
        this$0.setFont(f);
    }
    
    public FontMetrics getFontMetrics(Font f) {
        return null;
    }
    
    public boolean isEnabled() {
        return true;
    }
    
    public void setEnabled(boolean b) {
    }
    
    public boolean isVisible() {
        return true;
    }
    
    public void setVisible(boolean b) {
    }
    
    public boolean isShowing() {
        return true;
    }
    
    public boolean contains(Point p) {
        return false;
    }
    
    public Point getLocationOnScreen() {
        return null;
    }
    
    public Point getLocation() {
        return null;
    }
    
    public void setLocation(Point p) {
    }
    
    public Rectangle getBounds() {
        return null;
    }
    
    public void setBounds(Rectangle r) {
    }
    
    public Dimension getSize() {
        return null;
    }
    
    public void setSize(Dimension d) {
    }
    
    public Accessible getAccessibleAt(Point p) {
        return null;
    }
    
    public boolean isFocusTraversable() {
        return true;
    }
    
    public void requestFocus() {
    }
    
    public void addFocusListener(java.awt.event.FocusListener l) {
    }
    
    public void removeFocusListener(java.awt.event.FocusListener l) {
    }
    
    public int getAccessibleSelectionCount() {
        return 0;
    }
    
    public Accessible getAccessibleSelection(int i) {
        return null;
    }
    
    public boolean isAccessibleChildSelected(int i) {
        return false;
    }
    
    public void addAccessibleSelection(int i) {
    }
    
    public void removeAccessibleSelection(int i) {
    }
    
    public void clearAccessibleSelection() {
    }
    
    public void selectAllAccessibleSelection() {
    }
}
