package java.awt;

import java.util.Locale;
import java.awt.event.*;
import javax.accessibility.*;

public class List$AccessibleAWTList$AccessibleAWTListChild extends Component$AccessibleAWTComponent implements Accessible {
    /*synthetic*/ final List$AccessibleAWTList this$1;
    private static final long serialVersionUID = 4412022926028300317L;
    private List parent;
    private int indexInParent;
    
    public List$AccessibleAWTList$AccessibleAWTListChild(/*synthetic*/ final List$AccessibleAWTList this$1, List parent, int indexInParent) {
        super(this$1.this$0);
        this.this$1 = this$1;
        this.parent = parent;
        this.setAccessibleParent(parent);
        this.indexInParent = indexInParent;
    }
    
    public AccessibleContext getAccessibleContext() {
        return this;
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.LIST_ITEM;
    }
    
    public AccessibleStateSet getAccessibleStateSet() {
        AccessibleStateSet states = super.getAccessibleStateSet();
        if (parent.isIndexSelected(indexInParent)) {
            states.add(AccessibleState.SELECTED);
        }
        return states;
    }
    
    public Locale getLocale() {
        return parent.getLocale();
    }
    
    public int getAccessibleIndexInParent() {
        return indexInParent;
    }
    
    public int getAccessibleChildrenCount() {
        return 0;
    }
    
    public Accessible getAccessibleChild(int i) {
        return null;
    }
    
    public Color getBackground() {
        return parent.getBackground();
    }
    
    public void setBackground(Color c) {
        parent.setBackground(c);
    }
    
    public Color getForeground() {
        return parent.getForeground();
    }
    
    public void setForeground(Color c) {
        parent.setForeground(c);
    }
    
    public Cursor getCursor() {
        return parent.getCursor();
    }
    
    public void setCursor(Cursor cursor) {
        parent.setCursor(cursor);
    }
    
    public Font getFont() {
        return parent.getFont();
    }
    
    public void setFont(Font f) {
        parent.setFont(f);
    }
    
    public FontMetrics getFontMetrics(Font f) {
        return parent.getFontMetrics(f);
    }
    
    public boolean isEnabled() {
        return parent.isEnabled();
    }
    
    public void setEnabled(boolean b) {
        parent.setEnabled(b);
    }
    
    public boolean isVisible() {
        return false;
    }
    
    public void setVisible(boolean b) {
        parent.setVisible(b);
    }
    
    public boolean isShowing() {
        return false;
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
        return false;
    }
    
    public void requestFocus() {
    }
    
    public void addFocusListener(FocusListener l) {
    }
    
    public void removeFocusListener(FocusListener l) {
    }
}
