package javax.swing;

import java.awt.event.*;
import java.awt.*;
import java.util.Locale;
import java.beans.*;
import javax.swing.event.*;
import javax.accessibility.*;
import javax.swing.plaf.*;

public class JList$AccessibleJList$AccessibleJListChild extends AccessibleContext implements Accessible, AccessibleComponent {
    /*synthetic*/ final JList$AccessibleJList this$1;
    private JList parent = null;
    private int indexInParent;
    private Component component = null;
    private AccessibleContext accessibleContext = null;
    private ListModel listModel;
    private ListCellRenderer cellRenderer = null;
    
    public JList$AccessibleJList$AccessibleJListChild(/*synthetic*/ final JList$AccessibleJList this$1, JList parent, int indexInParent) {
        this.this$1 = this$1;
        
        this.parent = parent;
        this.setAccessibleParent(parent);
        this.indexInParent = indexInParent;
        if (parent != null) {
            listModel = parent.getModel();
            cellRenderer = parent.getCellRenderer();
        }
    }
    
    private Component getCurrentComponent() {
        return getComponentAtIndex(indexInParent);
    }
    
    private AccessibleContext getCurrentAccessibleContext() {
        Component c = getComponentAtIndex(indexInParent);
        if (c instanceof Accessible) {
            return ((Accessible)(Accessible)c).getAccessibleContext();
        } else {
            return null;
        }
    }
    
    private Component getComponentAtIndex(int index) {
        if (index < 0 || index >= listModel.getSize()) {
            return null;
        }
        if ((parent != null) && (listModel != null) && cellRenderer != null) {
            Object value = listModel.getElementAt(index);
            boolean isSelected = parent.isSelectedIndex(index);
            boolean isFocussed = parent.isFocusOwner() && (index == parent.getLeadSelectionIndex());
            return cellRenderer.getListCellRendererComponent(parent, value, index, isSelected, isFocussed);
        } else {
            return null;
        }
    }
    
    public AccessibleContext getAccessibleContext() {
        return this;
    }
    
    public String getAccessibleName() {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac != null) {
            return ac.getAccessibleName();
        } else {
            return null;
        }
    }
    
    public void setAccessibleName(String s) {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac != null) {
            ac.setAccessibleName(s);
        }
    }
    
    public String getAccessibleDescription() {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac != null) {
            return ac.getAccessibleDescription();
        } else {
            return null;
        }
    }
    
    public void setAccessibleDescription(String s) {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac != null) {
            ac.setAccessibleDescription(s);
        }
    }
    
    public AccessibleRole getAccessibleRole() {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac != null) {
            return ac.getAccessibleRole();
        } else {
            return null;
        }
    }
    
    public AccessibleStateSet getAccessibleStateSet() {
        AccessibleContext ac = getCurrentAccessibleContext();
        AccessibleStateSet s;
        if (ac != null) {
            s = ac.getAccessibleStateSet();
        } else {
            s = new AccessibleStateSet();
        }
        s = ac.getAccessibleStateSet();
        s.add(AccessibleState.SELECTABLE);
        if (parent.isFocusOwner() && (indexInParent == parent.getLeadSelectionIndex())) {
            s.add(AccessibleState.ACTIVE);
        }
        if (parent.isSelectedIndex(indexInParent)) {
            s.add(AccessibleState.SELECTED);
        }
        if (this.isShowing()) {
            s.add(AccessibleState.SHOWING);
        } else if (s.contains(AccessibleState.SHOWING)) {
            s.remove(AccessibleState.SHOWING);
        }
        if (this.isVisible()) {
            s.add(AccessibleState.VISIBLE);
        } else if (s.contains(AccessibleState.VISIBLE)) {
            s.remove(AccessibleState.VISIBLE);
        }
        s.add(AccessibleState.TRANSIENT);
        return s;
    }
    
    public int getAccessibleIndexInParent() {
        return indexInParent;
    }
    
    public int getAccessibleChildrenCount() {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac != null) {
            return ac.getAccessibleChildrenCount();
        } else {
            return 0;
        }
    }
    
    public Accessible getAccessibleChild(int i) {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac != null) {
            Accessible accessibleChild = ac.getAccessibleChild(i);
            ac.setAccessibleParent(this);
            return accessibleChild;
        } else {
            return null;
        }
    }
    
    public Locale getLocale() {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac != null) {
            return ac.getLocale();
        } else {
            return null;
        }
    }
    
    public void addPropertyChangeListener(PropertyChangeListener l) {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac != null) {
            ac.addPropertyChangeListener(l);
        }
    }
    
    public void removePropertyChangeListener(PropertyChangeListener l) {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac != null) {
            ac.removePropertyChangeListener(l);
        }
    }
    
    public AccessibleAction getAccessibleAction() {
        return getCurrentAccessibleContext().getAccessibleAction();
    }
    
    public AccessibleComponent getAccessibleComponent() {
        return this;
    }
    
    public AccessibleSelection getAccessibleSelection() {
        return getCurrentAccessibleContext().getAccessibleSelection();
    }
    
    public AccessibleText getAccessibleText() {
        return getCurrentAccessibleContext().getAccessibleText();
    }
    
    public AccessibleValue getAccessibleValue() {
        return getCurrentAccessibleContext().getAccessibleValue();
    }
    
    public Color getBackground() {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac instanceof AccessibleComponent) {
            return ((AccessibleComponent)(AccessibleComponent)ac).getBackground();
        } else {
            Component c = getCurrentComponent();
            if (c != null) {
                return c.getBackground();
            } else {
                return null;
            }
        }
    }
    
    public void setBackground(Color c) {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac instanceof AccessibleComponent) {
            ((AccessibleComponent)(AccessibleComponent)ac).setBackground(c);
        } else {
            Component cp = getCurrentComponent();
            if (cp != null) {
                cp.setBackground(c);
            }
        }
    }
    
    public Color getForeground() {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac instanceof AccessibleComponent) {
            return ((AccessibleComponent)(AccessibleComponent)ac).getForeground();
        } else {
            Component c = getCurrentComponent();
            if (c != null) {
                return c.getForeground();
            } else {
                return null;
            }
        }
    }
    
    public void setForeground(Color c) {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac instanceof AccessibleComponent) {
            ((AccessibleComponent)(AccessibleComponent)ac).setForeground(c);
        } else {
            Component cp = getCurrentComponent();
            if (cp != null) {
                cp.setForeground(c);
            }
        }
    }
    
    public Cursor getCursor() {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac instanceof AccessibleComponent) {
            return ((AccessibleComponent)(AccessibleComponent)ac).getCursor();
        } else {
            Component c = getCurrentComponent();
            if (c != null) {
                return c.getCursor();
            } else {
                Accessible ap = getAccessibleParent();
                if (ap instanceof AccessibleComponent) {
                    return ((AccessibleComponent)(AccessibleComponent)ap).getCursor();
                } else {
                    return null;
                }
            }
        }
    }
    
    public void setCursor(Cursor c) {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac instanceof AccessibleComponent) {
            ((AccessibleComponent)(AccessibleComponent)ac).setCursor(c);
        } else {
            Component cp = getCurrentComponent();
            if (cp != null) {
                cp.setCursor(c);
            }
        }
    }
    
    public Font getFont() {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac instanceof AccessibleComponent) {
            return ((AccessibleComponent)(AccessibleComponent)ac).getFont();
        } else {
            Component c = getCurrentComponent();
            if (c != null) {
                return c.getFont();
            } else {
                return null;
            }
        }
    }
    
    public void setFont(Font f) {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac instanceof AccessibleComponent) {
            ((AccessibleComponent)(AccessibleComponent)ac).setFont(f);
        } else {
            Component c = getCurrentComponent();
            if (c != null) {
                c.setFont(f);
            }
        }
    }
    
    public FontMetrics getFontMetrics(Font f) {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac instanceof AccessibleComponent) {
            return ((AccessibleComponent)(AccessibleComponent)ac).getFontMetrics(f);
        } else {
            Component c = getCurrentComponent();
            if (c != null) {
                return c.getFontMetrics(f);
            } else {
                return null;
            }
        }
    }
    
    public boolean isEnabled() {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac instanceof AccessibleComponent) {
            return ((AccessibleComponent)(AccessibleComponent)ac).isEnabled();
        } else {
            Component c = getCurrentComponent();
            if (c != null) {
                return c.isEnabled();
            } else {
                return false;
            }
        }
    }
    
    public void setEnabled(boolean b) {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac instanceof AccessibleComponent) {
            ((AccessibleComponent)(AccessibleComponent)ac).setEnabled(b);
        } else {
            Component c = getCurrentComponent();
            if (c != null) {
                c.setEnabled(b);
            }
        }
    }
    
    public boolean isVisible() {
        int fi = parent.getFirstVisibleIndex();
        int li = parent.getLastVisibleIndex();
        if (li == -1) {
            li = parent.getModel().getSize() - 1;
        }
        return ((indexInParent >= fi) && (indexInParent <= li));
    }
    
    public void setVisible(boolean b) {
    }
    
    public boolean isShowing() {
        return (parent.isShowing() && isVisible());
    }
    
    public boolean contains(Point p) {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac instanceof AccessibleComponent) {
            Rectangle r = ((AccessibleComponent)(AccessibleComponent)ac).getBounds();
            return r.contains(p);
        } else {
            Component c = getCurrentComponent();
            if (c != null) {
                Rectangle r = c.getBounds();
                return r.contains(p);
            } else {
                return getBounds().contains(p);
            }
        }
    }
    
    public Point getLocationOnScreen() {
        if (parent != null) {
            Point listLocation = parent.getLocationOnScreen();
            Point componentLocation = parent.indexToLocation(indexInParent);
            if (componentLocation != null) {
                componentLocation.translate(listLocation.x, listLocation.y);
                return componentLocation;
            } else {
                return null;
            }
        } else {
            return null;
        }
    }
    
    public Point getLocation() {
        if (parent != null) {
            return parent.indexToLocation(indexInParent);
        } else {
            return null;
        }
    }
    
    public void setLocation(Point p) {
        if ((parent != null) && (parent.contains(p))) {
            this$1.this$0.ensureIndexIsVisible(indexInParent);
        }
    }
    
    public Rectangle getBounds() {
        if (parent != null) {
            return parent.getCellBounds(indexInParent, indexInParent);
        } else {
            return null;
        }
    }
    
    public void setBounds(Rectangle r) {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac instanceof AccessibleComponent) {
            ((AccessibleComponent)(AccessibleComponent)ac).setBounds(r);
        }
    }
    
    public Dimension getSize() {
        Rectangle cellBounds = this.getBounds();
        if (cellBounds != null) {
            return cellBounds.getSize();
        } else {
            return null;
        }
    }
    
    public void setSize(Dimension d) {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac instanceof AccessibleComponent) {
            ((AccessibleComponent)(AccessibleComponent)ac).setSize(d);
        } else {
            Component c = getCurrentComponent();
            if (c != null) {
                c.setSize(d);
            }
        }
    }
    
    public Accessible getAccessibleAt(Point p) {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac instanceof AccessibleComponent) {
            return ((AccessibleComponent)(AccessibleComponent)ac).getAccessibleAt(p);
        } else {
            return null;
        }
    }
    
    public boolean isFocusTraversable() {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac instanceof AccessibleComponent) {
            return ((AccessibleComponent)(AccessibleComponent)ac).isFocusTraversable();
        } else {
            Component c = getCurrentComponent();
            if (c != null) {
                return c.isFocusTraversable();
            } else {
                return false;
            }
        }
    }
    
    public void requestFocus() {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac instanceof AccessibleComponent) {
            ((AccessibleComponent)(AccessibleComponent)ac).requestFocus();
        } else {
            Component c = getCurrentComponent();
            if (c != null) {
                c.requestFocus();
            }
        }
    }
    
    public void addFocusListener(FocusListener l) {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac instanceof AccessibleComponent) {
            ((AccessibleComponent)(AccessibleComponent)ac).addFocusListener(l);
        } else {
            Component c = getCurrentComponent();
            if (c != null) {
                c.addFocusListener(l);
            }
        }
    }
    
    public void removeFocusListener(FocusListener l) {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac instanceof AccessibleComponent) {
            ((AccessibleComponent)(AccessibleComponent)ac).removeFocusListener(l);
        } else {
            Component c = getCurrentComponent();
            if (c != null) {
                c.removeFocusListener(l);
            }
        }
    }
    
    public AccessibleIcon[] getAccessibleIcon() {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac != null) {
            return ac.getAccessibleIcon();
        } else {
            return null;
        }
    }
}
