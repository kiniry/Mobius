package javax.swing;

import java.util.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.print.*;
import java.beans.*;
import javax.accessibility.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.table.*;
import javax.swing.border.*;
import javax.print.attribute.*;

public class JTable$AccessibleJTable$AccessibleJTableCell extends AccessibleContext implements Accessible, AccessibleComponent {
    /*synthetic*/ final JTable$AccessibleJTable this$1;
    private JTable parent;
    private int row;
    private int column;
    private int index;
    
    public JTable$AccessibleJTable$AccessibleJTableCell(/*synthetic*/ final JTable$AccessibleJTable this$1, JTable t, int r, int c, int i) {
        this.this$1 = this$1;
        
        parent = t;
        row = r;
        column = c;
        index = i;
        this.setAccessibleParent(parent);
    }
    
    public AccessibleContext getAccessibleContext() {
        return this;
    }
    
    private AccessibleContext getCurrentAccessibleContext() {
        TableColumn aColumn = this$1.this$0.getColumnModel().getColumn(column);
        TableCellRenderer renderer = aColumn.getCellRenderer();
        if (renderer == null) {
            Class columnClass = this$1.this$0.getColumnClass(column);
            renderer = this$1.this$0.getDefaultRenderer(columnClass);
        }
        Component component = renderer.getTableCellRendererComponent(this$1.this$0, this$1.this$0.getValueAt(row, column), false, false, row, column);
        if (component instanceof Accessible) {
            return ((Accessible)(Accessible)component).getAccessibleContext();
        } else {
            return null;
        }
    }
    
    private Component getCurrentComponent() {
        TableColumn aColumn = this$1.this$0.getColumnModel().getColumn(column);
        TableCellRenderer renderer = aColumn.getCellRenderer();
        if (renderer == null) {
            Class columnClass = this$1.this$0.getColumnClass(column);
            renderer = this$1.this$0.getDefaultRenderer(columnClass);
        }
        return renderer.getTableCellRendererComponent(this$1.this$0, null, false, false, row, column);
    }
    
    public String getAccessibleName() {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac != null) {
            String name = ac.getAccessibleName();
            if ((name != null) && (name != "")) {
                return ac.getAccessibleName();
            }
        }
        if ((accessibleName != null) && (accessibleName != "")) {
            return accessibleName;
        } else {
            return null;
        }
    }
    
    public void setAccessibleName(String s) {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac != null) {
            ac.setAccessibleName(s);
        } else {
            super.setAccessibleName(s);
        }
    }
    
    public String getAccessibleDescription() {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac != null) {
            return ac.getAccessibleDescription();
        } else {
            return super.getAccessibleDescription();
        }
    }
    
    public void setAccessibleDescription(String s) {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac != null) {
            ac.setAccessibleDescription(s);
        } else {
            super.setAccessibleDescription(s);
        }
    }
    
    public AccessibleRole getAccessibleRole() {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac != null) {
            return ac.getAccessibleRole();
        } else {
            return AccessibleRole.UNKNOWN;
        }
    }
    
    public AccessibleStateSet getAccessibleStateSet() {
        AccessibleContext ac = getCurrentAccessibleContext();
        AccessibleStateSet as = null;
        if (ac != null) {
            as = ac.getAccessibleStateSet();
        }
        if (as == null) {
            as = new AccessibleStateSet();
        }
        Rectangle rjt = this$1.this$0.getVisibleRect();
        Rectangle rcell = this$1.this$0.getCellRect(row, column, false);
        if (rjt.intersects(rcell)) {
            as.add(AccessibleState.SHOWING);
        } else {
            if (as.contains(AccessibleState.SHOWING)) {
                as.remove(AccessibleState.SHOWING);
            }
        }
        if (parent.isCellSelected(row, column)) {
            as.add(AccessibleState.SELECTED);
        } else if (as.contains(AccessibleState.SELECTED)) {
            as.remove(AccessibleState.SELECTED);
        }
        if ((row == this$1.this$0.getSelectedRow()) && (column == this$1.this$0.getSelectedColumn())) {
            as.add(AccessibleState.ACTIVE);
        }
        as.add(AccessibleState.TRANSIENT);
        return as;
    }
    
    public Accessible getAccessibleParent() {
        return parent;
    }
    
    public int getAccessibleIndexInParent() {
        return index;
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
        } else {
            super.addPropertyChangeListener(l);
        }
    }
    
    public void removePropertyChangeListener(PropertyChangeListener l) {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac != null) {
            ac.removePropertyChangeListener(l);
        } else {
            super.removePropertyChangeListener(l);
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
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac instanceof AccessibleComponent) {
            return ((AccessibleComponent)(AccessibleComponent)ac).isVisible();
        } else {
            Component c = getCurrentComponent();
            if (c != null) {
                return c.isVisible();
            } else {
                return false;
            }
        }
    }
    
    public void setVisible(boolean b) {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac instanceof AccessibleComponent) {
            ((AccessibleComponent)(AccessibleComponent)ac).setVisible(b);
        } else {
            Component c = getCurrentComponent();
            if (c != null) {
                c.setVisible(b);
            }
        }
    }
    
    public boolean isShowing() {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac instanceof AccessibleComponent) {
            if (ac.getAccessibleParent() != null) {
                return ((AccessibleComponent)(AccessibleComponent)ac).isShowing();
            } else {
                return isVisible();
            }
        } else {
            Component c = getCurrentComponent();
            if (c != null) {
                return c.isShowing();
            } else {
                return false;
            }
        }
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
            Point parentLocation = parent.getLocationOnScreen();
            Point componentLocation = getLocation();
            componentLocation.translate(parentLocation.x, parentLocation.y);
            return componentLocation;
        } else {
            return null;
        }
    }
    
    public Point getLocation() {
        if (parent != null) {
            Rectangle r = parent.getCellRect(row, column, false);
            if (r != null) {
                return r.getLocation();
            }
        }
        return null;
    }
    
    public void setLocation(Point p) {
    }
    
    public Rectangle getBounds() {
        if (parent != null) {
            return parent.getCellRect(row, column, false);
        } else {
            return null;
        }
    }
    
    public void setBounds(Rectangle r) {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac instanceof AccessibleComponent) {
            ((AccessibleComponent)(AccessibleComponent)ac).setBounds(r);
        } else {
            Component c = getCurrentComponent();
            if (c != null) {
                c.setBounds(r);
            }
        }
    }
    
    public Dimension getSize() {
        if (parent != null) {
            Rectangle r = parent.getCellRect(row, column, false);
            if (r != null) {
                return r.getSize();
            }
        }
        return null;
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
}
