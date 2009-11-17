package javax.swing.table;

import java.util.*;
import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;
import java.beans.PropertyChangeListener;

public class JTableHeader$AccessibleJTableHeader$AccessibleJTableHeaderEntry extends AccessibleContext implements Accessible, AccessibleComponent {
    /*synthetic*/ final JTableHeader$AccessibleJTableHeader this$1;
    private JTableHeader parent;
    private int column;
    private JTable table;
    
    public JTableHeader$AccessibleJTableHeader$AccessibleJTableHeaderEntry(/*synthetic*/ final JTableHeader$AccessibleJTableHeader this$1, int c, JTableHeader p, JTable t) {
        this.this$1 = this$1;
        
        parent = p;
        column = c;
        table = t;
        this.setAccessibleParent(parent);
    }
    
    public AccessibleContext getAccessibleContext() {
        return this;
    }
    
    private AccessibleContext getCurrentAccessibleContext() {
        TableColumnModel tcm = table.getColumnModel();
        if (tcm != null) {
            if (column < 0 || column >= tcm.getColumnCount()) {
                return null;
            }
            TableColumn aColumn = tcm.getColumn(column);
            TableCellRenderer renderer = aColumn.getHeaderRenderer();
            if (renderer == null) {
                if (JTableHeader.access$100(this$1.this$0) != null) {
                    renderer = JTableHeader.access$100(this$1.this$0);
                } else {
                    return null;
                }
            }
            Component c = renderer.getTableCellRendererComponent(this$1.this$0.getTable(), aColumn.getHeaderValue(), false, false, -1, column);
            if (c instanceof Accessible) {
                return ((Accessible)(Accessible)c).getAccessibleContext();
            }
        }
        return null;
    }
    
    private Component getCurrentComponent() {
        TableColumnModel tcm = table.getColumnModel();
        if (tcm != null) {
            if (column < 0 || column >= tcm.getColumnCount()) {
                return null;
            }
            TableColumn aColumn = tcm.getColumn(column);
            TableCellRenderer renderer = aColumn.getHeaderRenderer();
            if (renderer == null) {
                if (JTableHeader.access$100(this$1.this$0) != null) {
                    renderer = JTableHeader.access$100(this$1.this$0);
                } else {
                    return null;
                }
            }
            return renderer.getTableCellRendererComponent(this$1.this$0.getTable(), aColumn.getHeaderValue(), false, false, -1, column);
        } else {
            return null;
        }
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
            return table.getColumnName(column);
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
            return AccessibleRole.COLUMN_HEADER;
        }
    }
    
    public AccessibleStateSet getAccessibleStateSet() {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac != null) {
            AccessibleStateSet states = ac.getAccessibleStateSet();
            if (isShowing()) {
                states.add(AccessibleState.SHOWING);
            }
            return states;
        } else {
            return new AccessibleStateSet();
        }
    }
    
    public int getAccessibleIndexInParent() {
        return column;
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
        if (isVisible() && this$1.this$0.isShowing()) {
            return true;
        } else {
            return false;
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
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac instanceof AccessibleComponent) {
            Rectangle r = ((AccessibleComponent)(AccessibleComponent)ac).getBounds();
            return r.getLocation();
        } else {
            Component c = getCurrentComponent();
            if (c != null) {
                Rectangle r = c.getBounds();
                return r.getLocation();
            } else {
                return getBounds().getLocation();
            }
        }
    }
    
    public void setLocation(Point p) {
    }
    
    public Rectangle getBounds() {
        Rectangle r = table.getCellRect(-1, column, false);
        r.y = 0;
        return r;
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
        return getBounds().getSize();
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
