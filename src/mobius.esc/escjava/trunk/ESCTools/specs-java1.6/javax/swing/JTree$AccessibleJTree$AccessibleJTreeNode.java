package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.io.*;
import java.util.*;
import javax.swing.event.*;
import javax.swing.plaf.TreeUI;
import javax.swing.tree.*;
import javax.accessibility.*;

public class JTree$AccessibleJTree$AccessibleJTreeNode extends AccessibleContext implements Accessible, AccessibleComponent, AccessibleSelection, AccessibleAction {
    /*synthetic*/ final JTree$AccessibleJTree this$1;
    private JTree tree = null;
    private TreeModel treeModel = null;
    private Object obj = null;
    private TreePath path = null;
    private Accessible accessibleParent = null;
    private int index = 0;
    private boolean isLeaf = false;
    
    public JTree$AccessibleJTree$AccessibleJTreeNode(/*synthetic*/ final JTree$AccessibleJTree this$1, JTree t, TreePath p, Accessible ap) {
        this.this$1 = this$1;
        
        tree = t;
        path = p;
        accessibleParent = ap;
        treeModel = t.getModel();
        obj = p.getLastPathComponent();
        if (treeModel != null) {
            isLeaf = treeModel.isLeaf(obj);
        }
    }
    
    private TreePath getChildTreePath(int i) {
        if (i < 0 || i >= getAccessibleChildrenCount()) {
            return null;
        } else {
            Object childObj = treeModel.getChild(obj, i);
            Object[] objPath = path.getPath();
            Object[] objChildPath = new Object[objPath.length + 1];
            java.lang.System.arraycopy(objPath, 0, objChildPath, 0, objPath.length);
            objChildPath[objChildPath.length - 1] = childObj;
            return new TreePath(objChildPath);
        }
    }
    
    public AccessibleContext getAccessibleContext() {
        return this;
    }
    
    private AccessibleContext getCurrentAccessibleContext() {
        Component c = getCurrentComponent();
        if (c instanceof Accessible) {
            return (((Accessible)(Accessible)c).getAccessibleContext());
        } else {
            return null;
        }
    }
    
    private Component getCurrentComponent() {
        if (tree.isVisible(path)) {
            TreeCellRenderer r = tree.getCellRenderer();
            if (r == null) {
                return null;
            }
            TreeUI ui = tree.getUI();
            if (ui != null) {
                int row = ui.getRowForPath(this$1.this$0, path);
                boolean selected = tree.isPathSelected(path);
                boolean expanded = tree.isExpanded(path);
                boolean hasFocus = false;
                return r.getTreeCellRendererComponent(tree, obj, selected, expanded, isLeaf, row, hasFocus);
            }
        }
        return null;
    }
    
    public String getAccessibleName() {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac != null) {
            String name = ac.getAccessibleName();
            if ((name != null) && (name != "")) {
                return ac.getAccessibleName();
            } else {
                return null;
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
        AccessibleStateSet states;
        int row = tree.getUI().getRowForPath(tree, path);
        int lsr = tree.getLeadSelectionRow();
        if (ac != null) {
            states = ac.getAccessibleStateSet();
        } else {
            states = new AccessibleStateSet();
        }
        if (isShowing()) {
            states.add(AccessibleState.SHOWING);
        } else if (states.contains(AccessibleState.SHOWING)) {
            states.remove(AccessibleState.SHOWING);
        }
        if (isVisible()) {
            states.add(AccessibleState.VISIBLE);
        } else if (states.contains(AccessibleState.VISIBLE)) {
            states.remove(AccessibleState.VISIBLE);
        }
        if (tree.isPathSelected(path)) {
            states.add(AccessibleState.SELECTED);
        }
        if (lsr == row) {
            states.add(AccessibleState.ACTIVE);
        }
        if (!isLeaf) {
            states.add(AccessibleState.EXPANDABLE);
        }
        if (tree.isExpanded(path)) {
            states.add(AccessibleState.EXPANDED);
        } else {
            states.add(AccessibleState.COLLAPSED);
        }
        if (tree.isEditable()) {
            states.add(AccessibleState.EDITABLE);
        }
        return states;
    }
    
    public Accessible getAccessibleParent() {
        if (accessibleParent == null) {
            Object[] objPath = path.getPath();
            if (objPath.length > 1) {
                Object objParent = objPath[objPath.length - 2];
                if (treeModel != null) {
                    index = treeModel.getIndexOfChild(objParent, obj);
                }
                Object[] objParentPath = new Object[objPath.length - 1];
                java.lang.System.arraycopy(objPath, 0, objParentPath, 0, objPath.length - 1);
                TreePath parentPath = new TreePath(objParentPath);
                accessibleParent = new JTree$AccessibleJTree$AccessibleJTreeNode(this$1, tree, parentPath, null);
                this.setAccessibleParent(accessibleParent);
            } else if (treeModel != null) {
                accessibleParent = tree;
                index = 0;
                this.setAccessibleParent(accessibleParent);
            }
        }
        return accessibleParent;
    }
    
    public int getAccessibleIndexInParent() {
        if (accessibleParent == null) {
            getAccessibleParent();
        }
        Object[] objPath = path.getPath();
        if (objPath.length > 1) {
            Object objParent = objPath[objPath.length - 2];
            if (treeModel != null) {
                index = treeModel.getIndexOfChild(objParent, obj);
            }
        }
        return index;
    }
    
    public int getAccessibleChildrenCount() {
        return treeModel.getChildCount(obj);
    }
    
    public Accessible getAccessibleChild(int i) {
        if (i < 0 || i >= getAccessibleChildrenCount()) {
            return null;
        } else {
            Object childObj = treeModel.getChild(obj, i);
            Object[] objPath = path.getPath();
            Object[] objChildPath = new Object[objPath.length + 1];
            java.lang.System.arraycopy(objPath, 0, objChildPath, 0, objPath.length);
            objChildPath[objChildPath.length - 1] = childObj;
            TreePath childPath = new TreePath(objChildPath);
            return new JTree$AccessibleJTree$AccessibleJTreeNode(this$1, this$1.this$0, childPath, this);
        }
    }
    
    public Locale getLocale() {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac != null) {
            return ac.getLocale();
        } else {
            return tree.getLocale();
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
        return this;
    }
    
    public AccessibleComponent getAccessibleComponent() {
        return this;
    }
    
    public AccessibleSelection getAccessibleSelection() {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac != null && isLeaf) {
            return getCurrentAccessibleContext().getAccessibleSelection();
        } else {
            return this;
        }
    }
    
    public AccessibleText getAccessibleText() {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac != null) {
            return getCurrentAccessibleContext().getAccessibleText();
        } else {
            return null;
        }
    }
    
    public AccessibleValue getAccessibleValue() {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac != null) {
            return getCurrentAccessibleContext().getAccessibleValue();
        } else {
            return null;
        }
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
        Rectangle pathBounds = tree.getPathBounds(path);
        Rectangle parentBounds = tree.getVisibleRect();
        if (pathBounds != null && parentBounds != null && parentBounds.intersects(pathBounds)) {
            return true;
        } else {
            return false;
        }
    }
    
    public void setVisible(boolean b) {
    }
    
    public boolean isShowing() {
        return (tree.isShowing() && isVisible());
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
        if (tree != null) {
            Point treeLocation = tree.getLocationOnScreen();
            Rectangle pathBounds = tree.getPathBounds(path);
            if (treeLocation != null && pathBounds != null) {
                Point nodeLocation = new Point(pathBounds.x, pathBounds.y);
                nodeLocation.translate(treeLocation.x, treeLocation.y);
                return nodeLocation;
            } else {
                return null;
            }
        } else {
            return null;
        }
    }
    
    protected Point getLocationInJTree() {
        Rectangle r = tree.getPathBounds(path);
        if (r != null) {
            return r.getLocation();
        } else {
            return null;
        }
    }
    
    public Point getLocation() {
        Rectangle r = getBounds();
        if (r != null) {
            return r.getLocation();
        } else {
            return null;
        }
    }
    
    public void setLocation(Point p) {
    }
    
    public Rectangle getBounds() {
        Rectangle r = tree.getPathBounds(path);
        Accessible parent = getAccessibleParent();
        if (parent != null) {
            if (parent instanceof JTree$AccessibleJTree$AccessibleJTreeNode) {
                Point parentLoc = ((JTree$AccessibleJTree$AccessibleJTreeNode)(JTree$AccessibleJTree$AccessibleJTreeNode)parent).getLocationInJTree();
                if (parentLoc != null && r != null) {
                    r.translate(-parentLoc.x, -parentLoc.y);
                } else {
                    return null;
                }
            }
        }
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
    
    public int getAccessibleSelectionCount() {
        int count = 0;
        int childCount = getAccessibleChildrenCount();
        for (int i = 0; i < childCount; i++) {
            TreePath childPath = getChildTreePath(i);
            if (tree.isPathSelected(childPath)) {
                count++;
            }
        }
        return count;
    }
    
    public Accessible getAccessibleSelection(int i) {
        int childCount = getAccessibleChildrenCount();
        if (i < 0 || i >= childCount) {
            return null;
        }
        int count = 0;
        for (int j = 0; j < childCount && i >= count; j++) {
            TreePath childPath = getChildTreePath(j);
            if (tree.isPathSelected(childPath)) {
                if (count == i) {
                    return new JTree$AccessibleJTree$AccessibleJTreeNode(this$1, tree, childPath, this);
                } else {
                    count++;
                }
            }
        }
        return null;
    }
    
    public boolean isAccessibleChildSelected(int i) {
        int childCount = getAccessibleChildrenCount();
        if (i < 0 || i >= childCount) {
            return false;
        } else {
            TreePath childPath = getChildTreePath(i);
            return tree.isPathSelected(childPath);
        }
    }
    
    public void addAccessibleSelection(int i) {
        TreeModel model = this$1.this$0.getModel();
        if (model != null) {
            if (i >= 0 && i < getAccessibleChildrenCount()) {
                TreePath path = getChildTreePath(i);
                this$1.this$0.addSelectionPath(path);
            }
        }
    }
    
    public void removeAccessibleSelection(int i) {
        TreeModel model = this$1.this$0.getModel();
        if (model != null) {
            if (i >= 0 && i < getAccessibleChildrenCount()) {
                TreePath path = getChildTreePath(i);
                this$1.this$0.removeSelectionPath(path);
            }
        }
    }
    
    public void clearAccessibleSelection() {
        int childCount = getAccessibleChildrenCount();
        for (int i = 0; i < childCount; i++) {
            removeAccessibleSelection(i);
        }
    }
    
    public void selectAllAccessibleSelection() {
        TreeModel model = this$1.this$0.getModel();
        if (model != null) {
            int childCount = getAccessibleChildrenCount();
            TreePath path;
            for (int i = 0; i < childCount; i++) {
                path = getChildTreePath(i);
                this$1.this$0.addSelectionPath(path);
            }
        }
    }
    
    public int getAccessibleActionCount() {
        AccessibleContext ac = getCurrentAccessibleContext();
        if (ac != null) {
            AccessibleAction aa = ac.getAccessibleAction();
            if (aa != null) {
                return (aa.getAccessibleActionCount() + (isLeaf ? 0 : 1));
            }
        }
        return isLeaf ? 0 : 1;
    }
    
    public String getAccessibleActionDescription(int i) {
        if (i < 0 || i >= getAccessibleActionCount()) {
            return null;
        }
        AccessibleContext ac = getCurrentAccessibleContext();
        if (i == 0) {
            return AccessibleAction.TOGGLE_EXPAND;
        } else if (ac != null) {
            AccessibleAction aa = ac.getAccessibleAction();
            if (aa != null) {
                return aa.getAccessibleActionDescription(i - 1);
            }
        }
        return null;
    }
    
    public boolean doAccessibleAction(int i) {
        if (i < 0 || i >= getAccessibleActionCount()) {
            return false;
        }
        AccessibleContext ac = getCurrentAccessibleContext();
        if (i == 0) {
            if (this$1.this$0.isExpanded(path)) {
                this$1.this$0.collapsePath(path);
            } else {
                this$1.this$0.expandPath(path);
            }
            return true;
        } else if (ac != null) {
            AccessibleAction aa = ac.getAccessibleAction();
            if (aa != null) {
                return aa.doAccessibleAction(i - 1);
            }
        }
        return false;
    }
}
