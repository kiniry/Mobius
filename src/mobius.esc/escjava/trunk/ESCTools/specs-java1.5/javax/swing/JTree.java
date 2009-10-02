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

public class JTree extends JComponent implements Scrollable, Accessible {
    
    /*synthetic*/ static Hashtable access$000(JTree x0) {
        return x0.expandedState;
    }
    private static final String uiClassID = "TreeUI";
    protected transient TreeModel treeModel;
    protected transient TreeSelectionModel selectionModel;
    protected boolean rootVisible;
    protected transient TreeCellRenderer cellRenderer;
    protected int rowHeight;
    private boolean rowHeightSet = false;
    private transient Hashtable expandedState;
    protected boolean showsRootHandles;
    private boolean showsRootHandlesSet = false;
    protected transient JTree$TreeSelectionRedirector selectionRedirector;
    protected transient TreeCellEditor cellEditor;
    protected boolean editable;
    protected boolean largeModel;
    protected int visibleRowCount;
    protected boolean invokesStopCellEditing;
    protected boolean scrollsOnExpand;
    private boolean scrollsOnExpandSet = false;
    protected int toggleClickCount;
    protected transient TreeModelListener treeModelListener;
    private transient Stack expandedStack;
    private TreePath leadPath;
    private TreePath anchorPath;
    private boolean expandsSelectedPaths;
    private boolean settingUI;
    private boolean dragEnabled;
    private transient TreeExpansionListener uiTreeExpansionListener;
    private static int TEMP_STACK_SIZE = 11;
    public static final String CELL_RENDERER_PROPERTY = "cellRenderer";
    public static final String TREE_MODEL_PROPERTY = "model";
    public static final String ROOT_VISIBLE_PROPERTY = "rootVisible";
    public static final String SHOWS_ROOT_HANDLES_PROPERTY = "showsRootHandles";
    public static final String ROW_HEIGHT_PROPERTY = "rowHeight";
    public static final String CELL_EDITOR_PROPERTY = "cellEditor";
    public static final String EDITABLE_PROPERTY = "editable";
    public static final String LARGE_MODEL_PROPERTY = "largeModel";
    public static final String SELECTION_MODEL_PROPERTY = "selectionModel";
    public static final String VISIBLE_ROW_COUNT_PROPERTY = "visibleRowCount";
    public static final String INVOKES_STOP_CELL_EDITING_PROPERTY = "invokesStopCellEditing";
    public static final String SCROLLS_ON_EXPAND_PROPERTY = "scrollsOnExpand";
    public static final String TOGGLE_CLICK_COUNT_PROPERTY = "toggleClickCount";
    public static final String LEAD_SELECTION_PATH_PROPERTY = "leadSelectionPath";
    public static final String ANCHOR_SELECTION_PATH_PROPERTY = "anchorSelectionPath";
    public static final String EXPANDS_SELECTED_PATHS_PROPERTY = "expandsSelectedPaths";
    
    protected static TreeModel getDefaultTreeModel() {
        DefaultMutableTreeNode root = new DefaultMutableTreeNode("JTree");
        DefaultMutableTreeNode parent;
        parent = new DefaultMutableTreeNode("colors");
        root.add(parent);
        parent.add(new DefaultMutableTreeNode("blue"));
        parent.add(new DefaultMutableTreeNode("violet"));
        parent.add(new DefaultMutableTreeNode("red"));
        parent.add(new DefaultMutableTreeNode("yellow"));
        parent = new DefaultMutableTreeNode("sports");
        root.add(parent);
        parent.add(new DefaultMutableTreeNode("basketball"));
        parent.add(new DefaultMutableTreeNode("soccer"));
        parent.add(new DefaultMutableTreeNode("football"));
        parent.add(new DefaultMutableTreeNode("hockey"));
        parent = new DefaultMutableTreeNode("food");
        root.add(parent);
        parent.add(new DefaultMutableTreeNode("hot dogs"));
        parent.add(new DefaultMutableTreeNode("pizza"));
        parent.add(new DefaultMutableTreeNode("ravioli"));
        parent.add(new DefaultMutableTreeNode("bananas"));
        return new DefaultTreeModel(root);
    }
    
    protected static TreeModel createTreeModel(Object value) {
        DefaultMutableTreeNode root;
        if ((value instanceof Object[]) || (value instanceof Hashtable) || (value instanceof Vector)) {
            root = new DefaultMutableTreeNode("root");
            JTree$DynamicUtilTreeNode.createChildren(root, value);
        } else {
            root = new JTree$DynamicUtilTreeNode("root", value);
        }
        return new DefaultTreeModel(root, false);
    }
    
    public JTree() {
        this(getDefaultTreeModel());
    }
    
    public JTree(Object[] value) {
        this(createTreeModel(value));
        this.setRootVisible(false);
        this.setShowsRootHandles(true);
        expandRoot();
    }
    
    public JTree(Vector value) {
        this(createTreeModel(value));
        this.setRootVisible(false);
        this.setShowsRootHandles(true);
        expandRoot();
    }
    
    public JTree(Hashtable value) {
        this(createTreeModel(value));
        this.setRootVisible(false);
        this.setShowsRootHandles(true);
        expandRoot();
    }
    
    public JTree(TreeNode root) {
        this(root, false);
    }
    
    public JTree(TreeNode root, boolean asksAllowsChildren) {
        this(new DefaultTreeModel(root, asksAllowsChildren));
    }
    
    public JTree(TreeModel newModel) {
        
        expandedStack = new Stack();
        toggleClickCount = 2;
        expandedState = new Hashtable();
        setLayout(null);
        rowHeight = 16;
        visibleRowCount = 20;
        rootVisible = true;
        selectionModel = new DefaultTreeSelectionModel();
        cellRenderer = null;
        scrollsOnExpand = true;
        setOpaque(true);
        expandsSelectedPaths = true;
        updateUI();
        setModel(newModel);
    }
    
    public TreeUI getUI() {
        return (TreeUI)(TreeUI)ui;
    }
    
    public void setUI(TreeUI ui) {
        if ((TreeUI)(TreeUI)this.ui != ui) {
            settingUI = true;
            uiTreeExpansionListener = null;
            try {
                super.setUI(ui);
            } finally {
                settingUI = false;
            }
        }
    }
    
    public void updateUI() {
        setUI((TreeUI)(TreeUI)UIManager.getUI(this));
        invalidate();
    }
    
    public String getUIClassID() {
        return uiClassID;
    }
    
    public TreeCellRenderer getCellRenderer() {
        return cellRenderer;
    }
    
    public void setCellRenderer(TreeCellRenderer x) {
        TreeCellRenderer oldValue = cellRenderer;
        cellRenderer = x;
        firePropertyChange(CELL_RENDERER_PROPERTY, oldValue, cellRenderer);
        invalidate();
    }
    
    public void setEditable(boolean flag) {
        boolean oldValue = this.editable;
        this.editable = flag;
        firePropertyChange(EDITABLE_PROPERTY, oldValue, flag);
        if (accessibleContext != null) {
            accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, (oldValue ? AccessibleState.EDITABLE : null), (flag ? AccessibleState.EDITABLE : null));
        }
    }
    
    public boolean isEditable() {
        return editable;
    }
    
    public void setCellEditor(TreeCellEditor cellEditor) {
        TreeCellEditor oldEditor = this.cellEditor;
        this.cellEditor = cellEditor;
        firePropertyChange(CELL_EDITOR_PROPERTY, oldEditor, cellEditor);
        invalidate();
    }
    
    public TreeCellEditor getCellEditor() {
        return cellEditor;
    }
    
    public TreeModel getModel() {
        return treeModel;
    }
    
    public void setModel(TreeModel newModel) {
        clearSelection();
        TreeModel oldModel = treeModel;
        if (treeModel != null && treeModelListener != null) treeModel.removeTreeModelListener(treeModelListener);
        if (accessibleContext != null) {
            if (treeModel != null) {
                treeModel.removeTreeModelListener((TreeModelListener)(TreeModelListener)accessibleContext);
            }
            if (newModel != null) {
                newModel.addTreeModelListener((TreeModelListener)(TreeModelListener)accessibleContext);
            }
        }
        treeModel = newModel;
        clearToggledPaths();
        if (treeModel != null) {
            if (treeModelListener == null) treeModelListener = createTreeModelListener();
            if (treeModelListener != null) treeModel.addTreeModelListener(treeModelListener);
            if (treeModel.getRoot() != null && !treeModel.isLeaf(treeModel.getRoot())) {
                expandedState.put(new TreePath(treeModel.getRoot()), Boolean.TRUE);
            }
        }
        firePropertyChange(TREE_MODEL_PROPERTY, oldModel, treeModel);
        invalidate();
    }
    
    public boolean isRootVisible() {
        return rootVisible;
    }
    
    public void setRootVisible(boolean rootVisible) {
        boolean oldValue = this.rootVisible;
        this.rootVisible = rootVisible;
        firePropertyChange(ROOT_VISIBLE_PROPERTY, oldValue, this.rootVisible);
        if (accessibleContext != null) {
            ((JTree$AccessibleJTree)(JTree$AccessibleJTree)accessibleContext).fireVisibleDataPropertyChange();
        }
    }
    
    public void setShowsRootHandles(boolean newValue) {
        boolean oldValue = showsRootHandles;
        TreeModel model = getModel();
        showsRootHandles = newValue;
        showsRootHandlesSet = true;
        firePropertyChange(SHOWS_ROOT_HANDLES_PROPERTY, oldValue, showsRootHandles);
        if (accessibleContext != null) {
            ((JTree$AccessibleJTree)(JTree$AccessibleJTree)accessibleContext).fireVisibleDataPropertyChange();
        }
        invalidate();
    }
    
    public boolean getShowsRootHandles() {
        return showsRootHandles;
    }
    
    public void setRowHeight(int rowHeight) {
        int oldValue = this.rowHeight;
        this.rowHeight = rowHeight;
        rowHeightSet = true;
        firePropertyChange(ROW_HEIGHT_PROPERTY, oldValue, this.rowHeight);
        invalidate();
    }
    
    public int getRowHeight() {
        return rowHeight;
    }
    
    public boolean isFixedRowHeight() {
        return (rowHeight > 0);
    }
    
    public void setLargeModel(boolean newValue) {
        boolean oldValue = largeModel;
        largeModel = newValue;
        firePropertyChange(LARGE_MODEL_PROPERTY, oldValue, newValue);
    }
    
    public boolean isLargeModel() {
        return largeModel;
    }
    
    public void setInvokesStopCellEditing(boolean newValue) {
        boolean oldValue = invokesStopCellEditing;
        invokesStopCellEditing = newValue;
        firePropertyChange(INVOKES_STOP_CELL_EDITING_PROPERTY, oldValue, newValue);
    }
    
    public boolean getInvokesStopCellEditing() {
        return invokesStopCellEditing;
    }
    
    public void setScrollsOnExpand(boolean newValue) {
        boolean oldValue = scrollsOnExpand;
        scrollsOnExpand = newValue;
        scrollsOnExpandSet = true;
        firePropertyChange(SCROLLS_ON_EXPAND_PROPERTY, oldValue, newValue);
    }
    
    public boolean getScrollsOnExpand() {
        return scrollsOnExpand;
    }
    
    public void setToggleClickCount(int clickCount) {
        int oldCount = toggleClickCount;
        toggleClickCount = clickCount;
        firePropertyChange(TOGGLE_CLICK_COUNT_PROPERTY, oldCount, clickCount);
    }
    
    public int getToggleClickCount() {
        return toggleClickCount;
    }
    
    public void setExpandsSelectedPaths(boolean newValue) {
        boolean oldValue = expandsSelectedPaths;
        expandsSelectedPaths = newValue;
        firePropertyChange(EXPANDS_SELECTED_PATHS_PROPERTY, oldValue, newValue);
    }
    
    public boolean getExpandsSelectedPaths() {
        return expandsSelectedPaths;
    }
    
    public void setDragEnabled(boolean b) {
        if (b && GraphicsEnvironment.isHeadless()) {
            throw new HeadlessException();
        }
        dragEnabled = b;
    }
    
    public boolean getDragEnabled() {
        return dragEnabled;
    }
    
    public boolean isPathEditable(TreePath path) {
        return isEditable();
    }
    
    public String getToolTipText(MouseEvent event) {
        if (event != null) {
            Point p = event.getPoint();
            int selRow = getRowForLocation(p.x, p.y);
            TreeCellRenderer r = getCellRenderer();
            if (selRow != -1 && r != null) {
                TreePath path = getPathForRow(selRow);
                Object lastPath = path.getLastPathComponent();
                Component rComponent = r.getTreeCellRendererComponent(this, lastPath, isRowSelected(selRow), isExpanded(selRow), getModel().isLeaf(lastPath), selRow, true);
                if (rComponent instanceof JComponent) {
                    MouseEvent newEvent;
                    Rectangle pathBounds = getPathBounds(path);
                    p.translate(-pathBounds.x, -pathBounds.y);
                    newEvent = new MouseEvent(rComponent, event.getID(), event.getWhen(), event.getModifiers(), p.x, p.y, event.getClickCount(), event.isPopupTrigger());
                    return ((JComponent)(JComponent)rComponent).getToolTipText(newEvent);
                }
            }
        }
        return null;
    }
    
    public String convertValueToText(Object value, boolean selected, boolean expanded, boolean leaf, int row, boolean hasFocus) {
        if (value != null) {
            String sValue = value.toString();
            if (sValue != null) {
                return sValue;
            }
        }
        return "";
    }
    
    public int getRowCount() {
        TreeUI tree = getUI();
        if (tree != null) return tree.getRowCount(this);
        return 0;
    }
    
    public void setSelectionPath(TreePath path) {
        getSelectionModel().setSelectionPath(path);
    }
    
    public void setSelectionPaths(TreePath[] paths) {
        getSelectionModel().setSelectionPaths(paths);
    }
    
    public void setLeadSelectionPath(TreePath newPath) {
        TreePath oldValue = leadPath;
        leadPath = newPath;
        firePropertyChange(LEAD_SELECTION_PATH_PROPERTY, oldValue, newPath);
    }
    
    public void setAnchorSelectionPath(TreePath newPath) {
        TreePath oldValue = anchorPath;
        anchorPath = newPath;
        firePropertyChange(ANCHOR_SELECTION_PATH_PROPERTY, oldValue, newPath);
    }
    
    public void setSelectionRow(int row) {
        int[] rows = {row};
        setSelectionRows(rows);
    }
    
    public void setSelectionRows(int[] rows) {
        TreeUI ui = getUI();
        if (ui != null && rows != null) {
            int numRows = rows.length;
            TreePath[] paths = new TreePath[numRows];
            for (int counter = 0; counter < numRows; counter++) {
                paths[counter] = ui.getPathForRow(this, rows[counter]);
            }
            setSelectionPaths(paths);
        }
    }
    
    public void addSelectionPath(TreePath path) {
        getSelectionModel().addSelectionPath(path);
    }
    
    public void addSelectionPaths(TreePath[] paths) {
        getSelectionModel().addSelectionPaths(paths);
    }
    
    public void addSelectionRow(int row) {
        int[] rows = {row};
        addSelectionRows(rows);
    }
    
    public void addSelectionRows(int[] rows) {
        TreeUI ui = getUI();
        if (ui != null && rows != null) {
            int numRows = rows.length;
            TreePath[] paths = new TreePath[numRows];
            for (int counter = 0; counter < numRows; counter++) paths[counter] = ui.getPathForRow(this, rows[counter]);
            addSelectionPaths(paths);
        }
    }
    
    public Object getLastSelectedPathComponent() {
        TreePath selPath = getSelectionModel().getSelectionPath();
        if (selPath != null) return selPath.getLastPathComponent();
        return null;
    }
    
    public TreePath getLeadSelectionPath() {
        return leadPath;
    }
    
    public TreePath getAnchorSelectionPath() {
        return anchorPath;
    }
    
    public TreePath getSelectionPath() {
        return getSelectionModel().getSelectionPath();
    }
    
    public TreePath[] getSelectionPaths() {
        return getSelectionModel().getSelectionPaths();
    }
    
    public int[] getSelectionRows() {
        return getSelectionModel().getSelectionRows();
    }
    
    public int getSelectionCount() {
        return selectionModel.getSelectionCount();
    }
    
    public int getMinSelectionRow() {
        return getSelectionModel().getMinSelectionRow();
    }
    
    public int getMaxSelectionRow() {
        return getSelectionModel().getMaxSelectionRow();
    }
    
    public int getLeadSelectionRow() {
        TreePath leadPath = getLeadSelectionPath();
        if (leadPath != null) {
            return getRowForPath(leadPath);
        }
        return -1;
    }
    
    public boolean isPathSelected(TreePath path) {
        return getSelectionModel().isPathSelected(path);
    }
    
    public boolean isRowSelected(int row) {
        return getSelectionModel().isRowSelected(row);
    }
    
    public Enumeration getExpandedDescendants(TreePath parent) {
        if (!isExpanded(parent)) return null;
        Enumeration toggledPaths = expandedState.keys();
        Vector elements = null;
        TreePath path;
        Object value;
        if (toggledPaths != null) {
            while (toggledPaths.hasMoreElements()) {
                path = (TreePath)(TreePath)toggledPaths.nextElement();
                value = expandedState.get(path);
                if (path != parent && value != null && ((Boolean)(Boolean)value).booleanValue() && parent.isDescendant(path) && isVisible(path)) {
                    if (elements == null) {
                        elements = new Vector();
                    }
                    elements.addElement(path);
                }
            }
        }
        if (elements == null) {
            Set empty = Collections.emptySet();
            return Collections.enumeration(empty);
        }
        return elements.elements();
    }
    
    public boolean hasBeenExpanded(TreePath path) {
        return (path != null && expandedState.get(path) != null);
    }
    
    public boolean isExpanded(TreePath path) {
        if (path == null) return false;
        Object value = expandedState.get(path);
        if (value == null || !((Boolean)(Boolean)value).booleanValue()) return false;
        TreePath parentPath = path.getParentPath();
        if (parentPath != null) return isExpanded(parentPath);
        return true;
    }
    
    public boolean isExpanded(int row) {
        TreeUI tree = getUI();
        if (tree != null) {
            TreePath path = tree.getPathForRow(this, row);
            if (path != null) {
                Boolean value = (Boolean)(Boolean)expandedState.get(path);
                return (value != null && value.booleanValue());
            }
        }
        return false;
    }
    
    public boolean isCollapsed(TreePath path) {
        return !isExpanded(path);
    }
    
    public boolean isCollapsed(int row) {
        return !isExpanded(row);
    }
    
    public void makeVisible(TreePath path) {
        if (path != null) {
            TreePath parentPath = path.getParentPath();
            if (parentPath != null) {
                expandPath(parentPath);
            }
        }
    }
    
    public boolean isVisible(TreePath path) {
        if (path != null) {
            TreePath parentPath = path.getParentPath();
            if (parentPath != null) return isExpanded(parentPath);
            return true;
        }
        return false;
    }
    
    public Rectangle getPathBounds(TreePath path) {
        TreeUI tree = getUI();
        if (tree != null) return tree.getPathBounds(this, path);
        return null;
    }
    
    public Rectangle getRowBounds(int row) {
        return getPathBounds(getPathForRow(row));
    }
    
    public void scrollPathToVisible(TreePath path) {
        if (path != null) {
            makeVisible(path);
            Rectangle bounds = getPathBounds(path);
            if (bounds != null) {
                scrollRectToVisible(bounds);
                if (accessibleContext != null) {
                    ((JTree$AccessibleJTree)(JTree$AccessibleJTree)accessibleContext).fireVisibleDataPropertyChange();
                }
            }
        }
    }
    
    public void scrollRowToVisible(int row) {
        scrollPathToVisible(getPathForRow(row));
    }
    
    public TreePath getPathForRow(int row) {
        TreeUI tree = getUI();
        if (tree != null) return tree.getPathForRow(this, row);
        return null;
    }
    
    public int getRowForPath(TreePath path) {
        TreeUI tree = getUI();
        if (tree != null) return tree.getRowForPath(this, path);
        return -1;
    }
    
    public void expandPath(TreePath path) {
        TreeModel model = getModel();
        if (path != null && model != null && !model.isLeaf(path.getLastPathComponent())) {
            setExpandedState(path, true);
        }
    }
    
    public void expandRow(int row) {
        expandPath(getPathForRow(row));
    }
    
    public void collapsePath(TreePath path) {
        setExpandedState(path, false);
    }
    
    public void collapseRow(int row) {
        collapsePath(getPathForRow(row));
    }
    
    public TreePath getPathForLocation(int x, int y) {
        TreePath closestPath = getClosestPathForLocation(x, y);
        if (closestPath != null) {
            Rectangle pathBounds = getPathBounds(closestPath);
            if (pathBounds != null && x >= pathBounds.x && x < (pathBounds.x + pathBounds.width) && y >= pathBounds.y && y < (pathBounds.y + pathBounds.height)) return closestPath;
        }
        return null;
    }
    
    public int getRowForLocation(int x, int y) {
        return getRowForPath(getPathForLocation(x, y));
    }
    
    public TreePath getClosestPathForLocation(int x, int y) {
        TreeUI tree = getUI();
        if (tree != null) return tree.getClosestPathForLocation(this, x, y);
        return null;
    }
    
    public int getClosestRowForLocation(int x, int y) {
        return getRowForPath(getClosestPathForLocation(x, y));
    }
    
    public boolean isEditing() {
        TreeUI tree = getUI();
        if (tree != null) return tree.isEditing(this);
        return false;
    }
    
    public boolean stopEditing() {
        TreeUI tree = getUI();
        if (tree != null) return tree.stopEditing(this);
        return false;
    }
    
    public void cancelEditing() {
        TreeUI tree = getUI();
        if (tree != null) tree.cancelEditing(this);
    }
    
    public void startEditingAtPath(TreePath path) {
        TreeUI tree = getUI();
        if (tree != null) tree.startEditingAtPath(this, path);
    }
    
    public TreePath getEditingPath() {
        TreeUI tree = getUI();
        if (tree != null) return tree.getEditingPath(this);
        return null;
    }
    
    public void setSelectionModel(TreeSelectionModel selectionModel) {
        if (selectionModel == null) selectionModel = JTree$EmptySelectionModel.sharedInstance();
        TreeSelectionModel oldValue = this.selectionModel;
        if (this.selectionModel != null && selectionRedirector != null) {
            this.selectionModel.removeTreeSelectionListener(selectionRedirector);
        }
        if (accessibleContext != null) {
            this.selectionModel.removeTreeSelectionListener((TreeSelectionListener)(TreeSelectionListener)accessibleContext);
            selectionModel.addTreeSelectionListener((TreeSelectionListener)(TreeSelectionListener)accessibleContext);
        }
        this.selectionModel = selectionModel;
        if (selectionRedirector != null) {
            this.selectionModel.addTreeSelectionListener(selectionRedirector);
        }
        firePropertyChange(SELECTION_MODEL_PROPERTY, oldValue, this.selectionModel);
        if (accessibleContext != null) {
            accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_SELECTION_PROPERTY, Boolean.valueOf(false), Boolean.valueOf(true));
        }
    }
    
    public TreeSelectionModel getSelectionModel() {
        return selectionModel;
    }
    
    protected TreePath[] getPathBetweenRows(int index0, int index1) {
        int newMinIndex;
        int newMaxIndex;
        TreeUI tree = getUI();
        newMinIndex = Math.min(index0, index1);
        newMaxIndex = Math.max(index0, index1);
        if (tree != null) {
            TreePath[] selection = new TreePath[newMaxIndex - newMinIndex + 1];
            for (int counter = newMinIndex; counter <= newMaxIndex; counter++) selection[counter - newMinIndex] = tree.getPathForRow(this, counter);
            return selection;
        }
        return null;
    }
    
    public void setSelectionInterval(int index0, int index1) {
        TreePath[] paths = getPathBetweenRows(index0, index1);
        this.getSelectionModel().setSelectionPaths(paths);
    }
    
    public void addSelectionInterval(int index0, int index1) {
        TreePath[] paths = getPathBetweenRows(index0, index1);
        this.getSelectionModel().addSelectionPaths(paths);
    }
    
    public void removeSelectionInterval(int index0, int index1) {
        TreePath[] paths = getPathBetweenRows(index0, index1);
        this.getSelectionModel().removeSelectionPaths(paths);
    }
    
    public void removeSelectionPath(TreePath path) {
        this.getSelectionModel().removeSelectionPath(path);
    }
    
    public void removeSelectionPaths(TreePath[] paths) {
        this.getSelectionModel().removeSelectionPaths(paths);
    }
    
    public void removeSelectionRow(int row) {
        int[] rows = {row};
        removeSelectionRows(rows);
    }
    
    public void removeSelectionRows(int[] rows) {
        TreeUI ui = getUI();
        if (ui != null && rows != null) {
            int numRows = rows.length;
            TreePath[] paths = new TreePath[numRows];
            for (int counter = 0; counter < numRows; counter++) paths[counter] = ui.getPathForRow(this, rows[counter]);
            removeSelectionPaths(paths);
        }
    }
    
    public void clearSelection() {
        getSelectionModel().clearSelection();
    }
    
    public boolean isSelectionEmpty() {
        return getSelectionModel().isSelectionEmpty();
    }
    
    public void addTreeExpansionListener(TreeExpansionListener tel) {
        if (settingUI) {
            uiTreeExpansionListener = tel;
        }
        listenerList.add(TreeExpansionListener.class, tel);
    }
    
    public void removeTreeExpansionListener(TreeExpansionListener tel) {
        listenerList.remove(TreeExpansionListener.class, tel);
        if (uiTreeExpansionListener == tel) {
            uiTreeExpansionListener = null;
        }
    }
    
    public TreeExpansionListener[] getTreeExpansionListeners() {
        return (TreeExpansionListener[])(TreeExpansionListener[])listenerList.getListeners(TreeExpansionListener.class);
    }
    
    public void addTreeWillExpandListener(TreeWillExpandListener tel) {
        listenerList.add(TreeWillExpandListener.class, tel);
    }
    
    public void removeTreeWillExpandListener(TreeWillExpandListener tel) {
        listenerList.remove(TreeWillExpandListener.class, tel);
    }
    
    public TreeWillExpandListener[] getTreeWillExpandListeners() {
        return (TreeWillExpandListener[])(TreeWillExpandListener[])listenerList.getListeners(TreeWillExpandListener.class);
    }
    
    public void fireTreeExpanded(TreePath path) {
        Object[] listeners = listenerList.getListenerList();
        TreeExpansionEvent e = null;
        if (uiTreeExpansionListener != null) {
            e = new TreeExpansionEvent(this, path);
            uiTreeExpansionListener.treeExpanded(e);
        }
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == TreeExpansionListener.class && listeners[i + 1] != uiTreeExpansionListener) {
                if (e == null) e = new TreeExpansionEvent(this, path);
                ((TreeExpansionListener)(TreeExpansionListener)listeners[i + 1]).treeExpanded(e);
            }
        }
    }
    
    public void fireTreeCollapsed(TreePath path) {
        Object[] listeners = listenerList.getListenerList();
        TreeExpansionEvent e = null;
        if (uiTreeExpansionListener != null) {
            e = new TreeExpansionEvent(this, path);
            uiTreeExpansionListener.treeCollapsed(e);
        }
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == TreeExpansionListener.class && listeners[i + 1] != uiTreeExpansionListener) {
                if (e == null) e = new TreeExpansionEvent(this, path);
                ((TreeExpansionListener)(TreeExpansionListener)listeners[i + 1]).treeCollapsed(e);
            }
        }
    }
    
    public void fireTreeWillExpand(TreePath path) throws ExpandVetoException {
        Object[] listeners = listenerList.getListenerList();
        TreeExpansionEvent e = null;
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == TreeWillExpandListener.class) {
                if (e == null) e = new TreeExpansionEvent(this, path);
                ((TreeWillExpandListener)(TreeWillExpandListener)listeners[i + 1]).treeWillExpand(e);
            }
        }
    }
    
    public void fireTreeWillCollapse(TreePath path) throws ExpandVetoException {
        Object[] listeners = listenerList.getListenerList();
        TreeExpansionEvent e = null;
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == TreeWillExpandListener.class) {
                if (e == null) e = new TreeExpansionEvent(this, path);
                ((TreeWillExpandListener)(TreeWillExpandListener)listeners[i + 1]).treeWillCollapse(e);
            }
        }
    }
    
    public void addTreeSelectionListener(TreeSelectionListener tsl) {
        listenerList.add(TreeSelectionListener.class, tsl);
        if (listenerList.getListenerCount(TreeSelectionListener.class) != 0 && selectionRedirector == null) {
            selectionRedirector = new JTree$TreeSelectionRedirector(this);
            selectionModel.addTreeSelectionListener(selectionRedirector);
        }
    }
    
    public void removeTreeSelectionListener(TreeSelectionListener tsl) {
        listenerList.remove(TreeSelectionListener.class, tsl);
        if (listenerList.getListenerCount(TreeSelectionListener.class) == 0 && selectionRedirector != null) {
            selectionModel.removeTreeSelectionListener(selectionRedirector);
            selectionRedirector = null;
        }
    }
    
    public TreeSelectionListener[] getTreeSelectionListeners() {
        return (TreeSelectionListener[])(TreeSelectionListener[])listenerList.getListeners(TreeSelectionListener.class);
    }
    
    protected void fireValueChanged(TreeSelectionEvent e) {
        Object[] listeners = listenerList.getListenerList();
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == TreeSelectionListener.class) {
                ((TreeSelectionListener)(TreeSelectionListener)listeners[i + 1]).valueChanged(e);
            }
        }
    }
    
    public void treeDidChange() {
        revalidate();
        repaint();
    }
    
    public void setVisibleRowCount(int newCount) {
        int oldCount = visibleRowCount;
        visibleRowCount = newCount;
        firePropertyChange(VISIBLE_ROW_COUNT_PROPERTY, oldCount, visibleRowCount);
        invalidate();
        if (accessibleContext != null) {
            ((JTree$AccessibleJTree)(JTree$AccessibleJTree)accessibleContext).fireVisibleDataPropertyChange();
        }
    }
    
    public int getVisibleRowCount() {
        return visibleRowCount;
    }
    
    private void expandRoot() {
        TreeModel model = getModel();
        if (model != null && model.getRoot() != null) {
            expandPath(new TreePath(model.getRoot()));
        }
    }
    
    public TreePath getNextMatch(String prefix, int startingRow, Position$Bias bias) {
        int max = getRowCount();
        if (prefix == null) {
            throw new IllegalArgumentException();
        }
        if (startingRow < 0 || startingRow >= max) {
            throw new IllegalArgumentException();
        }
        prefix = prefix.toUpperCase();
        int increment = (bias == Position$Bias.Forward) ? 1 : -1;
        int row = startingRow;
        do {
            TreePath path = getPathForRow(row);
            String text = convertValueToText(path.getLastPathComponent(), isRowSelected(row), isExpanded(row), true, row, false);
            if (text.toUpperCase().startsWith(prefix)) {
                return path;
            }
            row = (row + increment + max) % max;
        }         while (row != startingRow);
        return null;
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        Vector values = new Vector();
        s.defaultWriteObject();
        if (cellRenderer != null && cellRenderer instanceof Serializable) {
            values.addElement("cellRenderer");
            values.addElement(cellRenderer);
        }
        if (cellEditor != null && cellEditor instanceof Serializable) {
            values.addElement("cellEditor");
            values.addElement(cellEditor);
        }
        if (treeModel != null && treeModel instanceof Serializable) {
            values.addElement("treeModel");
            values.addElement(treeModel);
        }
        if (selectionModel != null && selectionModel instanceof Serializable) {
            values.addElement("selectionModel");
            values.addElement(selectionModel);
        }
        Object expandedData = getArchivableExpandedState();
        if (expandedData != null) {
            values.addElement("expandedState");
            values.addElement(expandedData);
        }
        s.writeObject(values);
        if (getUIClassID().equals(uiClassID)) {
            byte count = JComponent.getWriteObjCounter(this);
            JComponent.setWriteObjCounter(this, --count);
            if (count == 0 && ui != null) {
                ui.installUI(this);
            }
        }
    }
    
    private void readObject(ObjectInputStream s) throws IOException, ClassNotFoundException {
        s.defaultReadObject();
        expandedState = new Hashtable();
        expandedStack = new Stack();
        Vector values = (Vector)(Vector)s.readObject();
        int indexCounter = 0;
        int maxCounter = values.size();
        if (indexCounter < maxCounter && values.elementAt(indexCounter).equals("cellRenderer")) {
            cellRenderer = (TreeCellRenderer)(TreeCellRenderer)values.elementAt(++indexCounter);
            indexCounter++;
        }
        if (indexCounter < maxCounter && values.elementAt(indexCounter).equals("cellEditor")) {
            cellEditor = (TreeCellEditor)(TreeCellEditor)values.elementAt(++indexCounter);
            indexCounter++;
        }
        if (indexCounter < maxCounter && values.elementAt(indexCounter).equals("treeModel")) {
            treeModel = (TreeModel)(TreeModel)values.elementAt(++indexCounter);
            indexCounter++;
        }
        if (indexCounter < maxCounter && values.elementAt(indexCounter).equals("selectionModel")) {
            selectionModel = (TreeSelectionModel)(TreeSelectionModel)values.elementAt(++indexCounter);
            indexCounter++;
        }
        if (indexCounter < maxCounter && values.elementAt(indexCounter).equals("expandedState")) {
            unarchiveExpandedState(values.elementAt(++indexCounter));
            indexCounter++;
        }
        if (listenerList.getListenerCount(TreeSelectionListener.class) != 0) {
            selectionRedirector = new JTree$TreeSelectionRedirector(this);
            selectionModel.addTreeSelectionListener(selectionRedirector);
        }
        if (treeModel != null) {
            treeModelListener = createTreeModelListener();
            if (treeModelListener != null) treeModel.addTreeModelListener(treeModelListener);
        }
    }
    
    private Object getArchivableExpandedState() {
        TreeModel model = getModel();
        if (model != null) {
            Enumeration paths = expandedState.keys();
            if (paths != null) {
                Vector state = new Vector();
                while (paths.hasMoreElements()) {
                    TreePath path = (TreePath)(TreePath)paths.nextElement();
                    Object archivePath;
                    try {
                        archivePath = getModelIndexsForPath(path);
                    } catch (Error error) {
                        archivePath = null;
                    }
                    if (archivePath != null) {
                        state.addElement(archivePath);
                        state.addElement(expandedState.get(path));
                    }
                }
                return state;
            }
        }
        return null;
    }
    
    private void unarchiveExpandedState(Object state) {
        if (state instanceof Vector) {
            Vector paths = (Vector)(Vector)state;
            for (int counter = paths.size() - 1; counter >= 0; counter--) {
                Boolean eState = (Boolean)(Boolean)paths.elementAt(counter--);
                TreePath path;
                try {
                    path = getPathForIndexs((int[])(int[])paths.elementAt(counter));
                    if (path != null) expandedState.put(path, eState);
                } catch (Error error) {
                }
            }
        }
    }
    
    private int[] getModelIndexsForPath(TreePath path) {
        if (path != null) {
            TreeModel model = getModel();
            int count = path.getPathCount();
            int[] indexs = new int[count - 1];
            Object parent = model.getRoot();
            for (int counter = 1; counter < count; counter++) {
                indexs[counter - 1] = model.getIndexOfChild(parent, path.getPathComponent(counter));
                parent = path.getPathComponent(counter);
                if (indexs[counter - 1] < 0) return null;
            }
            return indexs;
        }
        return null;
    }
    
    private TreePath getPathForIndexs(int[] indexs) {
        if (indexs == null) return null;
        TreeModel model = getModel();
        if (model == null) return null;
        int count = indexs.length;
        Object parent = model.getRoot();
        TreePath parentPath = new TreePath(parent);
        for (int counter = 0; counter < count; counter++) {
            parent = model.getChild(parent, indexs[counter]);
            if (parent == null) return null;
            parentPath = parentPath.pathByAddingChild(parent);
        }
        return parentPath;
    }
    {
    }
    {
    }
    
    public Dimension getPreferredScrollableViewportSize() {
        int width = getPreferredSize().width;
        int visRows = getVisibleRowCount();
        int height = -1;
        if (isFixedRowHeight()) height = visRows * getRowHeight(); else {
            TreeUI ui = getUI();
            if (ui != null && visRows > 0) {
                int rc = ui.getRowCount(this);
                if (rc >= visRows) {
                    Rectangle bounds = getRowBounds(visRows - 1);
                    if (bounds != null) {
                        height = bounds.y + bounds.height;
                    }
                } else if (rc > 0) {
                    Rectangle bounds = getRowBounds(0);
                    if (bounds != null) {
                        height = bounds.height * visRows;
                    }
                }
            }
            if (height == -1) {
                height = 16 * visRows;
            }
        }
        return new Dimension(width, height);
    }
    
    public int getScrollableUnitIncrement(Rectangle visibleRect, int orientation, int direction) {
        if (orientation == SwingConstants.VERTICAL) {
            Rectangle rowBounds;
            int firstIndex = getClosestRowForLocation(0, visibleRect.y);
            if (firstIndex != -1) {
                rowBounds = getRowBounds(firstIndex);
                if (rowBounds.y != visibleRect.y) {
                    if (direction < 0) {
                        return Math.max(0, (visibleRect.y - rowBounds.y));
                    }
                    return (rowBounds.y + rowBounds.height - visibleRect.y);
                }
                if (direction < 0) {
                    if (firstIndex != 0) {
                        rowBounds = getRowBounds(firstIndex - 1);
                        return rowBounds.height;
                    }
                } else {
                    return rowBounds.height;
                }
            }
            return 0;
        }
        return 4;
    }
    
    public int getScrollableBlockIncrement(Rectangle visibleRect, int orientation, int direction) {
        return (orientation == SwingConstants.VERTICAL) ? visibleRect.height : visibleRect.width;
    }
    
    public boolean getScrollableTracksViewportWidth() {
        if (getParent() instanceof JViewport) {
            return (((JViewport)(JViewport)getParent()).getWidth() > getPreferredSize().width);
        }
        return false;
    }
    
    public boolean getScrollableTracksViewportHeight() {
        if (getParent() instanceof JViewport) {
            return (((JViewport)(JViewport)getParent()).getHeight() > getPreferredSize().height);
        }
        return false;
    }
    
    protected void setExpandedState(TreePath path, boolean state) {
        if (path != null) {
            Stack stack;
            TreePath parentPath = path.getParentPath();
            if (expandedStack.size() == 0) {
                stack = new Stack();
            } else {
                stack = (Stack)(Stack)expandedStack.pop();
            }
            try {
                while (parentPath != null) {
                    if (isExpanded(parentPath)) {
                        parentPath = null;
                    } else {
                        stack.push(parentPath);
                        parentPath = parentPath.getParentPath();
                    }
                }
                for (int counter = stack.size() - 1; counter >= 0; counter--) {
                    parentPath = (TreePath)(TreePath)stack.pop();
                    if (!isExpanded(parentPath)) {
                        try {
                            fireTreeWillExpand(parentPath);
                        } catch (ExpandVetoException eve) {
                            return;
                        }
                        expandedState.put(parentPath, Boolean.TRUE);
                        fireTreeExpanded(parentPath);
                        if (accessibleContext != null) {
                            ((JTree$AccessibleJTree)(JTree$AccessibleJTree)accessibleContext).fireVisibleDataPropertyChange();
                        }
                    }
                }
            } finally {
                if (expandedStack.size() < TEMP_STACK_SIZE) {
                    stack.removeAllElements();
                    expandedStack.push(stack);
                }
            }
            if (!state) {
                Object cValue = expandedState.get(path);
                if (cValue != null && ((Boolean)(Boolean)cValue).booleanValue()) {
                    try {
                        fireTreeWillCollapse(path);
                    } catch (ExpandVetoException eve) {
                        return;
                    }
                    expandedState.put(path, Boolean.FALSE);
                    fireTreeCollapsed(path);
                    if (removeDescendantSelectedPaths(path, false) && !isPathSelected(path)) {
                        addSelectionPath(path);
                    }
                    if (accessibleContext != null) {
                        ((JTree$AccessibleJTree)(JTree$AccessibleJTree)accessibleContext).fireVisibleDataPropertyChange();
                    }
                }
            } else {
                Object cValue = expandedState.get(path);
                if (cValue == null || !((Boolean)(Boolean)cValue).booleanValue()) {
                    try {
                        fireTreeWillExpand(path);
                    } catch (ExpandVetoException eve) {
                        return;
                    }
                    expandedState.put(path, Boolean.TRUE);
                    fireTreeExpanded(path);
                    if (accessibleContext != null) {
                        ((JTree$AccessibleJTree)(JTree$AccessibleJTree)accessibleContext).fireVisibleDataPropertyChange();
                    }
                }
            }
        }
    }
    
    protected Enumeration getDescendantToggledPaths(TreePath parent) {
        if (parent == null) return null;
        Vector descendants = new Vector();
        Enumeration nodes = expandedState.keys();
        TreePath path;
        while (nodes.hasMoreElements()) {
            path = (TreePath)(TreePath)nodes.nextElement();
            if (parent.isDescendant(path)) descendants.addElement(path);
        }
        return descendants.elements();
    }
    
    protected void removeDescendantToggledPaths(Enumeration toRemove) {
        if (toRemove != null) {
            while (toRemove.hasMoreElements()) {
                Enumeration descendants = getDescendantToggledPaths((TreePath)(TreePath)toRemove.nextElement());
                if (descendants != null) {
                    while (descendants.hasMoreElements()) {
                        expandedState.remove(descendants.nextElement());
                    }
                }
            }
        }
    }
    
    protected void clearToggledPaths() {
        expandedState.clear();
    }
    
    protected TreeModelListener createTreeModelListener() {
        return new JTree$TreeModelHandler(this);
    }
    
    protected boolean removeDescendantSelectedPaths(TreePath path, boolean includePath) {
        TreePath[] toRemove = getDescendantSelectedPaths(path, includePath);
        if (toRemove != null) {
            getSelectionModel().removeSelectionPaths(toRemove);
            return true;
        }
        return false;
    }
    
    private TreePath[] getDescendantSelectedPaths(TreePath path, boolean includePath) {
        TreeSelectionModel sm = getSelectionModel();
        TreePath[] selPaths = (sm != null) ? sm.getSelectionPaths() : null;
        if (selPaths != null) {
            boolean shouldRemove = false;
            for (int counter = selPaths.length - 1; counter >= 0; counter--) {
                if (selPaths[counter] != null && path.isDescendant(selPaths[counter]) && (!path.equals(selPaths[counter]) || includePath)) shouldRemove = true; else selPaths[counter] = null;
            }
            if (!shouldRemove) {
                selPaths = null;
            }
            return selPaths;
        }
        return null;
    }
    
    void removeDescendantSelectedPaths(TreeModelEvent e) {
        TreePath pPath = e.getTreePath();
        Object[] oldChildren = e.getChildren();
        TreeSelectionModel sm = getSelectionModel();
        if (sm != null && pPath != null && oldChildren != null && oldChildren.length > 0) {
            for (int counter = oldChildren.length - 1; counter >= 0; counter--) {
                removeDescendantSelectedPaths(pPath.pathByAddingChild(oldChildren[counter]), true);
            }
        }
    }
    {
    }
    {
    }
    
    void setUIProperty(String propertyName, Object value) {
        if (propertyName == "rowHeight") {
            if (!rowHeightSet) {
                setRowHeight(((Number)(Number)value).intValue());
                rowHeightSet = false;
            }
        } else if (propertyName == "scrollsOnExpand") {
            if (!scrollsOnExpandSet) {
                setScrollsOnExpand(((Boolean)(Boolean)value).booleanValue());
                scrollsOnExpandSet = false;
            }
        } else if (propertyName == "showsRootHandles") {
            if (!showsRootHandlesSet) {
                setShowsRootHandles(((Boolean)(Boolean)value).booleanValue());
                showsRootHandlesSet = false;
            }
        } else {
            super.setUIProperty(propertyName, value);
        }
    }
    
    protected String paramString() {
        String rootVisibleString = (rootVisible ? "true" : "false");
        String showsRootHandlesString = (showsRootHandles ? "true" : "false");
        String editableString = (editable ? "true" : "false");
        String largeModelString = (largeModel ? "true" : "false");
        String invokesStopCellEditingString = (invokesStopCellEditing ? "true" : "false");
        String scrollsOnExpandString = (scrollsOnExpand ? "true" : "false");
        return super.paramString() + ",editable=" + editableString + ",invokesStopCellEditing=" + invokesStopCellEditingString + ",largeModel=" + largeModelString + ",rootVisible=" + rootVisibleString + ",rowHeight=" + rowHeight + ",scrollsOnExpand=" + scrollsOnExpandString + ",showsRootHandles=" + showsRootHandlesString + ",toggleClickCount=" + toggleClickCount + ",visibleRowCount=" + visibleRowCount;
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new JTree$AccessibleJTree(this);
        }
        return accessibleContext;
    }
    {
    }
}
