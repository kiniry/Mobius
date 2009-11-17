package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.datatransfer.*;
import java.awt.dnd.*;
import java.beans.*;
import java.io.*;
import java.util.Enumeration;
import java.util.Hashtable;
import java.util.TooManyListenersException;
import javax.swing.plaf.ComponentUI;
import javax.swing.plaf.UIResource;
import javax.swing.plaf.TreeUI;
import javax.swing.tree.*;
import com.sun.java.swing.SwingUtilities2;
import sun.swing.DefaultLookup;

public class BasicTreeUI extends TreeUI {
    
    /*synthetic*/ static void access$2500(BasicTreeUI x0, TreePath x1) {
        x0.extendSelection(x1);
    }
    
    /*synthetic*/ static TreePath access$2400(BasicTreeUI x0) {
        return x0.getAnchorSelectionPath();
    }
    
    /*synthetic*/ static int access$2300(BasicTreeUI x0) {
        return x0.getLeadSelectionRow();
    }
    
    /*synthetic*/ static boolean access$2200(BasicTreeUI x0, TreePath x1, MouseEvent x2, MouseEvent x3) {
        return x0.startEditingOnRelease(x1, x2, x3);
    }
    
    /*synthetic*/ static void access$2100(BasicTreeUI x0, TreePath x1, boolean x2) {
        x0.setLeadSelectionPath(x1, x2);
    }
    
    /*synthetic*/ static void access$2000(BasicTreeUI x0, TreePath x1) {
        x0.setLeadSelectionPath(x1);
    }
    
    /*synthetic*/ static void access$1900(BasicTreeUI x0, TreePath x1) {
        x0.setAnchorSelectionPath(x1);
    }
    
    /*synthetic*/ static TreePath access$1800(BasicTreeUI x0) {
        return x0.getLeadSelectionPath();
    }
    
    /*synthetic*/ static DropTargetListener access$1702(DropTargetListener x0) {
        return defaultDropTargetListener = x0;
    }
    
    /*synthetic*/ static DropTargetListener access$1700() {
        return defaultDropTargetListener;
    }
    
    /*synthetic*/ static void access$1600(BasicTreeUI x0) {
        x0.redoTheLayout();
    }
    
    /*synthetic*/ static void access$1500(BasicTreeUI x0, TreePath x1) {
        x0.repaintPath(x1);
    }
    
    /*synthetic*/ static void access$1400(BasicTreeUI x0) {
        x0.updateLeadRow();
    }
    
    /*synthetic*/ static boolean access$1300(BasicTreeUI x0) {
        return x0.ignoreLAChange;
    }
    
    /*synthetic*/ static long access$1200(BasicTreeUI x0) {
        return x0.timeFactor;
    }
    
    /*synthetic*/ static BasicTreeUI$Actions access$500() {
        return SHARED_ACTION;
    }
    
    /*synthetic*/ static int access$400(BasicTreeUI x0) {
        return x0.lastWidth;
    }
    
    /*synthetic*/ static boolean access$302(BasicTreeUI x0, boolean x1) {
        return x0.leftToRight = x1;
    }
    
    /*synthetic*/ static boolean access$300(BasicTreeUI x0) {
        return x0.leftToRight;
    }
    
    /*synthetic*/ static BasicTreeUI$Handler access$200(BasicTreeUI x0) {
        return x0.getHandler();
    }
    {
    }
    private static final BasicTreeUI$Actions SHARED_ACTION = new BasicTreeUI$Actions();
    private static final Insets EMPTY_INSETS = new Insets(0, 0, 0, 0);
    protected transient Icon collapsedIcon;
    protected transient Icon expandedIcon;
    private Color hashColor;
    protected int leftChildIndent;
    protected int rightChildIndent;
    protected int totalChildIndent;
    protected Dimension preferredMinSize;
    protected int lastSelectedRow;
    protected JTree tree;
    protected transient TreeCellRenderer currentCellRenderer;
    protected boolean createdRenderer;
    protected transient TreeCellEditor cellEditor;
    protected boolean createdCellEditor;
    protected boolean stopEditingInCompleteEditing;
    protected CellRendererPane rendererPane;
    protected Dimension preferredSize;
    protected boolean validCachedPreferredSize;
    protected AbstractLayoutCache treeState;
    protected Hashtable drawingCache;
    protected boolean largeModel;
    protected AbstractLayoutCache$NodeDimensions nodeDimensions;
    protected TreeModel treeModel;
    protected TreeSelectionModel treeSelectionModel;
    protected int depthOffset;
    private int lastWidth;
    protected Component editingComponent;
    protected TreePath editingPath;
    protected int editingRow;
    protected boolean editorHasDifferentSize;
    private int leadRow;
    private boolean ignoreLAChange;
    private boolean leftToRight;
    private PropertyChangeListener propertyChangeListener;
    private PropertyChangeListener selectionModelPropertyChangeListener;
    private MouseListener mouseListener;
    private FocusListener focusListener;
    private KeyListener keyListener;
    private ComponentListener componentListener;
    private CellEditorListener cellEditorListener;
    private TreeSelectionListener treeSelectionListener;
    private TreeModelListener treeModelListener;
    private TreeExpansionListener treeExpansionListener;
    private boolean paintLines = true;
    private boolean lineTypeDashed;
    private long timeFactor = 1000L;
    private BasicTreeUI$Handler handler;
    private MouseEvent releaseEvent;
    
    public static ComponentUI createUI(JComponent x) {
        return new BasicTreeUI();
    }
    
    static void loadActionMap(LazyActionMap map) {
        map.put(new BasicTreeUI$Actions("selectPrevious"));
        map.put(new BasicTreeUI$Actions("selectPreviousChangeLead"));
        map.put(new BasicTreeUI$Actions("selectPreviousExtendSelection"));
        map.put(new BasicTreeUI$Actions("selectNext"));
        map.put(new BasicTreeUI$Actions("selectNextChangeLead"));
        map.put(new BasicTreeUI$Actions("selectNextExtendSelection"));
        map.put(new BasicTreeUI$Actions("selectChild"));
        map.put(new BasicTreeUI$Actions("selectChildChangeLead"));
        map.put(new BasicTreeUI$Actions("selectParent"));
        map.put(new BasicTreeUI$Actions("selectParentChangeLead"));
        map.put(new BasicTreeUI$Actions("scrollUpChangeSelection"));
        map.put(new BasicTreeUI$Actions("scrollUpChangeLead"));
        map.put(new BasicTreeUI$Actions("scrollUpExtendSelection"));
        map.put(new BasicTreeUI$Actions("scrollDownChangeSelection"));
        map.put(new BasicTreeUI$Actions("scrollDownExtendSelection"));
        map.put(new BasicTreeUI$Actions("scrollDownChangeLead"));
        map.put(new BasicTreeUI$Actions("selectFirst"));
        map.put(new BasicTreeUI$Actions("selectFirstChangeLead"));
        map.put(new BasicTreeUI$Actions("selectFirstExtendSelection"));
        map.put(new BasicTreeUI$Actions("selectLast"));
        map.put(new BasicTreeUI$Actions("selectLastChangeLead"));
        map.put(new BasicTreeUI$Actions("selectLastExtendSelection"));
        map.put(new BasicTreeUI$Actions("toggle"));
        map.put(new BasicTreeUI$Actions("cancel"));
        map.put(new BasicTreeUI$Actions("startEditing"));
        map.put(new BasicTreeUI$Actions("selectAll"));
        map.put(new BasicTreeUI$Actions("clearSelection"));
        map.put(new BasicTreeUI$Actions("scrollLeft"));
        map.put(new BasicTreeUI$Actions("scrollRight"));
        map.put(new BasicTreeUI$Actions("scrollLeftExtendSelection"));
        map.put(new BasicTreeUI$Actions("scrollRightExtendSelection"));
        map.put(new BasicTreeUI$Actions("scrollRightChangeLead"));
        map.put(new BasicTreeUI$Actions("scrollLeftChangeLead"));
        map.put(new BasicTreeUI$Actions("expand"));
        map.put(new BasicTreeUI$Actions("collapse"));
        map.put(new BasicTreeUI$Actions("moveSelectionToParent"));
        map.put(new BasicTreeUI$Actions("addToSelection"));
        map.put(new BasicTreeUI$Actions("toggleAndAnchor"));
        map.put(new BasicTreeUI$Actions("extendTo"));
        map.put(new BasicTreeUI$Actions("moveSelectionTo"));
        map.put(TransferHandler.getCutAction());
        map.put(TransferHandler.getCopyAction());
        map.put(TransferHandler.getPasteAction());
    }
    
    public BasicTreeUI() {
        
    }
    
    protected Color getHashColor() {
        return hashColor;
    }
    
    protected void setHashColor(Color color) {
        hashColor = color;
    }
    
    public void setLeftChildIndent(int newAmount) {
        leftChildIndent = newAmount;
        totalChildIndent = leftChildIndent + rightChildIndent;
        if (treeState != null) treeState.invalidateSizes();
        updateSize();
    }
    
    public int getLeftChildIndent() {
        return leftChildIndent;
    }
    
    public void setRightChildIndent(int newAmount) {
        rightChildIndent = newAmount;
        totalChildIndent = leftChildIndent + rightChildIndent;
        if (treeState != null) treeState.invalidateSizes();
        updateSize();
    }
    
    public int getRightChildIndent() {
        return rightChildIndent;
    }
    
    public void setExpandedIcon(Icon newG) {
        expandedIcon = newG;
    }
    
    public Icon getExpandedIcon() {
        return expandedIcon;
    }
    
    public void setCollapsedIcon(Icon newG) {
        collapsedIcon = newG;
    }
    
    public Icon getCollapsedIcon() {
        return collapsedIcon;
    }
    
    protected void setLargeModel(boolean largeModel) {
        if (getRowHeight() < 1) largeModel = false;
        if (this.largeModel != largeModel) {
            completeEditing();
            this.largeModel = largeModel;
            treeState = createLayoutCache();
            configureLayoutCache();
            updateLayoutCacheExpandedNodes();
            updateSize();
        }
    }
    
    protected boolean isLargeModel() {
        return largeModel;
    }
    
    protected void setRowHeight(int rowHeight) {
        completeEditing();
        if (treeState != null) {
            setLargeModel(tree.isLargeModel());
            treeState.setRowHeight(rowHeight);
            updateSize();
        }
    }
    
    protected int getRowHeight() {
        return (tree == null) ? -1 : tree.getRowHeight();
    }
    
    protected void setCellRenderer(TreeCellRenderer tcr) {
        completeEditing();
        updateRenderer();
        if (treeState != null) {
            treeState.invalidateSizes();
            updateSize();
        }
    }
    
    protected TreeCellRenderer getCellRenderer() {
        return currentCellRenderer;
    }
    
    protected void setModel(TreeModel model) {
        completeEditing();
        if (treeModel != null && treeModelListener != null) treeModel.removeTreeModelListener(treeModelListener);
        treeModel = model;
        if (treeModel != null) {
            if (treeModelListener != null) treeModel.addTreeModelListener(treeModelListener);
        }
        if (treeState != null) {
            treeState.setModel(model);
            updateLayoutCacheExpandedNodes();
            updateSize();
        }
    }
    
    protected TreeModel getModel() {
        return treeModel;
    }
    
    protected void setRootVisible(boolean newValue) {
        completeEditing();
        updateDepthOffset();
        if (treeState != null) {
            treeState.setRootVisible(newValue);
            treeState.invalidateSizes();
            updateSize();
        }
    }
    
    protected boolean isRootVisible() {
        return (tree != null) ? tree.isRootVisible() : false;
    }
    
    protected void setShowsRootHandles(boolean newValue) {
        completeEditing();
        updateDepthOffset();
        if (treeState != null) {
            treeState.invalidateSizes();
            updateSize();
        }
    }
    
    protected boolean getShowsRootHandles() {
        return (tree != null) ? tree.getShowsRootHandles() : false;
    }
    
    protected void setCellEditor(TreeCellEditor editor) {
        updateCellEditor();
    }
    
    protected TreeCellEditor getCellEditor() {
        return (tree != null) ? tree.getCellEditor() : null;
    }
    
    protected void setEditable(boolean newValue) {
        updateCellEditor();
    }
    
    protected boolean isEditable() {
        return (tree != null) ? tree.isEditable() : false;
    }
    
    protected void setSelectionModel(TreeSelectionModel newLSM) {
        completeEditing();
        if (selectionModelPropertyChangeListener != null && treeSelectionModel != null) treeSelectionModel.removePropertyChangeListener(selectionModelPropertyChangeListener);
        if (treeSelectionListener != null && treeSelectionModel != null) treeSelectionModel.removeTreeSelectionListener(treeSelectionListener);
        treeSelectionModel = newLSM;
        if (treeSelectionModel != null) {
            if (selectionModelPropertyChangeListener != null) treeSelectionModel.addPropertyChangeListener(selectionModelPropertyChangeListener);
            if (treeSelectionListener != null) treeSelectionModel.addTreeSelectionListener(treeSelectionListener);
            if (treeState != null) treeState.setSelectionModel(treeSelectionModel);
        } else if (treeState != null) treeState.setSelectionModel(null);
        if (tree != null) tree.repaint();
    }
    
    protected TreeSelectionModel getSelectionModel() {
        return treeSelectionModel;
    }
    
    public Rectangle getPathBounds(JTree tree, TreePath path) {
        if (tree != null && treeState != null) {
            Insets i = tree.getInsets();
            Rectangle bounds = treeState.getBounds(path, null);
            if (bounds != null && i != null) {
                bounds.x += i.left;
                bounds.y += i.top;
            }
            return bounds;
        }
        return null;
    }
    
    public TreePath getPathForRow(JTree tree, int row) {
        return (treeState != null) ? treeState.getPathForRow(row) : null;
    }
    
    public int getRowForPath(JTree tree, TreePath path) {
        return (treeState != null) ? treeState.getRowForPath(path) : -1;
    }
    
    public int getRowCount(JTree tree) {
        return (treeState != null) ? treeState.getRowCount() : 0;
    }
    
    public TreePath getClosestPathForLocation(JTree tree, int x, int y) {
        if (tree != null && treeState != null) {
            Insets i = tree.getInsets();
            if (i == null) i = EMPTY_INSETS;
            return treeState.getPathClosestTo(x - i.left, y - i.top);
        }
        return null;
    }
    
    public boolean isEditing(JTree tree) {
        return (editingComponent != null);
    }
    
    public boolean stopEditing(JTree tree) {
        if (editingComponent != null && cellEditor.stopCellEditing()) {
            completeEditing(false, false, true);
            return true;
        }
        return false;
    }
    
    public void cancelEditing(JTree tree) {
        if (editingComponent != null) {
            completeEditing(false, true, false);
        }
    }
    
    public void startEditingAtPath(JTree tree, TreePath path) {
        tree.scrollPathToVisible(path);
        if (path != null && tree.isVisible(path)) startEditing(path, null);
    }
    
    public TreePath getEditingPath(JTree tree) {
        return editingPath;
    }
    
    public void installUI(JComponent c) {
        if (c == null) {
            throw new NullPointerException("null component passed to BasicTreeUI.installUI()");
        }
        tree = (JTree)(JTree)c;
        prepareForUIInstall();
        installDefaults();
        installKeyboardActions();
        installComponents();
        installListeners();
        completeUIInstall();
    }
    
    protected void prepareForUIInstall() {
        drawingCache = new Hashtable(7);
        leftToRight = BasicGraphicsUtils.isLeftToRight(tree);
        lastWidth = tree.getWidth();
        stopEditingInCompleteEditing = true;
        lastSelectedRow = -1;
        leadRow = -1;
        preferredSize = new Dimension();
        largeModel = tree.isLargeModel();
        if (getRowHeight() <= 0) largeModel = false;
        setModel(tree.getModel());
    }
    
    protected void completeUIInstall() {
        this.setShowsRootHandles(tree.getShowsRootHandles());
        updateRenderer();
        updateDepthOffset();
        setSelectionModel(tree.getSelectionModel());
        treeState = createLayoutCache();
        configureLayoutCache();
        updateSize();
    }
    
    protected void installDefaults() {
        if (tree.getBackground() == null || tree.getBackground() instanceof UIResource) {
            tree.setBackground(UIManager.getColor("Tree.background"));
        }
        if (getHashColor() == null || getHashColor() instanceof UIResource) {
            setHashColor(UIManager.getColor("Tree.hash"));
        }
        if (tree.getFont() == null || tree.getFont() instanceof UIResource) tree.setFont(UIManager.getFont("Tree.font"));
        setExpandedIcon((Icon)(Icon)UIManager.get("Tree.expandedIcon"));
        setCollapsedIcon((Icon)(Icon)UIManager.get("Tree.collapsedIcon"));
        setLeftChildIndent(((Integer)(Integer)UIManager.get("Tree.leftChildIndent")).intValue());
        setRightChildIndent(((Integer)(Integer)UIManager.get("Tree.rightChildIndent")).intValue());
        LookAndFeel.installProperty(tree, "rowHeight", UIManager.get("Tree.rowHeight"));
        largeModel = (tree.isLargeModel() && tree.getRowHeight() > 0);
        Object scrollsOnExpand = UIManager.get("Tree.scrollsOnExpand");
        if (scrollsOnExpand != null) {
            LookAndFeel.installProperty(tree, "scrollsOnExpand", scrollsOnExpand);
        }
        paintLines = UIManager.getBoolean("Tree.paintLines");
        lineTypeDashed = UIManager.getBoolean("Tree.lineTypeDashed");
        Long l = (Long)(Long)UIManager.get("Tree.timeFactor");
        timeFactor = (l != null) ? l.longValue() : 1000L;
        Object showsRootHandles = UIManager.get("Tree.showsRootHandles");
        if (showsRootHandles != null) {
            LookAndFeel.installProperty(tree, JTree.SHOWS_ROOT_HANDLES_PROPERTY, showsRootHandles);
        }
    }
    
    protected void installListeners() {
        if ((propertyChangeListener = createPropertyChangeListener()) != null) {
            tree.addPropertyChangeListener(propertyChangeListener);
        }
        if (!SwingUtilities2.DRAG_FIX) {
            tree.addMouseListener(defaultDragRecognizer);
            tree.addMouseMotionListener(defaultDragRecognizer);
        }
        if ((mouseListener = createMouseListener()) != null) {
            tree.addMouseListener(mouseListener);
            if (mouseListener instanceof MouseMotionListener) {
                tree.addMouseMotionListener((MouseMotionListener)(MouseMotionListener)mouseListener);
            }
        }
        if ((focusListener = createFocusListener()) != null) {
            tree.addFocusListener(focusListener);
        }
        if ((keyListener = createKeyListener()) != null) {
            tree.addKeyListener(keyListener);
        }
        if ((treeExpansionListener = createTreeExpansionListener()) != null) {
            tree.addTreeExpansionListener(treeExpansionListener);
        }
        if ((treeModelListener = createTreeModelListener()) != null && treeModel != null) {
            treeModel.addTreeModelListener(treeModelListener);
        }
        if ((selectionModelPropertyChangeListener = createSelectionModelPropertyChangeListener()) != null && treeSelectionModel != null) {
            treeSelectionModel.addPropertyChangeListener(selectionModelPropertyChangeListener);
        }
        if ((treeSelectionListener = createTreeSelectionListener()) != null && treeSelectionModel != null) {
            treeSelectionModel.addTreeSelectionListener(treeSelectionListener);
        }
        TransferHandler th = tree.getTransferHandler();
        if (th == null || th instanceof UIResource) {
            tree.setTransferHandler(defaultTransferHandler);
        }
        DropTarget dropTarget = tree.getDropTarget();
        if (dropTarget instanceof UIResource) {
            if (defaultDropTargetListener == null) {
                defaultDropTargetListener = new BasicTreeUI$TreeDropTargetListener();
            }
            try {
                dropTarget.addDropTargetListener(defaultDropTargetListener);
            } catch (TooManyListenersException tmle) {
            }
        }
        LookAndFeel.installProperty(tree, "opaque", Boolean.TRUE);
    }
    
    protected void installKeyboardActions() {
        InputMap km = getInputMap(JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);
        SwingUtilities.replaceUIInputMap(tree, JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT, km);
        km = getInputMap(JComponent.WHEN_FOCUSED);
        SwingUtilities.replaceUIInputMap(tree, JComponent.WHEN_FOCUSED, km);
        LazyActionMap.installLazyActionMap(tree, BasicTreeUI.class, "Tree.actionMap");
    }
    
    InputMap getInputMap(int condition) {
        if (condition == JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT) {
            return (InputMap)(InputMap)DefaultLookup.get(tree, this, "Tree.ancestorInputMap");
        } else if (condition == JComponent.WHEN_FOCUSED) {
            InputMap keyMap = (InputMap)(InputMap)DefaultLookup.get(tree, this, "Tree.focusInputMap");
            InputMap rtlKeyMap;
            if (tree.getComponentOrientation().isLeftToRight() || ((rtlKeyMap = (InputMap)(InputMap)DefaultLookup.get(tree, this, "Tree.focusInputMap.RightToLeft")) == null)) {
                return keyMap;
            } else {
                rtlKeyMap.setParent(keyMap);
                return rtlKeyMap;
            }
        }
        return null;
    }
    
    protected void installComponents() {
        if ((rendererPane = createCellRendererPane()) != null) {
            tree.add(rendererPane);
        }
    }
    
    protected AbstractLayoutCache$NodeDimensions createNodeDimensions() {
        return new BasicTreeUI$NodeDimensionsHandler(this);
    }
    
    protected PropertyChangeListener createPropertyChangeListener() {
        return getHandler();
    }
    
    private BasicTreeUI$Handler getHandler() {
        if (handler == null) {
            handler = SwingUtilities2.DRAG_FIX ? new BasicTreeUI$DragFixHandler(this, null) : new BasicTreeUI$Handler(this, null);
        }
        return handler;
    }
    
    protected MouseListener createMouseListener() {
        return getHandler();
    }
    
    protected FocusListener createFocusListener() {
        return getHandler();
    }
    
    protected KeyListener createKeyListener() {
        return getHandler();
    }
    
    protected PropertyChangeListener createSelectionModelPropertyChangeListener() {
        return getHandler();
    }
    
    protected TreeSelectionListener createTreeSelectionListener() {
        return getHandler();
    }
    
    protected CellEditorListener createCellEditorListener() {
        return getHandler();
    }
    
    protected ComponentListener createComponentListener() {
        return new BasicTreeUI$ComponentHandler(this);
    }
    
    protected TreeExpansionListener createTreeExpansionListener() {
        return getHandler();
    }
    
    protected AbstractLayoutCache createLayoutCache() {
        if (isLargeModel() && getRowHeight() > 0) {
            return new FixedHeightLayoutCache();
        }
        return new VariableHeightLayoutCache();
    }
    
    protected CellRendererPane createCellRendererPane() {
        return new CellRendererPane();
    }
    
    protected TreeCellEditor createDefaultCellEditor() {
        if (currentCellRenderer != null && (currentCellRenderer instanceof DefaultTreeCellRenderer)) {
            DefaultTreeCellEditor editor = new DefaultTreeCellEditor(tree, (DefaultTreeCellRenderer)(DefaultTreeCellRenderer)currentCellRenderer);
            return editor;
        }
        return new DefaultTreeCellEditor(tree, null);
    }
    
    protected TreeCellRenderer createDefaultCellRenderer() {
        return new DefaultTreeCellRenderer();
    }
    
    protected TreeModelListener createTreeModelListener() {
        return getHandler();
    }
    
    public void uninstallUI(JComponent c) {
        completeEditing();
        prepareForUIUninstall();
        uninstallDefaults();
        uninstallListeners();
        uninstallKeyboardActions();
        uninstallComponents();
        completeUIUninstall();
    }
    
    protected void prepareForUIUninstall() {
    }
    
    protected void completeUIUninstall() {
        if (createdRenderer) {
            tree.setCellRenderer(null);
        }
        if (createdCellEditor) {
            tree.setCellEditor(null);
        }
        cellEditor = null;
        currentCellRenderer = null;
        rendererPane = null;
        componentListener = null;
        propertyChangeListener = null;
        mouseListener = null;
        focusListener = null;
        keyListener = null;
        setSelectionModel(null);
        treeState = null;
        drawingCache = null;
        selectionModelPropertyChangeListener = null;
        tree = null;
        treeModel = null;
        treeSelectionModel = null;
        treeSelectionListener = null;
        treeExpansionListener = null;
    }
    
    protected void uninstallDefaults() {
        if (tree.getTransferHandler() instanceof UIResource) {
            tree.setTransferHandler(null);
        }
    }
    
    protected void uninstallListeners() {
        if (componentListener != null) {
            tree.removeComponentListener(componentListener);
        }
        if (propertyChangeListener != null) {
            tree.removePropertyChangeListener(propertyChangeListener);
        }
        if (!SwingUtilities2.DRAG_FIX) {
            tree.removeMouseListener(defaultDragRecognizer);
            tree.removeMouseMotionListener(defaultDragRecognizer);
        }
        if (mouseListener != null) {
            tree.removeMouseListener(mouseListener);
            if (mouseListener instanceof MouseMotionListener) {
                tree.removeMouseMotionListener((MouseMotionListener)(MouseMotionListener)mouseListener);
            }
        }
        if (focusListener != null) {
            tree.removeFocusListener(focusListener);
        }
        if (keyListener != null) {
            tree.removeKeyListener(keyListener);
        }
        if (treeExpansionListener != null) {
            tree.removeTreeExpansionListener(treeExpansionListener);
        }
        if (treeModel != null && treeModelListener != null) {
            treeModel.removeTreeModelListener(treeModelListener);
        }
        if (selectionModelPropertyChangeListener != null && treeSelectionModel != null) {
            treeSelectionModel.removePropertyChangeListener(selectionModelPropertyChangeListener);
        }
        if (treeSelectionListener != null && treeSelectionModel != null) {
            treeSelectionModel.removeTreeSelectionListener(treeSelectionListener);
        }
        handler = null;
    }
    
    protected void uninstallKeyboardActions() {
        SwingUtilities.replaceUIActionMap(tree, null);
        SwingUtilities.replaceUIInputMap(tree, JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT, null);
        SwingUtilities.replaceUIInputMap(tree, JComponent.WHEN_FOCUSED, null);
    }
    
    protected void uninstallComponents() {
        if (rendererPane != null) {
            tree.remove(rendererPane);
        }
    }
    
    private void redoTheLayout() {
        if (treeState != null) {
            treeState.invalidateSizes();
        }
    }
    
    public void paint(Graphics g, JComponent c) {
        if (tree != c) {
            throw new InternalError("incorrect component");
        }
        if (treeState == null) {
            return;
        }
        int width = tree.getWidth();
        if (width != lastWidth) {
            lastWidth = width;
            if (!leftToRight) {
                redoTheLayout();
                updateSize();
            }
        }
        Rectangle paintBounds = g.getClipBounds();
        Insets insets = tree.getInsets();
        if (insets == null) insets = EMPTY_INSETS;
        TreePath initialPath = getClosestPathForLocation(tree, 0, paintBounds.y);
        Enumeration paintingEnumerator = treeState.getVisiblePathsFrom(initialPath);
        int row = treeState.getRowForPath(initialPath);
        int endY = paintBounds.y + paintBounds.height;
        drawingCache.clear();
        if (initialPath != null && paintingEnumerator != null) {
            TreePath parentPath = initialPath;
            parentPath = parentPath.getParentPath();
            while (parentPath != null) {
                paintVerticalPartOfLeg(g, paintBounds, insets, parentPath);
                drawingCache.put(parentPath, Boolean.TRUE);
                parentPath = parentPath.getParentPath();
            }
            boolean done = false;
            boolean isExpanded;
            boolean hasBeenExpanded;
            boolean isLeaf;
            Rectangle boundsBuffer = new Rectangle();
            Rectangle bounds;
            TreePath path;
            boolean rootVisible = isRootVisible();
            while (!done && paintingEnumerator.hasMoreElements()) {
                path = (TreePath)(TreePath)paintingEnumerator.nextElement();
                if (path != null) {
                    isLeaf = treeModel.isLeaf(path.getLastPathComponent());
                    if (isLeaf) isExpanded = hasBeenExpanded = false; else {
                        isExpanded = treeState.getExpandedState(path);
                        hasBeenExpanded = tree.hasBeenExpanded(path);
                    }
                    bounds = treeState.getBounds(path, boundsBuffer);
                    if (bounds == null) return;
                    bounds.x += insets.left;
                    bounds.y += insets.top;
                    parentPath = path.getParentPath();
                    if (parentPath != null) {
                        if (drawingCache.get(parentPath) == null) {
                            paintVerticalPartOfLeg(g, paintBounds, insets, parentPath);
                            drawingCache.put(parentPath, Boolean.TRUE);
                        }
                        paintHorizontalPartOfLeg(g, paintBounds, insets, bounds, path, row, isExpanded, hasBeenExpanded, isLeaf);
                    } else if (rootVisible && row == 0) {
                        paintHorizontalPartOfLeg(g, paintBounds, insets, bounds, path, row, isExpanded, hasBeenExpanded, isLeaf);
                    }
                    if (shouldPaintExpandControl(path, row, isExpanded, hasBeenExpanded, isLeaf)) {
                        paintExpandControl(g, paintBounds, insets, bounds, path, row, isExpanded, hasBeenExpanded, isLeaf);
                    }
                    if (!leftToRight) {
                        bounds.x += 4;
                    }
                    paintRow(g, paintBounds, insets, bounds, path, row, isExpanded, hasBeenExpanded, isLeaf);
                    if ((bounds.y + bounds.height) >= endY) done = true;
                } else {
                    done = true;
                }
                row++;
            }
        }
        rendererPane.removeAll();
    }
    
    protected void paintHorizontalPartOfLeg(Graphics g, Rectangle clipBounds, Insets insets, Rectangle bounds, TreePath path, int row, boolean isExpanded, boolean hasBeenExpanded, boolean isLeaf) {
        if (!paintLines) {
            return;
        }
        int depth = path.getPathCount() - 1;
        if ((depth == 0 || (depth == 1 && !isRootVisible())) && !getShowsRootHandles()) {
            return;
        }
        int clipLeft = clipBounds.x;
        int clipRight = clipBounds.x + (clipBounds.width - 1);
        int clipTop = clipBounds.y;
        int clipBottom = clipBounds.y + (clipBounds.height - 1);
        int lineY = bounds.y + bounds.height / 2;
        if (leftToRight) {
            int leftX = bounds.x - getRightChildIndent();
            int nodeX = bounds.x - getHorizontalLegBuffer();
            if (lineY >= clipTop && lineY <= clipBottom && nodeX >= clipLeft && leftX <= clipRight) {
                leftX = Math.max(Math.max(insets.left, leftX), clipLeft);
                nodeX = Math.min(Math.max(insets.left, nodeX), clipRight);
                if (leftX != nodeX) {
                    g.setColor(getHashColor());
                    paintHorizontalLine(g, tree, lineY, leftX, nodeX);
                }
            }
        } else {
            int leftX = bounds.x + bounds.width + getRightChildIndent();
            int nodeX = bounds.x + bounds.width + getHorizontalLegBuffer() - 1;
            if (lineY >= clipTop && lineY <= clipBottom && leftX >= clipLeft && nodeX <= clipRight) {
                leftX = Math.min(leftX, clipRight);
                nodeX = Math.max(nodeX, clipLeft);
                g.setColor(getHashColor());
                paintHorizontalLine(g, tree, lineY, nodeX, leftX);
            }
        }
    }
    
    protected void paintVerticalPartOfLeg(Graphics g, Rectangle clipBounds, Insets insets, TreePath path) {
        if (!paintLines) {
            return;
        }
        int depth = path.getPathCount() - 1;
        if (depth == 0 && !getShowsRootHandles() && !isRootVisible()) {
            return;
        }
        int lineX = getRowX(-1, depth + 1);
        if (leftToRight) {
            lineX = lineX - getRightChildIndent() + insets.left;
        } else {
            lineX = lastWidth - getRowX(-1, depth) - 9;
        }
        int clipLeft = clipBounds.x;
        int clipRight = clipBounds.x + (clipBounds.width - 1);
        if (lineX >= clipLeft && lineX <= clipRight) {
            int clipTop = clipBounds.y;
            int clipBottom = clipBounds.y + clipBounds.height;
            Rectangle parentBounds = getPathBounds(tree, path);
            Rectangle lastChildBounds = getPathBounds(tree, getLastChildPath(path));
            if (lastChildBounds == null) return;
            int top;
            if (parentBounds == null) {
                top = Math.max(insets.top + getVerticalLegBuffer(), clipTop);
            } else top = Math.max(parentBounds.y + parentBounds.height + getVerticalLegBuffer(), clipTop);
            if (depth == 0 && !isRootVisible()) {
                TreeModel model = getModel();
                if (model != null) {
                    Object root = model.getRoot();
                    if (model.getChildCount(root) > 0) {
                        parentBounds = getPathBounds(tree, path.pathByAddingChild(model.getChild(root, 0)));
                        if (parentBounds != null) top = Math.max(insets.top + getVerticalLegBuffer(), parentBounds.y + parentBounds.height / 2);
                    }
                }
            }
            int bottom = Math.min(lastChildBounds.y + (lastChildBounds.height / 2), clipBottom);
            if (top <= bottom) {
                g.setColor(getHashColor());
                paintVerticalLine(g, tree, lineX, top, bottom);
            }
        }
    }
    
    protected void paintExpandControl(Graphics g, Rectangle clipBounds, Insets insets, Rectangle bounds, TreePath path, int row, boolean isExpanded, boolean hasBeenExpanded, boolean isLeaf) {
        Object value = path.getLastPathComponent();
        if (!isLeaf && (!hasBeenExpanded || treeModel.getChildCount(value) > 0)) {
            int middleXOfKnob;
            if (leftToRight) {
                middleXOfKnob = bounds.x - (getRightChildIndent() - 1);
            } else {
                middleXOfKnob = bounds.x + bounds.width + getRightChildIndent();
            }
            int middleYOfKnob = bounds.y + (bounds.height / 2);
            if (isExpanded) {
                Icon expandedIcon = getExpandedIcon();
                if (expandedIcon != null) drawCentered(tree, g, expandedIcon, middleXOfKnob, middleYOfKnob);
            } else {
                Icon collapsedIcon = getCollapsedIcon();
                if (collapsedIcon != null) drawCentered(tree, g, collapsedIcon, middleXOfKnob, middleYOfKnob);
            }
        }
    }
    
    protected void paintRow(Graphics g, Rectangle clipBounds, Insets insets, Rectangle bounds, TreePath path, int row, boolean isExpanded, boolean hasBeenExpanded, boolean isLeaf) {
        if (editingComponent != null && editingRow == row) return;
        int leadIndex;
        if (tree.hasFocus()) {
            leadIndex = getLeadSelectionRow();
        } else leadIndex = -1;
        Component component;
        component = currentCellRenderer.getTreeCellRendererComponent(tree, path.getLastPathComponent(), tree.isRowSelected(row), isExpanded, isLeaf, row, (leadIndex == row));
        rendererPane.paintComponent(g, component, tree, bounds.x, bounds.y, bounds.width, bounds.height, true);
    }
    
    protected boolean shouldPaintExpandControl(TreePath path, int row, boolean isExpanded, boolean hasBeenExpanded, boolean isLeaf) {
        if (isLeaf) return false;
        int depth = path.getPathCount() - 1;
        if ((depth == 0 || (depth == 1 && !isRootVisible())) && !getShowsRootHandles()) return false;
        return true;
    }
    
    protected void paintVerticalLine(Graphics g, JComponent c, int x, int top, int bottom) {
        if (lineTypeDashed) {
            drawDashedVerticalLine(g, x, top, bottom);
        } else {
            g.drawLine(x, top, x, bottom);
        }
    }
    
    protected void paintHorizontalLine(Graphics g, JComponent c, int y, int left, int right) {
        if (lineTypeDashed) {
            drawDashedHorizontalLine(g, y, left, right);
        } else {
            g.drawLine(left, y, right, y);
        }
    }
    
    protected int getVerticalLegBuffer() {
        return 0;
    }
    
    protected int getHorizontalLegBuffer() {
        return 0;
    }
    
    protected void drawCentered(Component c, Graphics graphics, Icon icon, int x, int y) {
        icon.paintIcon(c, graphics, x - icon.getIconWidth() / 2, y - icon.getIconHeight() / 2);
    }
    
    protected void drawDashedHorizontalLine(Graphics g, int y, int x1, int x2) {
        x1 += (x1 % 2);
        for (int x = x1; x <= x2; x += 2) {
            g.drawLine(x, y, x, y);
        }
    }
    
    protected void drawDashedVerticalLine(Graphics g, int x, int y1, int y2) {
        y1 += (y1 % 2);
        for (int y = y1; y <= y2; y += 2) {
            g.drawLine(x, y, x, y);
        }
    }
    
    protected int getRowX(int row, int depth) {
        return totalChildIndent * (depth + depthOffset);
    }
    
    protected void updateLayoutCacheExpandedNodes() {
        if (treeModel != null && treeModel.getRoot() != null) updateExpandedDescendants(new TreePath(treeModel.getRoot()));
    }
    
    protected void updateExpandedDescendants(TreePath path) {
        completeEditing();
        if (treeState != null) {
            treeState.setExpandedState(path, true);
            Enumeration descendants = tree.getExpandedDescendants(path);
            if (descendants != null) {
                while (descendants.hasMoreElements()) {
                    path = (TreePath)(TreePath)descendants.nextElement();
                    treeState.setExpandedState(path, true);
                }
            }
            updateLeadRow();
            updateSize();
        }
    }
    
    protected TreePath getLastChildPath(TreePath parent) {
        if (treeModel != null) {
            int childCount = treeModel.getChildCount(parent.getLastPathComponent());
            if (childCount > 0) return parent.pathByAddingChild(treeModel.getChild(parent.getLastPathComponent(), childCount - 1));
        }
        return null;
    }
    
    protected void updateDepthOffset() {
        if (isRootVisible()) {
            if (getShowsRootHandles()) depthOffset = 1; else depthOffset = 0;
        } else if (!getShowsRootHandles()) depthOffset = -1; else depthOffset = 0;
    }
    
    protected void updateCellEditor() {
        TreeCellEditor newEditor;
        completeEditing();
        if (tree == null) newEditor = null; else {
            if (tree.isEditable()) {
                newEditor = tree.getCellEditor();
                if (newEditor == null) {
                    newEditor = createDefaultCellEditor();
                    if (newEditor != null) {
                        tree.setCellEditor(newEditor);
                        createdCellEditor = true;
                    }
                }
            } else newEditor = null;
        }
        if (newEditor != cellEditor) {
            if (cellEditor != null && cellEditorListener != null) cellEditor.removeCellEditorListener(cellEditorListener);
            cellEditor = newEditor;
            if (cellEditorListener == null) cellEditorListener = createCellEditorListener();
            if (newEditor != null && cellEditorListener != null) newEditor.addCellEditorListener(cellEditorListener);
            createdCellEditor = false;
        }
    }
    
    protected void updateRenderer() {
        if (tree != null) {
            TreeCellRenderer newCellRenderer;
            newCellRenderer = tree.getCellRenderer();
            if (newCellRenderer == null) {
                tree.setCellRenderer(createDefaultCellRenderer());
                createdRenderer = true;
            } else {
                createdRenderer = false;
                currentCellRenderer = newCellRenderer;
                if (createdCellEditor) {
                    tree.setCellEditor(null);
                }
            }
        } else {
            createdRenderer = false;
            currentCellRenderer = null;
        }
        updateCellEditor();
    }
    
    protected void configureLayoutCache() {
        if (treeState != null && tree != null) {
            if (nodeDimensions == null) nodeDimensions = createNodeDimensions();
            treeState.setNodeDimensions(nodeDimensions);
            treeState.setRootVisible(tree.isRootVisible());
            treeState.setRowHeight(tree.getRowHeight());
            treeState.setSelectionModel(getSelectionModel());
            if (treeState.getModel() != tree.getModel()) treeState.setModel(tree.getModel());
            updateLayoutCacheExpandedNodes();
            if (isLargeModel()) {
                if (componentListener == null) {
                    componentListener = createComponentListener();
                    if (componentListener != null) tree.addComponentListener(componentListener);
                }
            } else if (componentListener != null) {
                tree.removeComponentListener(componentListener);
                componentListener = null;
            }
        } else if (componentListener != null) {
            tree.removeComponentListener(componentListener);
            componentListener = null;
        }
    }
    
    protected void updateSize() {
        validCachedPreferredSize = false;
        tree.treeDidChange();
    }
    
    protected void updateCachedPreferredSize() {
        if (treeState != null) {
            Insets i = tree.getInsets();
            if (isLargeModel()) {
                Rectangle visRect = tree.getVisibleRect();
                if (i != null) {
                    visRect.x -= i.left;
                    visRect.y -= i.top;
                }
                if (leftToRight) {
                    preferredSize.width = treeState.getPreferredWidth(visRect);
                } else {
                    if (getRowCount(tree) == 0) {
                        preferredSize.width = 0;
                    } else {
                        preferredSize.width = lastWidth - getMinX(visRect);
                    }
                }
            } else if (leftToRight) {
                preferredSize.width = treeState.getPreferredWidth(null);
            } else {
                Rectangle tempRect = null;
                int rowCount = tree.getRowCount();
                int width = 0;
                for (int counter = 0; counter < rowCount; counter++) {
                    tempRect = treeState.getBounds(treeState.getPathForRow(counter), tempRect);
                    if (tempRect != null) {
                        width = Math.max(lastWidth - tempRect.x, width);
                    }
                }
                preferredSize.width = width;
            }
            preferredSize.height = treeState.getPreferredHeight();
            if (i != null) {
                preferredSize.width += i.left + i.right;
                preferredSize.height += i.top + i.bottom;
            }
        }
        validCachedPreferredSize = true;
    }
    
    private int getMinX(Rectangle bounds) {
        TreePath firstPath;
        int endY;
        if (bounds == null) {
            firstPath = getPathForRow(tree, 0);
            endY = Integer.MAX_VALUE;
        } else {
            firstPath = treeState.getPathClosestTo(bounds.x, bounds.y);
            endY = bounds.height + bounds.y;
        }
        Enumeration paths = treeState.getVisiblePathsFrom(firstPath);
        int minX = 0;
        if (paths != null && paths.hasMoreElements()) {
            Rectangle pBounds = treeState.getBounds((TreePath)(TreePath)paths.nextElement(), null);
            int width;
            if (pBounds != null) {
                minX = pBounds.x + pBounds.width;
                if (pBounds.y >= endY) {
                    return minX;
                }
            }
            while (pBounds != null && paths.hasMoreElements()) {
                pBounds = treeState.getBounds((TreePath)(TreePath)paths.nextElement(), pBounds);
                if (pBounds != null && pBounds.y < endY) {
                    minX = Math.min(minX, pBounds.x);
                } else {
                    pBounds = null;
                }
            }
            return minX;
        }
        return minX;
    }
    
    protected void pathWasExpanded(TreePath path) {
        if (tree != null) {
            tree.fireTreeExpanded(path);
        }
    }
    
    protected void pathWasCollapsed(TreePath path) {
        if (tree != null) {
            tree.fireTreeCollapsed(path);
        }
    }
    
    protected void ensureRowsAreVisible(int beginRow, int endRow) {
        if (tree != null && beginRow >= 0 && endRow < getRowCount(tree)) {
            boolean scrollVert = DefaultLookup.getBoolean(tree, this, "Tree.scrollsHorizontallyAndVertically", false);
            if (beginRow == endRow) {
                Rectangle scrollBounds = getPathBounds(tree, getPathForRow(tree, beginRow));
                if (scrollBounds != null) {
                    if (!scrollVert) {
                        scrollBounds.x = tree.getVisibleRect().x;
                        scrollBounds.width = 1;
                    }
                    tree.scrollRectToVisible(scrollBounds);
                }
            } else {
                Rectangle beginRect = getPathBounds(tree, getPathForRow(tree, beginRow));
                Rectangle visRect = tree.getVisibleRect();
                Rectangle testRect = beginRect;
                int beginY = beginRect.y;
                int maxY = beginY + visRect.height;
                for (int counter = beginRow + 1; counter <= endRow; counter++) {
                    testRect = getPathBounds(tree, getPathForRow(tree, counter));
                    if ((testRect.y + testRect.height) > maxY) counter = endRow;
                }
                tree.scrollRectToVisible(new Rectangle(visRect.x, beginY, 1, testRect.y + testRect.height - beginY));
            }
        }
    }
    
    public void setPreferredMinSize(Dimension newSize) {
        preferredMinSize = newSize;
    }
    
    public Dimension getPreferredMinSize() {
        if (preferredMinSize == null) return null;
        return new Dimension(preferredMinSize);
    }
    
    public Dimension getPreferredSize(JComponent c) {
        return getPreferredSize(c, true);
    }
    
    public Dimension getPreferredSize(JComponent c, boolean checkConsistancy) {
        Dimension pSize = this.getPreferredMinSize();
        if (!validCachedPreferredSize) updateCachedPreferredSize();
        if (tree != null) {
            if (pSize != null) return new Dimension(Math.max(pSize.width, preferredSize.width), Math.max(pSize.height, preferredSize.height));
            return new Dimension(preferredSize.width, preferredSize.height);
        } else if (pSize != null) return pSize; else return new Dimension(0, 0);
    }
    
    public Dimension getMinimumSize(JComponent c) {
        if (this.getPreferredMinSize() != null) return this.getPreferredMinSize();
        return new Dimension(0, 0);
    }
    
    public Dimension getMaximumSize(JComponent c) {
        if (tree != null) return getPreferredSize(tree);
        if (this.getPreferredMinSize() != null) return this.getPreferredMinSize();
        return new Dimension(0, 0);
    }
    
    protected void completeEditing() {
        if (tree.getInvokesStopCellEditing() && stopEditingInCompleteEditing && editingComponent != null) {
            cellEditor.stopCellEditing();
        }
        completeEditing(false, true, false);
    }
    
    protected void completeEditing(boolean messageStop, boolean messageCancel, boolean messageTree) {
        if (stopEditingInCompleteEditing && editingComponent != null) {
            Component oldComponent = editingComponent;
            TreePath oldPath = editingPath;
            TreeCellEditor oldEditor = cellEditor;
            Object newValue = oldEditor.getCellEditorValue();
            Rectangle editingBounds = getPathBounds(tree, editingPath);
            boolean requestFocus = (tree != null && (tree.hasFocus() || SwingUtilities.findFocusOwner(editingComponent) != null));
            editingComponent = null;
            editingPath = null;
            if (messageStop) oldEditor.stopCellEditing(); else if (messageCancel) oldEditor.cancelCellEditing();
            tree.remove(oldComponent);
            if (editorHasDifferentSize) {
                treeState.invalidatePathBounds(oldPath);
                updateSize();
            } else {
                editingBounds.x = 0;
                editingBounds.width = tree.getSize().width;
                tree.repaint(editingBounds);
            }
            if (requestFocus) tree.requestFocus();
            if (messageTree) treeModel.valueForPathChanged(oldPath, newValue);
        }
    }
    
    private boolean startEditingOnRelease(TreePath path, MouseEvent event, MouseEvent releaseEvent) {
        this.releaseEvent = releaseEvent;
        try {
            return startEditing(path, event);
        } finally {
            this.releaseEvent = null;
        }
    }
    
    protected boolean startEditing(TreePath path, MouseEvent event) {
        if (isEditing(tree) && tree.getInvokesStopCellEditing() && !stopEditing(tree)) {
            return false;
        }
        completeEditing();
        if (cellEditor != null && tree.isPathEditable(path)) {
            int row = getRowForPath(tree, path);
            if (cellEditor.isCellEditable(event)) {
                editingComponent = cellEditor.getTreeCellEditorComponent(tree, path.getLastPathComponent(), tree.isPathSelected(path), tree.isExpanded(path), treeModel.isLeaf(path.getLastPathComponent()), row);
                Rectangle nodeBounds = getPathBounds(tree, path);
                editingRow = row;
                Dimension editorSize = editingComponent.getPreferredSize();
                if (editorSize.height != nodeBounds.height && getRowHeight() > 0) editorSize.height = getRowHeight();
                if (editorSize.width != nodeBounds.width || editorSize.height != nodeBounds.height) {
                    editorHasDifferentSize = true;
                    treeState.invalidatePathBounds(path);
                    updateSize();
                } else editorHasDifferentSize = false;
                tree.add(editingComponent);
                editingComponent.setBounds(nodeBounds.x, nodeBounds.y, editorSize.width, editorSize.height);
                editingPath = path;
                editingComponent.validate();
                Rectangle visRect = tree.getVisibleRect();
                tree.paintImmediately(nodeBounds.x, nodeBounds.y, visRect.width + visRect.x - nodeBounds.x, editorSize.height);
                if (cellEditor.shouldSelectCell(event)) {
                    stopEditingInCompleteEditing = false;
                    try {
                        tree.setSelectionRow(row);
                    } catch (Exception e) {
                        System.err.println("Editing exception: " + e);
                    }
                    stopEditingInCompleteEditing = true;
                }
                Component focusedComponent = BasicLookAndFeel.compositeRequestFocus(editingComponent);
                boolean selectAll = true;
                if (event != null && event instanceof MouseEvent) {
                    Point componentPoint = SwingUtilities.convertPoint(tree, new Point(event.getX(), event.getY()), editingComponent);
                    Component activeComponent = SwingUtilities.getDeepestComponentAt(editingComponent, componentPoint.x, componentPoint.y);
                    if (activeComponent != null) {
                        BasicTreeUI$MouseInputHandler handler = new BasicTreeUI$MouseInputHandler(this, tree, activeComponent, event, focusedComponent);
                        if (releaseEvent != null) {
                            handler.mouseReleased(releaseEvent);
                        }
                        selectAll = false;
                    }
                }
                if (selectAll && focusedComponent instanceof JTextField) {
                    ((JTextField)(JTextField)focusedComponent).selectAll();
                }
                return true;
            } else editingComponent = null;
        }
        return false;
    }
    
    protected void checkForClickInExpandControl(TreePath path, int mouseX, int mouseY) {
        if (isLocationInExpandControl(path, mouseX, mouseY)) {
            handleExpandControlClick(path, mouseX, mouseY);
        }
    }
    
    protected boolean isLocationInExpandControl(TreePath path, int mouseX, int mouseY) {
        if (path != null && !treeModel.isLeaf(path.getLastPathComponent())) {
            int boxWidth;
            Insets i = tree.getInsets();
            if (getExpandedIcon() != null) boxWidth = getExpandedIcon().getIconWidth(); else boxWidth = 8;
            int boxLeftX = getRowX(tree.getRowForPath(path), path.getPathCount() - 1) - getRightChildIndent() - boxWidth / 2;
            if (leftToRight) {
                boxLeftX += i.left;
            } else {
                boxLeftX = i.left + lastWidth - 1 - ((path.getPathCount() - 2 + depthOffset) * totalChildIndent) - getLeftChildIndent() - boxWidth / 2;
            }
            int boxRightX = boxLeftX + boxWidth;
            return mouseX >= boxLeftX && mouseX <= boxRightX;
        }
        return false;
    }
    
    protected void handleExpandControlClick(TreePath path, int mouseX, int mouseY) {
        toggleExpandState(path);
    }
    
    protected void toggleExpandState(TreePath path) {
        if (!tree.isExpanded(path)) {
            int row = getRowForPath(tree, path);
            tree.expandPath(path);
            updateSize();
            if (row != -1) {
                if (tree.getScrollsOnExpand()) ensureRowsAreVisible(row, row + treeState.getVisibleChildCount(path)); else ensureRowsAreVisible(row, row);
            }
        } else {
            tree.collapsePath(path);
            updateSize();
        }
    }
    
    protected boolean isToggleSelectionEvent(MouseEvent event) {
        return (SwingUtilities.isLeftMouseButton(event) && event.isControlDown());
    }
    
    protected boolean isMultiSelectEvent(MouseEvent event) {
        return (SwingUtilities.isLeftMouseButton(event) && event.isShiftDown());
    }
    
    protected boolean isToggleEvent(MouseEvent event) {
        if (!SwingUtilities.isLeftMouseButton(event)) {
            return false;
        }
        int clickCount = tree.getToggleClickCount();
        if (clickCount <= 0) {
            return false;
        }
        return ((event.getClickCount() % clickCount) == 0);
    }
    
    protected void selectPathForEvent(TreePath path, MouseEvent event) {
        if (isMultiSelectEvent(event)) {
            TreePath anchor = getAnchorSelectionPath();
            int anchorRow = (anchor == null) ? -1 : getRowForPath(tree, anchor);
            if (anchorRow == -1 || tree.getSelectionModel().getSelectionMode() == TreeSelectionModel.SINGLE_TREE_SELECTION) {
                tree.setSelectionPath(path);
            } else {
                int row = getRowForPath(tree, path);
                TreePath lastAnchorPath = anchor;
                if (isToggleSelectionEvent(event)) {
                    if (tree.isRowSelected(anchorRow)) {
                        tree.addSelectionInterval(anchorRow, row);
                    } else {
                        tree.removeSelectionInterval(anchorRow, row);
                        tree.addSelectionInterval(row, row);
                    }
                } else if (row < anchorRow) {
                    tree.setSelectionInterval(row, anchorRow);
                } else {
                    tree.setSelectionInterval(anchorRow, row);
                }
                lastSelectedRow = row;
                setAnchorSelectionPath(lastAnchorPath);
                setLeadSelectionPath(path);
            }
        } else if (isToggleSelectionEvent(event)) {
            if (tree.isPathSelected(path)) tree.removeSelectionPath(path); else tree.addSelectionPath(path);
            lastSelectedRow = getRowForPath(tree, path);
            setAnchorSelectionPath(path);
            setLeadSelectionPath(path);
        } else if (SwingUtilities.isLeftMouseButton(event)) {
            tree.setSelectionPath(path);
            if (isToggleEvent(event)) {
                toggleExpandState(path);
            }
        }
    }
    
    protected boolean isLeaf(int row) {
        TreePath path = getPathForRow(tree, row);
        if (path != null) return treeModel.isLeaf(path.getLastPathComponent());
        return true;
    }
    
    private void setAnchorSelectionPath(TreePath newPath) {
        ignoreLAChange = true;
        try {
            tree.setAnchorSelectionPath(newPath);
        } finally {
            ignoreLAChange = false;
        }
    }
    
    private TreePath getAnchorSelectionPath() {
        return tree.getAnchorSelectionPath();
    }
    
    private void setLeadSelectionPath(TreePath newPath) {
        setLeadSelectionPath(newPath, false);
    }
    
    private void setLeadSelectionPath(TreePath newPath, boolean repaint) {
        Rectangle bounds = repaint ? getPathBounds(tree, getLeadSelectionPath()) : null;
        ignoreLAChange = true;
        try {
            tree.setLeadSelectionPath(newPath);
        } finally {
            ignoreLAChange = false;
        }
        leadRow = getRowForPath(tree, newPath);
        if (repaint) {
            if (bounds != null) tree.repaint(bounds);
            bounds = getPathBounds(tree, newPath);
            if (bounds != null) tree.repaint(bounds);
        }
    }
    
    private TreePath getLeadSelectionPath() {
        return tree.getLeadSelectionPath();
    }
    
    private void updateLeadRow() {
        leadRow = getRowForPath(tree, getLeadSelectionPath());
    }
    
    private int getLeadSelectionRow() {
        return leadRow;
    }
    
    private void extendSelection(TreePath newLead) {
        TreePath aPath = getAnchorSelectionPath();
        int aRow = (aPath == null) ? -1 : getRowForPath(tree, aPath);
        int newIndex = getRowForPath(tree, newLead);
        if (aRow == -1) {
            tree.setSelectionRow(newIndex);
        } else {
            if (aRow < newIndex) {
                tree.setSelectionInterval(aRow, newIndex);
            } else {
                tree.setSelectionInterval(newIndex, aRow);
            }
            setAnchorSelectionPath(aPath);
            setLeadSelectionPath(newLead);
        }
    }
    
    private void repaintPath(TreePath path) {
        if (path != null) {
            Rectangle bounds = getPathBounds(tree, path);
            if (bounds != null) {
                tree.repaint(bounds.x, bounds.y, bounds.width, bounds.height);
            }
        }
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    private static final BasicTreeUI$TreeDragGestureRecognizer defaultDragRecognizer = SwingUtilities2.DRAG_FIX ? null : new BasicTreeUI$TreeDragGestureRecognizer();
    {
    }
    private static DropTargetListener defaultDropTargetListener = null;
    {
    }
    private static final TransferHandler defaultTransferHandler = new BasicTreeUI$TreeTransferHandler();
    {
    }
    {
    }
    {
    }
    {
    }
}
