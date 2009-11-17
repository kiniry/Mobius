package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.datatransfer.*;
import java.awt.dnd.*;
import java.beans.*;
import java.io.*;
import java.util.TooManyListenersException;
import javax.swing.plaf.UIResource;
import javax.swing.tree.*;
import com.sun.java.swing.SwingUtilities2;

class BasicTreeUI$Handler implements CellEditorListener, FocusListener, KeyListener, MouseListener, PropertyChangeListener, TreeExpansionListener, TreeModelListener, TreeSelectionListener {
    
    /*synthetic*/ BasicTreeUI$Handler(BasicTreeUI x0, javax.swing.plaf.basic.BasicTreeUI$1 x1) {
        this(x0);
    }
    /*synthetic*/ final BasicTreeUI this$0;
    
    private BasicTreeUI$Handler(/*synthetic*/ final BasicTreeUI this$0) {
        this.this$0 = this$0;
        
    }
    private String prefix = "";
    private String typedString = "";
    private long lastTime = 0L;
    
    public void keyTyped(KeyEvent e) {
        if (this$0.tree != null && this$0.tree.getRowCount() > 0 && this$0.tree.hasFocus() && this$0.tree.isEnabled()) {
            if (e.isAltDown() || e.isControlDown() || e.isMetaDown() || isNavigationKey(e)) {
                return;
            }
            boolean startingFromSelection = true;
            char c = e.getKeyChar();
            long time = e.getWhen();
            int startingRow = this$0.tree.getLeadSelectionRow();
            if (time - lastTime < BasicTreeUI.access$1200(this$0)) {
                typedString += c;
                if ((prefix.length() == 1) && (c == prefix.charAt(0))) {
                    startingRow++;
                } else {
                    prefix = typedString;
                }
            } else {
                startingRow++;
                typedString = "" + c;
                prefix = typedString;
            }
            lastTime = time;
            if (startingRow < 0 || startingRow >= this$0.tree.getRowCount()) {
                startingFromSelection = false;
                startingRow = 0;
            }
            TreePath path = this$0.tree.getNextMatch(prefix, startingRow, Position$Bias.Forward);
            if (path != null) {
                this$0.tree.setSelectionPath(path);
                int row = this$0.getRowForPath(this$0.tree, path);
                this$0.ensureRowsAreVisible(row, row);
            } else if (startingFromSelection) {
                path = this$0.tree.getNextMatch(prefix, 0, Position$Bias.Forward);
                if (path != null) {
                    this$0.tree.setSelectionPath(path);
                    int row = this$0.getRowForPath(this$0.tree, path);
                    this$0.ensureRowsAreVisible(row, row);
                }
            }
        }
    }
    
    public void keyPressed(KeyEvent e) {
        if (isNavigationKey(e)) {
            prefix = "";
            typedString = "";
            lastTime = 0L;
        }
    }
    
    public void keyReleased(KeyEvent e) {
    }
    
    private boolean isNavigationKey(KeyEvent event) {
        InputMap inputMap = this$0.tree.getInputMap(JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);
        KeyStroke key = KeyStroke.getKeyStrokeForEvent(event);
        if (inputMap != null && inputMap.get(key) != null) {
            return true;
        }
        return false;
    }
    
    public void propertyChange(PropertyChangeEvent event) {
        if (event.getSource() == this$0.treeSelectionModel) {
            this$0.treeSelectionModel.resetRowSelection();
        } else if (event.getSource() == this$0.tree) {
            String changeName = event.getPropertyName();
            if (changeName == JTree.LEAD_SELECTION_PATH_PROPERTY) {
                if (!BasicTreeUI.access$1300(this$0)) {
                    BasicTreeUI.access$1400(this$0);
                    BasicTreeUI.access$1500(this$0, (TreePath)(TreePath)event.getOldValue());
                    BasicTreeUI.access$1500(this$0, (TreePath)(TreePath)event.getNewValue());
                }
            } else if (changeName == JTree.ANCHOR_SELECTION_PATH_PROPERTY) {
                if (!BasicTreeUI.access$1300(this$0)) {
                    BasicTreeUI.access$1500(this$0, (TreePath)(TreePath)event.getOldValue());
                    BasicTreeUI.access$1500(this$0, (TreePath)(TreePath)event.getNewValue());
                }
            }
            if (changeName == JTree.CELL_RENDERER_PROPERTY) {
                this$0.setCellRenderer((TreeCellRenderer)(TreeCellRenderer)event.getNewValue());
                BasicTreeUI.access$1600(this$0);
            } else if (changeName == JTree.TREE_MODEL_PROPERTY) {
                this$0.setModel((TreeModel)(TreeModel)event.getNewValue());
            } else if (changeName == JTree.ROOT_VISIBLE_PROPERTY) {
                this$0.setRootVisible(((Boolean)(Boolean)event.getNewValue()).booleanValue());
            } else if (changeName == JTree.SHOWS_ROOT_HANDLES_PROPERTY) {
                this$0.setShowsRootHandles(((Boolean)(Boolean)event.getNewValue()).booleanValue());
            } else if (changeName == JTree.ROW_HEIGHT_PROPERTY) {
                this$0.setRowHeight(((Integer)(Integer)event.getNewValue()).intValue());
            } else if (changeName == JTree.CELL_EDITOR_PROPERTY) {
                this$0.setCellEditor((TreeCellEditor)(TreeCellEditor)event.getNewValue());
            } else if (changeName == JTree.EDITABLE_PROPERTY) {
                this$0.setEditable(((Boolean)(Boolean)event.getNewValue()).booleanValue());
            } else if (changeName == JTree.LARGE_MODEL_PROPERTY) {
                this$0.setLargeModel(this$0.tree.isLargeModel());
            } else if (changeName == JTree.SELECTION_MODEL_PROPERTY) {
                this$0.setSelectionModel(this$0.tree.getSelectionModel());
            } else if (changeName == "font") {
                this$0.completeEditing();
                if (this$0.treeState != null) this$0.treeState.invalidateSizes();
                this$0.updateSize();
            } else if (changeName == "componentOrientation") {
                if (this$0.tree != null) {
                    BasicTreeUI.access$302(this$0, BasicGraphicsUtils.isLeftToRight(this$0.tree));
                    BasicTreeUI.access$1600(this$0);
                    this$0.tree.treeDidChange();
                    InputMap km = this$0.getInputMap(JComponent.WHEN_FOCUSED);
                    SwingUtilities.replaceUIInputMap(this$0.tree, JComponent.WHEN_FOCUSED, km);
                }
            } else if ("transferHandler" == changeName) {
                DropTarget dropTarget = this$0.tree.getDropTarget();
                if (dropTarget instanceof UIResource) {
                    if (BasicTreeUI.access$1700() == null) {
                        BasicTreeUI.access$1702(new BasicTreeUI$TreeDropTargetListener());
                    }
                    try {
                        dropTarget.addDropTargetListener(BasicTreeUI.access$1700());
                    } catch (TooManyListenersException tmle) {
                    }
                }
            }
        }
    }
    private boolean selectedOnPress;
    
    public void mouseClicked(MouseEvent e) {
    }
    
    public void mouseEntered(MouseEvent e) {
    }
    
    public void mouseExited(MouseEvent e) {
    }
    
    public void mousePressed(MouseEvent e) {
        if (!e.isConsumed()) {
            handleSelection(e);
            selectedOnPress = true;
        } else {
            selectedOnPress = false;
        }
    }
    
    void handleSelection(MouseEvent e) {
        if (this$0.tree != null && this$0.tree.isEnabled()) {
            if (this$0.isEditing(this$0.tree) && this$0.tree.getInvokesStopCellEditing() && !this$0.stopEditing(this$0.tree)) {
                return;
            }
            SwingUtilities2.adjustFocus(this$0.tree);
            TreePath path = this$0.getClosestPathForLocation(this$0.tree, e.getX(), e.getY());
            handleSelectionImpl(e, path);
        }
    }
    
    protected void handleSelectionImpl(MouseEvent e, TreePath path) {
        if (path != null) {
            Rectangle bounds = this$0.getPathBounds(this$0.tree, path);
            if (e.getY() > (bounds.y + bounds.height)) {
                return;
            }
            if (SwingUtilities.isLeftMouseButton(e)) this$0.checkForClickInExpandControl(path, e.getX(), e.getY());
            int x = e.getX();
            if (x > bounds.x && x <= (bounds.x + bounds.width)) {
                if ((SwingUtilities2.DRAG_FIX && this$0.tree.getDragEnabled()) || !this$0.startEditing(path, e)) {
                    this$0.selectPathForEvent(path, e);
                }
            }
        }
    }
    
    public void mouseDragged(MouseEvent e) {
    }
    
    public void mouseMoved(MouseEvent e) {
    }
    
    public void mouseReleased(MouseEvent e) {
        if ((!e.isConsumed()) && (!selectedOnPress)) {
            handleSelection(e);
        }
    }
    
    public void focusGained(FocusEvent e) {
        if (this$0.tree != null) {
            Rectangle pBounds;
            pBounds = this$0.getPathBounds(this$0.tree, this$0.tree.getLeadSelectionPath());
            if (pBounds != null) this$0.tree.repaint(pBounds);
            pBounds = this$0.getPathBounds(this$0.tree, BasicTreeUI.access$1800(this$0));
            if (pBounds != null) this$0.tree.repaint(pBounds);
        }
    }
    
    public void focusLost(FocusEvent e) {
        focusGained(e);
    }
    
    public void editingStopped(ChangeEvent e) {
        this$0.completeEditing(false, false, true);
    }
    
    public void editingCanceled(ChangeEvent e) {
        this$0.completeEditing(false, false, false);
    }
    
    public void valueChanged(TreeSelectionEvent event) {
        this$0.completeEditing();
        if (this$0.tree.getExpandsSelectedPaths() && this$0.treeSelectionModel != null) {
            TreePath[] paths = this$0.treeSelectionModel.getSelectionPaths();
            if (paths != null) {
                for (int counter = paths.length - 1; counter >= 0; counter--) {
                    TreePath path = paths[counter].getParentPath();
                    boolean expand = true;
                    while (path != null) {
                        if (this$0.treeModel.isLeaf(path.getLastPathComponent())) {
                            expand = false;
                            path = null;
                        } else {
                            path = path.getParentPath();
                        }
                    }
                    if (expand) {
                        this$0.tree.makeVisible(paths[counter]);
                    }
                }
            }
        }
        TreePath oldLead = BasicTreeUI.access$1800(this$0);
        this$0.lastSelectedRow = this$0.tree.getMinSelectionRow();
        TreePath lead = this$0.tree.getSelectionModel().getLeadSelectionPath();
        BasicTreeUI.access$1900(this$0, lead);
        BasicTreeUI.access$2000(this$0, lead);
        TreePath[] changedPaths = event.getPaths();
        Rectangle nodeBounds;
        Rectangle visRect = this$0.tree.getVisibleRect();
        boolean paintPaths = true;
        int nWidth = this$0.tree.getWidth();
        if (changedPaths != null) {
            int counter;
            int maxCounter = changedPaths.length;
            if (maxCounter > 4) {
                this$0.tree.repaint();
                paintPaths = false;
            } else {
                for (counter = 0; counter < maxCounter; counter++) {
                    nodeBounds = this$0.getPathBounds(this$0.tree, changedPaths[counter]);
                    if (nodeBounds != null && visRect.intersects(nodeBounds)) this$0.tree.repaint(0, nodeBounds.y, nWidth, nodeBounds.height);
                }
            }
        }
        if (paintPaths) {
            nodeBounds = this$0.getPathBounds(this$0.tree, oldLead);
            if (nodeBounds != null && visRect.intersects(nodeBounds)) this$0.tree.repaint(0, nodeBounds.y, nWidth, nodeBounds.height);
            nodeBounds = this$0.getPathBounds(this$0.tree, lead);
            if (nodeBounds != null && visRect.intersects(nodeBounds)) this$0.tree.repaint(0, nodeBounds.y, nWidth, nodeBounds.height);
        }
    }
    
    public void treeExpanded(TreeExpansionEvent event) {
        if (event != null && this$0.tree != null) {
            TreePath path = event.getPath();
            this$0.updateExpandedDescendants(path);
        }
    }
    
    public void treeCollapsed(TreeExpansionEvent event) {
        if (event != null && this$0.tree != null) {
            TreePath path = event.getPath();
            this$0.completeEditing();
            if (path != null && this$0.tree.isVisible(path)) {
                this$0.treeState.setExpandedState(path, false);
                BasicTreeUI.access$1400(this$0);
                this$0.updateSize();
            }
        }
    }
    
    public void treeNodesChanged(TreeModelEvent e) {
        if (this$0.treeState != null && e != null) {
            this$0.treeState.treeNodesChanged(e);
            TreePath pPath = e.getTreePath().getParentPath();
            if (pPath == null || this$0.treeState.isExpanded(pPath)) this$0.updateSize();
        }
    }
    
    public void treeNodesInserted(TreeModelEvent e) {
        if (this$0.treeState != null && e != null) {
            this$0.treeState.treeNodesInserted(e);
            BasicTreeUI.access$1400(this$0);
            TreePath path = e.getTreePath();
            if (this$0.treeState.isExpanded(path)) {
                this$0.updateSize();
            } else {
                int[] indices = e.getChildIndices();
                int childCount = this$0.treeModel.getChildCount(path.getLastPathComponent());
                if (indices != null && (childCount - indices.length) == 0) this$0.updateSize();
            }
        }
    }
    
    public void treeNodesRemoved(TreeModelEvent e) {
        if (this$0.treeState != null && e != null) {
            this$0.treeState.treeNodesRemoved(e);
            BasicTreeUI.access$1400(this$0);
            TreePath path = e.getTreePath();
            if (this$0.treeState.isExpanded(path) || this$0.treeModel.getChildCount(path.getLastPathComponent()) == 0) this$0.updateSize();
        }
    }
    
    public void treeStructureChanged(TreeModelEvent e) {
        if (this$0.treeState != null && e != null) {
            this$0.treeState.treeStructureChanged(e);
            BasicTreeUI.access$1400(this$0);
            TreePath pPath = e.getTreePath();
            if (pPath != null) {
                pPath = pPath.getParentPath();
            }
            if (pPath == null || this$0.treeState.isExpanded(pPath)) this$0.updateSize();
        }
    }
}
