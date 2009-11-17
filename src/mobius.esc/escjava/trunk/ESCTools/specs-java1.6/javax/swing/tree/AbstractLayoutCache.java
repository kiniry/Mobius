package javax.swing.tree;

import javax.swing.event.TreeModelEvent;
import java.awt.Rectangle;
import java.util.Enumeration;

public abstract class AbstractLayoutCache implements RowMapper {
    
    public AbstractLayoutCache() {
        
    }
    protected AbstractLayoutCache$NodeDimensions nodeDimensions;
    protected TreeModel treeModel;
    protected TreeSelectionModel treeSelectionModel;
    protected boolean rootVisible;
    protected int rowHeight;
    
    public void setNodeDimensions(AbstractLayoutCache$NodeDimensions nd) {
        this.nodeDimensions = nd;
    }
    
    public AbstractLayoutCache$NodeDimensions getNodeDimensions() {
        return nodeDimensions;
    }
    
    public void setModel(TreeModel newModel) {
        treeModel = newModel;
    }
    
    public TreeModel getModel() {
        return treeModel;
    }
    
    public void setRootVisible(boolean rootVisible) {
        this.rootVisible = rootVisible;
    }
    
    public boolean isRootVisible() {
        return rootVisible;
    }
    
    public void setRowHeight(int rowHeight) {
        this.rowHeight = rowHeight;
    }
    
    public int getRowHeight() {
        return rowHeight;
    }
    
    public void setSelectionModel(TreeSelectionModel newLSM) {
        if (treeSelectionModel != null) treeSelectionModel.setRowMapper(null);
        treeSelectionModel = newLSM;
        if (treeSelectionModel != null) treeSelectionModel.setRowMapper(this);
    }
    
    public TreeSelectionModel getSelectionModel() {
        return treeSelectionModel;
    }
    
    public int getPreferredHeight() {
        int rowCount = getRowCount();
        if (rowCount > 0) {
            Rectangle bounds = getBounds(getPathForRow(rowCount - 1), null);
            if (bounds != null) return bounds.y + bounds.height;
        }
        return 0;
    }
    
    public int getPreferredWidth(Rectangle bounds) {
        int rowCount = getRowCount();
        if (rowCount > 0) {
            TreePath firstPath;
            int endY;
            if (bounds == null) {
                firstPath = getPathForRow(0);
                endY = Integer.MAX_VALUE;
            } else {
                firstPath = getPathClosestTo(bounds.x, bounds.y);
                endY = bounds.height + bounds.y;
            }
            Enumeration paths = getVisiblePathsFrom(firstPath);
            if (paths != null && paths.hasMoreElements()) {
                Rectangle pBounds = getBounds((TreePath)(TreePath)paths.nextElement(), null);
                int width;
                if (pBounds != null) {
                    width = pBounds.x + pBounds.width;
                    if (pBounds.y >= endY) {
                        return width;
                    }
                } else width = 0;
                while (pBounds != null && paths.hasMoreElements()) {
                    pBounds = getBounds((TreePath)(TreePath)paths.nextElement(), pBounds);
                    if (pBounds != null && pBounds.y < endY) {
                        width = Math.max(width, pBounds.x + pBounds.width);
                    } else {
                        pBounds = null;
                    }
                }
                return width;
            }
        }
        return 0;
    }
    
    public abstract boolean isExpanded(TreePath path);
    
    public abstract Rectangle getBounds(TreePath path, Rectangle placeIn);
    
    public abstract TreePath getPathForRow(int row);
    
    public abstract int getRowForPath(TreePath path);
    
    public abstract TreePath getPathClosestTo(int x, int y);
    
    public abstract Enumeration getVisiblePathsFrom(TreePath path);
    
    public abstract int getVisibleChildCount(TreePath path);
    
    public abstract void setExpandedState(TreePath path, boolean isExpanded);
    
    public abstract boolean getExpandedState(TreePath path);
    
    public abstract int getRowCount();
    
    public abstract void invalidateSizes();
    
    public abstract void invalidatePathBounds(TreePath path);
    
    public abstract void treeNodesChanged(TreeModelEvent e);
    
    public abstract void treeNodesInserted(TreeModelEvent e);
    
    public abstract void treeNodesRemoved(TreeModelEvent e);
    
    public abstract void treeStructureChanged(TreeModelEvent e);
    
    public int[] getRowsForPaths(TreePath[] paths) {
        if (paths == null) return null;
        int numPaths = paths.length;
        int[] rows = new int[numPaths];
        for (int counter = 0; counter < numPaths; counter++) rows[counter] = getRowForPath(paths[counter]);
        return rows;
    }
    
    protected Rectangle getNodeDimensions(Object value, int row, int depth, boolean expanded, Rectangle placeIn) {
        AbstractLayoutCache$NodeDimensions nd = getNodeDimensions();
        if (nd != null) {
            return nd.getNodeDimensions(value, row, depth, expanded, placeIn);
        }
        return null;
    }
    
    protected boolean isFixedRowHeight() {
        return (rowHeight > 0);
    }
    {
    }
}
