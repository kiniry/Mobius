package javax.swing.tree;

import javax.swing.tree.TreePath;

public interface RowMapper {
    
    int[] getRowsForPaths(TreePath[] path);
}
