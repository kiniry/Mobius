package javax.swing.tree;

import java.io.*;
import javax.swing.event.*;

class PathPlaceHolder {
    protected boolean isNew;
    protected TreePath path;
    
    PathPlaceHolder(TreePath path, boolean isNew) {
        
        this.path = path;
        this.isNew = isNew;
    }
}
