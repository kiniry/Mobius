package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.io.*;
import java.util.*;
import javax.swing.event.*;
import javax.swing.tree.*;
import javax.accessibility.*;

public class JTree$EmptySelectionModel extends DefaultTreeSelectionModel {
    
    protected JTree$EmptySelectionModel() {
        
    }
    protected static final JTree$EmptySelectionModel sharedInstance = new JTree$EmptySelectionModel();
    
    public static JTree$EmptySelectionModel sharedInstance() {
        return sharedInstance;
    }
    
    public void setSelectionPaths(TreePath[] pPaths) {
    }
    
    public void addSelectionPaths(TreePath[] paths) {
    }
    
    public void removeSelectionPaths(TreePath[] paths) {
    }
}
