package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.datatransfer.*;
import java.awt.dnd.*;
import java.beans.*;
import java.io.*;
import javax.swing.tree.*;

public class BasicTreeUI$TreeModelHandler implements TreeModelListener {
    /*synthetic*/ final BasicTreeUI this$0;
    
    public BasicTreeUI$TreeModelHandler(/*synthetic*/ final BasicTreeUI this$0) {
        this.this$0 = this$0;
        
    }
    
    public void treeNodesChanged(TreeModelEvent e) {
        BasicTreeUI.access$200(this$0).treeNodesChanged(e);
    }
    
    public void treeNodesInserted(TreeModelEvent e) {
        BasicTreeUI.access$200(this$0).treeNodesInserted(e);
    }
    
    public void treeNodesRemoved(TreeModelEvent e) {
        BasicTreeUI.access$200(this$0).treeNodesInserted(e);
    }
    
    public void treeStructureChanged(TreeModelEvent e) {
        BasicTreeUI.access$200(this$0).treeStructureChanged(e);
    }
}
