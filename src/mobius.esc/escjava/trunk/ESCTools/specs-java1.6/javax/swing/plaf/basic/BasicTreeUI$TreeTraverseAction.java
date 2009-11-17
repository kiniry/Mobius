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

public class BasicTreeUI$TreeTraverseAction extends AbstractAction {
    /*synthetic*/ final BasicTreeUI this$0;
    protected int direction;
    private boolean changeSelection;
    
    public BasicTreeUI$TreeTraverseAction(/*synthetic*/ final BasicTreeUI this$0, int direction, String name) {
        this(this$0, direction, name, true);
    }
    
    private BasicTreeUI$TreeTraverseAction(/*synthetic*/ final BasicTreeUI this$0, int direction, String name, boolean changeSelection) {
        this.this$0 = this$0;
        
        this.direction = direction;
        this.changeSelection = changeSelection;
    }
    
    public void actionPerformed(ActionEvent e) {
        if (this$0.tree != null) {
            BasicTreeUI.Actions.access$600(BasicTreeUI.access$500(), this$0.tree, this$0, direction, changeSelection);
        }
    }
    
    public boolean isEnabled() {
        return (this$0.tree != null && this$0.tree.isEnabled());
    }
}
