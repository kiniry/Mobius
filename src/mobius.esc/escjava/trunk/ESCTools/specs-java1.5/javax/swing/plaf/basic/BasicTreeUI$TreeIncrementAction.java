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

public class BasicTreeUI$TreeIncrementAction extends AbstractAction {
    /*synthetic*/ final BasicTreeUI this$0;
    protected int direction;
    private boolean addToSelection;
    private boolean changeSelection;
    
    public BasicTreeUI$TreeIncrementAction(/*synthetic*/ final BasicTreeUI this$0, int direction, String name) {
        this(this$0, direction, name, false, true);
    }
    
    private BasicTreeUI$TreeIncrementAction(/*synthetic*/ final BasicTreeUI this$0, int direction, String name, boolean addToSelection, boolean changeSelection) {
        this.this$0 = this$0;
        
        this.direction = direction;
        this.addToSelection = addToSelection;
        this.changeSelection = changeSelection;
    }
    
    public void actionPerformed(ActionEvent e) {
        if (this$0.tree != null) {
            BasicTreeUI.Actions.access$800(BasicTreeUI.access$500(), this$0.tree, this$0, direction, addToSelection, changeSelection);
        }
    }
    
    public boolean isEnabled() {
        return (this$0.tree != null && this$0.tree.isEnabled());
    }
}
