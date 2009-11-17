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

public class BasicTreeUI$TreeCancelEditingAction extends AbstractAction {
    /*synthetic*/ final BasicTreeUI this$0;
    
    public BasicTreeUI$TreeCancelEditingAction(/*synthetic*/ final BasicTreeUI this$0, String name) {
        this.this$0 = this$0;
        
    }
    
    public void actionPerformed(ActionEvent e) {
        if (this$0.tree != null) {
            BasicTreeUI.Actions.access$1100(BasicTreeUI.access$500(), this$0.tree, this$0);
        }
    }
    
    public boolean isEnabled() {
        return (this$0.tree != null && this$0.tree.isEnabled() && this$0.isEditing(this$0.tree));
    }
}
