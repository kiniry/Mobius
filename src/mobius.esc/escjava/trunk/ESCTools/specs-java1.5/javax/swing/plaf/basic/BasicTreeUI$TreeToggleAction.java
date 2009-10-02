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

public class BasicTreeUI$TreeToggleAction extends AbstractAction {
    /*synthetic*/ final BasicTreeUI this$0;
    
    public BasicTreeUI$TreeToggleAction(/*synthetic*/ final BasicTreeUI this$0, String name) {
        this.this$0 = this$0;
        
    }
    
    public void actionPerformed(ActionEvent e) {
        if (this$0.tree != null) {
            BasicTreeUI.Actions.access$1000(BasicTreeUI.access$500(), this$0.tree, this$0);
        }
    }
    
    public boolean isEnabled() {
        return (this$0.tree != null && this$0.tree.isEnabled());
    }
}
