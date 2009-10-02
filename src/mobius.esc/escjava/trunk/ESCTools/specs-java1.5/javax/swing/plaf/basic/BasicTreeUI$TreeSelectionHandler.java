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

public class BasicTreeUI$TreeSelectionHandler implements TreeSelectionListener {
    /*synthetic*/ final BasicTreeUI this$0;
    
    public BasicTreeUI$TreeSelectionHandler(/*synthetic*/ final BasicTreeUI this$0) {
        this.this$0 = this$0;
        
    }
    
    public void valueChanged(TreeSelectionEvent event) {
        BasicTreeUI.access$200(this$0).valueChanged(event);
    }
}
