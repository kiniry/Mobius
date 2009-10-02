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

public class BasicTreeUI$CellEditorHandler implements CellEditorListener {
    /*synthetic*/ final BasicTreeUI this$0;
    
    public BasicTreeUI$CellEditorHandler(/*synthetic*/ final BasicTreeUI this$0) {
        this.this$0 = this$0;
        
    }
    
    public void editingStopped(ChangeEvent e) {
        BasicTreeUI.access$200(this$0).editingStopped(e);
    }
    
    public void editingCanceled(ChangeEvent e) {
        BasicTreeUI.access$200(this$0).editingCanceled(e);
    }
}
