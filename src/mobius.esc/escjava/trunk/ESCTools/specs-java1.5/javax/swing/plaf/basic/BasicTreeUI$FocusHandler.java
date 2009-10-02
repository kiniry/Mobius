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

public class BasicTreeUI$FocusHandler implements FocusListener {
    /*synthetic*/ final BasicTreeUI this$0;
    
    public BasicTreeUI$FocusHandler(/*synthetic*/ final BasicTreeUI this$0) {
        this.this$0 = this$0;
        
    }
    
    public void focusGained(FocusEvent e) {
        BasicTreeUI.access$200(this$0).focusGained(e);
    }
    
    public void focusLost(FocusEvent e) {
        focusGained(e);
    }
}
