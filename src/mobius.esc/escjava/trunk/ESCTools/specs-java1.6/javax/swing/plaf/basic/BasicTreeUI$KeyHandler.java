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

public class BasicTreeUI$KeyHandler extends KeyAdapter {
    /*synthetic*/ final BasicTreeUI this$0;
    
    public BasicTreeUI$KeyHandler(/*synthetic*/ final BasicTreeUI this$0) {
        this.this$0 = this$0;
        
    }
    protected Action repeatKeyAction;
    protected boolean isKeyDown;
    
    public void keyTyped(KeyEvent e) {
        BasicTreeUI.access$200(this$0).keyTyped(e);
    }
    
    public void keyPressed(KeyEvent e) {
        BasicTreeUI.access$200(this$0).keyPressed(e);
    }
    
    public void keyReleased(KeyEvent e) {
        BasicTreeUI.access$200(this$0).keyReleased(e);
    }
}
