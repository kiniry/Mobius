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

public class BasicTreeUI$MouseHandler extends MouseAdapter implements MouseMotionListener {
    /*synthetic*/ final BasicTreeUI this$0;
    
    public BasicTreeUI$MouseHandler(/*synthetic*/ final BasicTreeUI this$0) {
        this.this$0 = this$0;
        
    }
    
    public void mousePressed(MouseEvent e) {
        BasicTreeUI.access$200(this$0).mousePressed(e);
    }
    
    public void mouseDragged(MouseEvent e) {
        BasicTreeUI.access$200(this$0).mouseDragged(e);
    }
    
    public void mouseMoved(MouseEvent e) {
        BasicTreeUI.access$200(this$0).mouseMoved(e);
    }
    
    public void mouseReleased(MouseEvent e) {
        BasicTreeUI.access$200(this$0).mouseReleased(e);
    }
}
