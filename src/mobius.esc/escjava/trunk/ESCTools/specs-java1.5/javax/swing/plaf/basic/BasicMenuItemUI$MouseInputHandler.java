package javax.swing.plaf.basic;

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.border.*;
import javax.swing.plaf.*;

public class BasicMenuItemUI$MouseInputHandler implements MouseInputListener {
    /*synthetic*/ final BasicMenuItemUI this$0;
    
    protected BasicMenuItemUI$MouseInputHandler(/*synthetic*/ final BasicMenuItemUI this$0) {
        this.this$0 = this$0;
        
    }
    
    public void mouseClicked(MouseEvent e) {
        this$0.getHandler().mouseClicked(e);
    }
    
    public void mousePressed(MouseEvent e) {
        this$0.getHandler().mousePressed(e);
    }
    
    public void mouseReleased(MouseEvent e) {
        this$0.getHandler().mouseReleased(e);
    }
    
    public void mouseEntered(MouseEvent e) {
        this$0.getHandler().mouseEntered(e);
    }
    
    public void mouseExited(MouseEvent e) {
        this$0.getHandler().mouseExited(e);
    }
    
    public void mouseDragged(MouseEvent e) {
        this$0.getHandler().mouseDragged(e);
    }
    
    public void mouseMoved(MouseEvent e) {
        this$0.getHandler().mouseMoved(e);
    }
}
