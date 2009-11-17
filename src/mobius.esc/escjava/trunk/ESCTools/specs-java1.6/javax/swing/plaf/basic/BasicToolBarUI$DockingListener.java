package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.swing.border.*;
import javax.swing.plaf.*;

public class BasicToolBarUI$DockingListener implements MouseInputListener {
    /*synthetic*/ final BasicToolBarUI this$0;
    protected JToolBar toolBar;
    protected boolean isDragging = false;
    protected Point origin = null;
    
    public BasicToolBarUI$DockingListener(/*synthetic*/ final BasicToolBarUI this$0, JToolBar t) {
        this.this$0 = this$0;
        
        this.toolBar = t;
        BasicToolBarUI.access$500(this$0).tb = t;
    }
    
    public void mouseClicked(MouseEvent e) {
        BasicToolBarUI.access$500(this$0).mouseClicked(e);
    }
    
    public void mousePressed(MouseEvent e) {
        BasicToolBarUI.access$500(this$0).tb = toolBar;
        BasicToolBarUI.access$500(this$0).mousePressed(e);
        isDragging = BasicToolBarUI.access$500(this$0).isDragging;
    }
    
    public void mouseReleased(MouseEvent e) {
        BasicToolBarUI.access$500(this$0).tb = toolBar;
        BasicToolBarUI.access$500(this$0).isDragging = isDragging;
        BasicToolBarUI.access$500(this$0).origin = origin;
        BasicToolBarUI.access$500(this$0).mouseReleased(e);
        isDragging = BasicToolBarUI.access$500(this$0).isDragging;
        origin = BasicToolBarUI.access$500(this$0).origin;
    }
    
    public void mouseEntered(MouseEvent e) {
        BasicToolBarUI.access$500(this$0).mouseEntered(e);
    }
    
    public void mouseExited(MouseEvent e) {
        BasicToolBarUI.access$500(this$0).mouseExited(e);
    }
    
    public void mouseDragged(MouseEvent e) {
        BasicToolBarUI.access$500(this$0).tb = toolBar;
        BasicToolBarUI.access$500(this$0).origin = origin;
        BasicToolBarUI.access$500(this$0).mouseDragged(e);
        isDragging = BasicToolBarUI.access$500(this$0).isDragging;
        origin = BasicToolBarUI.access$500(this$0).origin;
    }
    
    public void mouseMoved(MouseEvent e) {
        BasicToolBarUI.access$500(this$0).mouseMoved(e);
    }
}
