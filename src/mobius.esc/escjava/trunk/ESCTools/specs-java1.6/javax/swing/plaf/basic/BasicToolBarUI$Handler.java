package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.swing.border.*;
import javax.swing.plaf.*;

class BasicToolBarUI$Handler implements ContainerListener, FocusListener, MouseInputListener, PropertyChangeListener {
    
    /*synthetic*/ BasicToolBarUI$Handler(BasicToolBarUI x0, javax.swing.plaf.basic.BasicToolBarUI$1 x1) {
        this(x0);
    }
    /*synthetic*/ final BasicToolBarUI this$0;
    
    private BasicToolBarUI$Handler(/*synthetic*/ final BasicToolBarUI this$0) {
        this.this$0 = this$0;
        
    }
    
    public void componentAdded(ContainerEvent evt) {
        Component c = evt.getChild();
        if (this$0.toolBarFocusListener != null) {
            c.addFocusListener(this$0.toolBarFocusListener);
        }
        if (this$0.isRolloverBorders()) {
            this$0.setBorderToRollover(c);
        } else {
            this$0.setBorderToNonRollover(c);
        }
    }
    
    public void componentRemoved(ContainerEvent evt) {
        Component c = evt.getChild();
        if (this$0.toolBarFocusListener != null) {
            c.removeFocusListener(this$0.toolBarFocusListener);
        }
        this$0.setBorderToNormal(c);
    }
    
    public void focusGained(FocusEvent evt) {
        Component c = evt.getComponent();
        this$0.focusedCompIndex = this$0.toolBar.getComponentIndex(c);
    }
    
    public void focusLost(FocusEvent evt) {
    }
    JToolBar tb;
    boolean isDragging = false;
    Point origin = null;
    
    public void mousePressed(MouseEvent evt) {
        if (!tb.isEnabled()) {
            return;
        }
        isDragging = false;
    }
    
    public void mouseReleased(MouseEvent evt) {
        if (!tb.isEnabled()) {
            return;
        }
        if (isDragging == true) {
            Point position = evt.getPoint();
            if (origin == null) origin = evt.getComponent().getLocationOnScreen();
            this$0.floatAt(position, origin);
        }
        origin = null;
        isDragging = false;
    }
    
    public void mouseDragged(MouseEvent evt) {
        if (!tb.isEnabled()) {
            return;
        }
        isDragging = true;
        Point position = evt.getPoint();
        if (origin == null) {
            origin = evt.getComponent().getLocationOnScreen();
        }
        this$0.dragTo(position, origin);
    }
    
    public void mouseClicked(MouseEvent evt) {
    }
    
    public void mouseEntered(MouseEvent evt) {
    }
    
    public void mouseExited(MouseEvent evt) {
    }
    
    public void mouseMoved(MouseEvent evt) {
    }
    
    public void propertyChange(PropertyChangeEvent evt) {
        String propertyName = evt.getPropertyName();
        if (propertyName == "lookAndFeel") {
            this$0.toolBar.updateUI();
        } else if (propertyName == "orientation") {
            Component[] components = this$0.toolBar.getComponents();
            int orientation = ((Integer)(Integer)evt.getNewValue()).intValue();
            JToolBar$Separator separator;
            for (int i = 0; i < components.length; ++i) {
                if (components[i] instanceof JToolBar$Separator) {
                    separator = (JToolBar$Separator)(JToolBar$Separator)components[i];
                    if (orientation == JToolBar.HORIZONTAL) {
                        separator.setOrientation(JSeparator.VERTICAL);
                    } else {
                        separator.setOrientation(JSeparator.HORIZONTAL);
                    }
                    Dimension size = separator.getSeparatorSize();
                    if (size != null && size.width != size.height) {
                        Dimension newSize = new Dimension(size.height, size.width);
                        separator.setSeparatorSize(newSize);
                    }
                }
            }
        } else if (propertyName == BasicToolBarUI.access$100()) {
            this$0.installNormalBorders(this$0.toolBar);
            this$0.setRolloverBorders(((Boolean)(Boolean)evt.getNewValue()).booleanValue());
        }
    }
}
