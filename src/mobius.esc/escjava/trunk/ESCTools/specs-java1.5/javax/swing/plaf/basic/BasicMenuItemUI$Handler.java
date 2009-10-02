package javax.swing.plaf.basic;

import java.awt.*;
import java.awt.event.*;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.border.*;
import javax.swing.plaf.*;

class BasicMenuItemUI$Handler implements MenuDragMouseListener, MouseInputListener, PropertyChangeListener {
    /*synthetic*/ final BasicMenuItemUI this$0;
    
    BasicMenuItemUI$Handler(/*synthetic*/ final BasicMenuItemUI this$0) {
        this.this$0 = this$0;
        
    }
    
    public void mouseClicked(MouseEvent e) {
    }
    
    public void mousePressed(MouseEvent e) {
    }
    
    public void mouseReleased(MouseEvent e) {
        MenuSelectionManager manager = MenuSelectionManager.defaultManager();
        Point p = e.getPoint();
        if (p.x >= 0 && p.x < this$0.menuItem.getWidth() && p.y >= 0 && p.y < this$0.menuItem.getHeight()) {
            this$0.doClick(manager);
        } else {
            manager.processMouseEvent(e);
        }
    }
    
    public void mouseEntered(MouseEvent e) {
        MenuSelectionManager manager = MenuSelectionManager.defaultManager();
        int modifiers = e.getModifiers();
        if ((modifiers & (InputEvent.BUTTON1_MASK | InputEvent.BUTTON2_MASK | InputEvent.BUTTON3_MASK)) != 0) {
            MenuSelectionManager.defaultManager().processMouseEvent(e);
        } else {
            manager.setSelectedPath(this$0.getPath());
        }
    }
    
    public void mouseExited(MouseEvent e) {
        MenuSelectionManager manager = MenuSelectionManager.defaultManager();
        int modifiers = e.getModifiers();
        if ((modifiers & (InputEvent.BUTTON1_MASK | InputEvent.BUTTON2_MASK | InputEvent.BUTTON3_MASK)) != 0) {
            MenuSelectionManager.defaultManager().processMouseEvent(e);
        } else {
            MenuElement[] path = manager.getSelectedPath();
            if (path.length > 1 && path[path.length - 1] == this$0.menuItem) {
                MenuElement[] newPath = new MenuElement[path.length - 1];
                int i;
                int c;
                for (i = 0, c = path.length - 1; i < c; i++) newPath[i] = path[i];
                manager.setSelectedPath(newPath);
            }
        }
    }
    
    public void mouseDragged(MouseEvent e) {
        MenuSelectionManager.defaultManager().processMouseEvent(e);
    }
    
    public void mouseMoved(MouseEvent e) {
    }
    
    public void menuDragMouseEntered(MenuDragMouseEvent e) {
        MenuSelectionManager manager = e.getMenuSelectionManager();
        MenuElement[] path = e.getPath();
        manager.setSelectedPath(path);
    }
    
    public void menuDragMouseDragged(MenuDragMouseEvent e) {
        MenuSelectionManager manager = e.getMenuSelectionManager();
        MenuElement[] path = e.getPath();
        manager.setSelectedPath(path);
    }
    
    public void menuDragMouseExited(MenuDragMouseEvent e) {
    }
    
    public void menuDragMouseReleased(MenuDragMouseEvent e) {
        MenuSelectionManager manager = e.getMenuSelectionManager();
        MenuElement[] path = e.getPath();
        Point p = e.getPoint();
        if (p.x >= 0 && p.x < this$0.menuItem.getWidth() && p.y >= 0 && p.y < this$0.menuItem.getHeight()) {
            this$0.doClick(manager);
        } else {
            manager.clearSelectedPath();
        }
    }
    
    public void propertyChange(PropertyChangeEvent e) {
        String name = e.getPropertyName();
        if (name == "labelFor" || name == "displayedMnemonic" || name == "accelerator") {
            this$0.updateAcceleratorBinding();
        } else if (name == "text" || "font" == name || "foreground" == name) {
            JMenuItem lbl = ((JMenuItem)(JMenuItem)e.getSource());
            String text = lbl.getText();
            BasicHTML.updateRenderer(lbl, text);
        }
    }
}
