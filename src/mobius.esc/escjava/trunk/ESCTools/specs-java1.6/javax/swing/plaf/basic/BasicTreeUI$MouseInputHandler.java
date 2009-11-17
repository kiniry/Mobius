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
import com.sun.java.swing.SwingUtilities2;

public class BasicTreeUI$MouseInputHandler extends Object implements MouseInputListener {
    /*synthetic*/ final BasicTreeUI this$0;
    protected Component source;
    protected Component destination;
    private Component focusComponent;
    private boolean dispatchedEvent;
    
    public BasicTreeUI$MouseInputHandler(/*synthetic*/ final BasicTreeUI this$0, Component source, Component destination, MouseEvent event) {
        this(this$0, source, destination, event, null);
    }
    
    BasicTreeUI$MouseInputHandler(/*synthetic*/ final BasicTreeUI this$0, Component source, Component destination, MouseEvent event, Component focusComponent) {
        this.this$0 = this$0;
        
        this.source = source;
        this.destination = destination;
        this.source.addMouseListener(this);
        this.source.addMouseMotionListener(this);
        SwingUtilities2.setSkipClickCount(destination, event.getClickCount() - 1);
        destination.dispatchEvent(SwingUtilities.convertMouseEvent(source, event, destination));
        this.focusComponent = focusComponent;
    }
    
    public void mouseClicked(MouseEvent e) {
        if (destination != null) {
            dispatchedEvent = true;
            destination.dispatchEvent(SwingUtilities.convertMouseEvent(source, e, destination));
        }
    }
    
    public void mousePressed(MouseEvent e) {
    }
    
    public void mouseReleased(MouseEvent e) {
        if (destination != null) destination.dispatchEvent(SwingUtilities.convertMouseEvent(source, e, destination));
        removeFromSource();
    }
    
    public void mouseEntered(MouseEvent e) {
        if (!SwingUtilities.isLeftMouseButton(e)) {
            removeFromSource();
        }
    }
    
    public void mouseExited(MouseEvent e) {
        if (!SwingUtilities.isLeftMouseButton(e)) {
            removeFromSource();
        }
    }
    
    public void mouseDragged(MouseEvent e) {
        if (destination != null) {
            dispatchedEvent = true;
            destination.dispatchEvent(SwingUtilities.convertMouseEvent(source, e, destination));
        }
    }
    
    public void mouseMoved(MouseEvent e) {
        removeFromSource();
    }
    
    protected void removeFromSource() {
        if (source != null) {
            source.removeMouseListener(this);
            source.removeMouseMotionListener(this);
            if (focusComponent != null && focusComponent == destination && !dispatchedEvent && (focusComponent instanceof JTextField)) {
                ((JTextField)(JTextField)focusComponent).selectAll();
            }
        }
        source = destination = null;
    }
}
