package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.datatransfer.*;
import java.text.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;
import sun.awt.AppContext;

class JTextComponent$MutableCaretEvent extends CaretEvent implements ChangeListener, FocusListener, MouseListener {
    
    JTextComponent$MutableCaretEvent(JTextComponent c) {
        super(c);
    }
    
    final void fire() {
        JTextComponent c = (JTextComponent)(JTextComponent)getSource();
        if (c != null) {
            Caret caret = c.getCaret();
            dot = caret.getDot();
            mark = caret.getMark();
            c.fireCaretUpdate(this);
        }
    }
    
    public final String toString() {
        return "dot=" + dot + "," + "mark=" + mark;
    }
    
    public final int getDot() {
        return dot;
    }
    
    public final int getMark() {
        return mark;
    }
    
    public final void stateChanged(ChangeEvent e) {
        if (!dragActive) {
            fire();
        }
    }
    
    public void focusGained(FocusEvent fe) {
        AppContext.getAppContext().put(JTextComponent.access$500(), fe.getSource());
    }
    
    public void focusLost(FocusEvent fe) {
    }
    
    public final void mousePressed(MouseEvent e) {
        dragActive = true;
    }
    
    public final void mouseReleased(MouseEvent e) {
        dragActive = false;
        fire();
    }
    
    public final void mouseClicked(MouseEvent e) {
    }
    
    public final void mouseEntered(MouseEvent e) {
    }
    
    public final void mouseExited(MouseEvent e) {
    }
    private boolean dragActive;
    private int dot;
    private int mark;
}
