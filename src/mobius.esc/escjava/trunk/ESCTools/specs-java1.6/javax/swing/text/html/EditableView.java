package javax.swing.text.html;

import java.awt.*;
import java.awt.event.*;
import java.io.*;
import javax.swing.text.*;
import javax.swing.*;
import javax.swing.border.*;
import javax.swing.event.*;
import java.util.*;

class EditableView extends ComponentView {
    
    EditableView(Element e) {
        super(e);
    }
    
    public float getMinimumSpan(int axis) {
        if (isVisible) {
            return super.getMinimumSpan(axis);
        }
        return 0;
    }
    
    public float getPreferredSpan(int axis) {
        if (isVisible) {
            return super.getPreferredSpan(axis);
        }
        return 0;
    }
    
    public float getMaximumSpan(int axis) {
        if (isVisible) {
            return super.getMaximumSpan(axis);
        }
        return 0;
    }
    
    public void paint(Graphics g, Shape allocation) {
        Component c = getComponent();
        Container host = getContainer();
        if (host != null && isVisible != ((JTextComponent)(JTextComponent)host).isEditable()) {
            isVisible = ((JTextComponent)(JTextComponent)host).isEditable();
            preferenceChanged(null, true, true);
            host.repaint();
        }
        if (isVisible) {
            super.paint(g, allocation);
        } else {
            setSize(0, 0);
        }
        if (c != null) {
            c.setFocusable(isVisible);
        }
    }
    
    public void setParent(View parent) {
        if (parent != null) {
            Container host = parent.getContainer();
            if (host != null) {
                isVisible = ((JTextComponent)(JTextComponent)host).isEditable();
            }
        }
        super.setParent(parent);
    }
    
    public boolean isVisible() {
        return isVisible;
    }
    private boolean isVisible;
}
