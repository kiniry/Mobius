package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.net.*;
import java.util.*;
import java.io.*;
import java.util.*;
import javax.swing.plaf.*;
import javax.swing.text.*;
import javax.swing.event.*;
import javax.swing.text.html.*;
import javax.accessibility.*;

class JEditorPane$PlainEditorKit$PlainParagraph extends javax.swing.text.ParagraphView {
    
    JEditorPane$PlainEditorKit$PlainParagraph(Element elem) {
        super(elem);
        layoutPool = new JEditorPane$PlainEditorKit$PlainParagraph$LogicalView(elem);
        layoutPool.setParent(this);
    }
    
    protected void setPropertiesFromAttributes() {
        Component c = getContainer();
        if ((c != null) && (!c.getComponentOrientation().isLeftToRight())) {
            setJustification(StyleConstants.ALIGN_RIGHT);
        } else {
            setJustification(StyleConstants.ALIGN_LEFT);
        }
    }
    
    public int getFlowSpan(int index) {
        Component c = getContainer();
        if (c instanceof JTextArea) {
            JTextArea area = (JTextArea)(JTextArea)c;
            if (!area.getLineWrap()) {
                return Integer.MAX_VALUE;
            }
        }
        return super.getFlowSpan(index);
    }
    
    protected SizeRequirements calculateMinorAxisRequirements(int axis, SizeRequirements r) {
        SizeRequirements req = super.calculateMinorAxisRequirements(axis, r);
        Component c = getContainer();
        if (c instanceof JTextArea) {
            JTextArea area = (JTextArea)(JTextArea)c;
            if (!area.getLineWrap()) {
                req.minimum = req.preferred;
            }
        }
        return req;
    }
    {
    }
}
