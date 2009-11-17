package javax.swing.text.html;

import java.awt.*;
import java.awt.event.*;
import java.io.*;
import javax.swing.text.*;
import javax.swing.*;
import javax.swing.border.*;
import javax.swing.event.*;
import java.util.*;
import javax.accessibility.*;
import java.lang.ref.*;

class HTMLEditorKit$HTMLFactory$BodyBlockView extends BlockView implements ComponentListener {
    
    public HTMLEditorKit$HTMLFactory$BodyBlockView(Element elem) {
        super(elem, View.Y_AXIS);
    }
    
    protected SizeRequirements calculateMajorAxisRequirements(int axis, SizeRequirements r) {
        r = super.calculateMajorAxisRequirements(axis, r);
        r.maximum = Integer.MAX_VALUE;
        return r;
    }
    
    protected void layoutMinorAxis(int targetSpan, int axis, int[] offsets, int[] spans) {
        Container container = getContainer();
        Container parentContainer;
        if (container != null && (container instanceof javax.swing.JEditorPane) && (parentContainer = container.getParent()) != null && (parentContainer instanceof javax.swing.JViewport)) {
            JViewport viewPort = (JViewport)(JViewport)parentContainer;
            Object cachedObject;
            if (cachedViewPort != null) {
                if ((cachedObject = cachedViewPort.get()) != null) {
                    if (cachedObject != viewPort) {
                        ((JComponent)(JComponent)cachedObject).removeComponentListener(this);
                    }
                } else {
                    cachedViewPort = null;
                }
            }
            if (cachedViewPort == null) {
                viewPort.addComponentListener(this);
                cachedViewPort = new WeakReference(viewPort);
            }
            componentVisibleWidth = viewPort.getExtentSize().width;
            if (componentVisibleWidth > 0) {
                Insets insets = container.getInsets();
                viewVisibleWidth = componentVisibleWidth - insets.left - getLeftInset();
                targetSpan = Math.min(targetSpan, viewVisibleWidth);
            }
        } else {
            if (cachedViewPort != null) {
                Object cachedObject;
                if ((cachedObject = cachedViewPort.get()) != null) {
                    ((JComponent)(JComponent)cachedObject).removeComponentListener(this);
                }
                cachedViewPort = null;
            }
        }
        super.layoutMinorAxis(targetSpan, axis, offsets, spans);
    }
    
    public void setParent(View parent) {
        if (parent == null) {
            if (cachedViewPort != null) {
                Object cachedObject;
                if ((cachedObject = cachedViewPort.get()) != null) {
                    ((JComponent)(JComponent)cachedObject).removeComponentListener(this);
                }
                cachedViewPort = null;
            }
        }
        super.setParent(parent);
    }
    
    public void componentResized(ComponentEvent e) {
        if (!(e.getSource() instanceof JViewport)) {
            return;
        }
        JViewport viewPort = (JViewport)(JViewport)e.getSource();
        if (componentVisibleWidth != viewPort.getExtentSize().width) {
            Document doc = getDocument();
            if (doc instanceof AbstractDocument) {
                AbstractDocument document = (AbstractDocument)(AbstractDocument)getDocument();
                document.readLock();
                try {
                    layoutChanged(X_AXIS);
                    preferenceChanged(null, true, true);
                } finally {
                    document.readUnlock();
                }
            }
        }
    }
    
    public void componentHidden(ComponentEvent e) {
    }
    
    public void componentMoved(ComponentEvent e) {
    }
    
    public void componentShown(ComponentEvent e) {
    }
    private Reference cachedViewPort = null;
    private boolean isListening = false;
    private int viewVisibleWidth = Integer.MAX_VALUE;
    private int componentVisibleWidth = Integer.MAX_VALUE;
}
