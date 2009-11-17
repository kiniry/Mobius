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

class HTMLEditorKit$NavigateLinkAction extends TextAction implements CaretListener {
    private static int prevHypertextOffset = -1;
    private static boolean foundLink = false;
    private HTMLEditorKit$NavigateLinkAction$FocusHighlightPainter focusPainter = new HTMLEditorKit$NavigateLinkAction$FocusHighlightPainter(this, null);
    private Object selectionTag;
    private boolean focusBack = false;
    
    public HTMLEditorKit$NavigateLinkAction(String actionName) {
        super(actionName);
        if ("previous-link-action".equals(actionName)) {
            focusBack = true;
        }
    }
    
    public void caretUpdate(CaretEvent e) {
        if (foundLink) {
            foundLink = false;
            Object src = e.getSource();
            if (src instanceof JTextComponent) {
                ((JTextComponent)(JTextComponent)src).getAccessibleContext().firePropertyChange(AccessibleContext.ACCESSIBLE_HYPERTEXT_OFFSET, new Integer(prevHypertextOffset), new Integer(e.getDot()));
            }
        }
    }
    
    public void actionPerformed(ActionEvent e) {
        JTextComponent comp = getTextComponent(e);
        if (comp == null || comp.isEditable()) {
            return;
        }
        Document doc = comp.getDocument();
        if (doc == null) {
            return;
        }
        ElementIterator ei = new ElementIterator(doc);
        int currentOffset = comp.getCaretPosition();
        int prevStartOffset = -1;
        int prevEndOffset = -1;
        Element nextElement = null;
        while ((nextElement = ei.next()) != null) {
            String name = nextElement.getName();
            AttributeSet attr = nextElement.getAttributes();
            Object href = HTMLEditorKit.access$000(attr, HTML$Attribute.HREF);
            if (!(name.equals(HTML$Tag.OBJECT.toString())) && href == null) {
                continue;
            }
            int elementOffset = nextElement.getStartOffset();
            if (focusBack) {
                if (elementOffset >= currentOffset && prevStartOffset >= 0) {
                    foundLink = true;
                    comp.setCaretPosition(prevStartOffset);
                    moveCaretPosition(comp, prevStartOffset, prevEndOffset);
                    prevHypertextOffset = prevStartOffset;
                    return;
                }
            } else {
                if (elementOffset > currentOffset) {
                    foundLink = true;
                    comp.setCaretPosition(elementOffset);
                    moveCaretPosition(comp, elementOffset, nextElement.getEndOffset());
                    prevHypertextOffset = elementOffset;
                    return;
                }
            }
            prevStartOffset = nextElement.getStartOffset();
            prevEndOffset = nextElement.getEndOffset();
        }
        if (focusBack && prevStartOffset >= 0) {
            foundLink = true;
            comp.setCaretPosition(prevStartOffset);
            moveCaretPosition(comp, prevStartOffset, prevEndOffset);
            prevHypertextOffset = prevStartOffset;
            return;
        }
    }
    
    private void moveCaretPosition(JTextComponent comp, int mark, int dot) {
        Highlighter h = comp.getHighlighter();
        if (h != null) {
            int p0 = Math.min(dot, mark);
            int p1 = Math.max(dot, mark);
            try {
                if (selectionTag != null) {
                    h.changeHighlight(selectionTag, p0, p1);
                } else {
                    Highlighter$HighlightPainter p = focusPainter;
                    selectionTag = h.addHighlight(p0, p1, p);
                }
            } catch (BadLocationException e) {
            }
        }
    }
    {
    }
}
