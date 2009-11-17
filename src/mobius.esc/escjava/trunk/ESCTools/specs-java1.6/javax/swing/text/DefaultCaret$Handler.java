package javax.swing.text;

import java.awt.*;
import java.awt.event.*;
import java.awt.datatransfer.*;
import java.beans.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;

class DefaultCaret$Handler implements PropertyChangeListener, DocumentListener, ActionListener, ClipboardOwner {
    /*synthetic*/ final DefaultCaret this$0;
    
    DefaultCaret$Handler(/*synthetic*/ final DefaultCaret this$0) {
        this.this$0 = this$0;
        
    }
    
    public void actionPerformed(ActionEvent e) {
        if (this$0.width == 0 || this$0.height == 0) {
            if (this$0.component != null) {
                TextUI mapper = this$0.component.getUI();
                try {
                    Rectangle r = mapper.modelToView(this$0.component, this$0.dot, this$0.dotBias);
                    if (r != null && r.width != 0 && r.height != 0) {
                        this$0.damage(r);
                    }
                } catch (BadLocationException ble) {
                }
            }
        }
        this$0.visible = !this$0.visible;
        this$0.repaint();
    }
    
    public void insertUpdate(DocumentEvent e) {
        if (this$0.getUpdatePolicy() == 1 || (this$0.getUpdatePolicy() == 0 && !SwingUtilities.isEventDispatchThread())) {
            if ((e.getOffset() <= this$0.dot || e.getOffset() <= this$0.mark) && this$0.selectionTag != null) {
                try {
                    this$0.component.getHighlighter().changeHighlight(this$0.selectionTag, Math.min(this$0.dot, this$0.mark), Math.max(this$0.dot, this$0.mark));
                } catch (BadLocationException e1) {
                    e1.printStackTrace();
                }
            }
            return;
        }
        int adjust = 0;
        int offset = e.getOffset();
        int length = e.getLength();
        int newDot = this$0.dot;
        short changed = 0;
        if (e instanceof AbstractDocument$UndoRedoDocumentEvent) {
            this$0.setDot(offset + length);
            return;
        }
        if (newDot >= offset) {
            newDot += length;
            changed |= 1;
        }
        int newMark = this$0.mark;
        if (newMark >= offset) {
            newMark += length;
            changed |= 2;
        }
        if (changed != 0) {
            Position$Bias dotBias = this$0.dotBias;
            if (this$0.dot == offset) {
                Document doc = this$0.component.getDocument();
                boolean isNewline;
                try {
                    Segment s = new Segment();
                    doc.getText(newDot - 1, 1, s);
                    isNewline = (s.count > 0 && s.array[s.offset] == '\n');
                } catch (BadLocationException ble) {
                    isNewline = false;
                }
                if (isNewline) {
                    dotBias = Position$Bias.Forward;
                } else {
                    dotBias = Position$Bias.Backward;
                }
            }
            if (newMark == newDot) {
                this$0.setDot(newDot, dotBias);
                DefaultCaret.access$100(this$0);
            } else {
                this$0.setDot(newMark, this$0.markBias);
                if (this$0.getDot() == newMark) {
                    this$0.moveDot(newDot, dotBias);
                }
                DefaultCaret.access$100(this$0);
            }
        }
    }
    
    public void removeUpdate(DocumentEvent e) {
        if (this$0.getUpdatePolicy() == 1 || (this$0.getUpdatePolicy() == 0 && !SwingUtilities.isEventDispatchThread())) {
            int length = this$0.component.getDocument().getLength();
            this$0.dot = Math.min(this$0.dot, length);
            this$0.mark = Math.min(this$0.mark, length);
            if ((e.getOffset() < this$0.dot || e.getOffset() < this$0.mark) && this$0.selectionTag != null) {
                try {
                    this$0.component.getHighlighter().changeHighlight(this$0.selectionTag, Math.min(this$0.dot, this$0.mark), Math.max(this$0.dot, this$0.mark));
                } catch (BadLocationException e1) {
                    e1.printStackTrace();
                }
            }
            return;
        }
        int offs0 = e.getOffset();
        int offs1 = offs0 + e.getLength();
        int adjust = 0;
        int newDot = this$0.dot;
        boolean adjustDotBias = false;
        int newMark = this$0.mark;
        boolean adjustMarkBias = false;
        if (e instanceof AbstractDocument$UndoRedoDocumentEvent) {
            this$0.setDot(offs0);
            return;
        }
        if (newDot >= offs1) {
            newDot -= (offs1 - offs0);
            if (newDot == offs1) {
                adjustDotBias = true;
            }
        } else if (newDot >= offs0) {
            newDot = offs0;
            adjustDotBias = true;
        }
        if (newMark >= offs1) {
            newMark -= (offs1 - offs0);
            if (newMark == offs1) {
                adjustMarkBias = true;
            }
        } else if (newMark >= offs0) {
            newMark = offs0;
            adjustMarkBias = true;
        }
        if (newMark == newDot) {
            DefaultCaret.access$202(this$0, true);
            try {
                this$0.setDot(newDot, this$0.guessBiasForOffset(newDot, this$0.dotBias, this$0.dotLTR));
            } finally {
                DefaultCaret.access$202(this$0, false);
            }
            DefaultCaret.access$100(this$0);
        } else {
            Position$Bias dotBias = this$0.dotBias;
            Position$Bias markBias = this$0.markBias;
            if (adjustDotBias) {
                dotBias = this$0.guessBiasForOffset(newDot, dotBias, this$0.dotLTR);
            }
            if (adjustMarkBias) {
                markBias = this$0.guessBiasForOffset(this$0.mark, markBias, this$0.markLTR);
            }
            this$0.setDot(newMark, markBias);
            if (this$0.getDot() == newMark) {
                this$0.moveDot(newDot, dotBias);
            }
            DefaultCaret.access$100(this$0);
        }
    }
    
    public void changedUpdate(DocumentEvent e) {
        if (this$0.getUpdatePolicy() == 1 || (this$0.getUpdatePolicy() == 0 && !SwingUtilities.isEventDispatchThread())) {
            return;
        }
        if (e instanceof AbstractDocument$UndoRedoDocumentEvent) {
            this$0.setDot(e.getOffset() + e.getLength());
        }
    }
    
    public void propertyChange(PropertyChangeEvent evt) {
        Object oldValue = evt.getOldValue();
        Object newValue = evt.getNewValue();
        if ((oldValue instanceof Document) || (newValue instanceof Document)) {
            this$0.setDot(0);
            if (oldValue != null) {
                ((Document)(Document)oldValue).removeDocumentListener(this);
            }
            if (newValue != null) {
                ((Document)(Document)newValue).addDocumentListener(this);
            }
        } else if ("enabled".equals(evt.getPropertyName())) {
            Boolean enabled = (Boolean)(Boolean)evt.getNewValue();
            if (this$0.component.isFocusOwner()) {
                if (enabled == Boolean.TRUE) {
                    if (this$0.component.isEditable()) {
                        this$0.setVisible(true);
                    }
                    this$0.setSelectionVisible(true);
                } else {
                    this$0.setVisible(false);
                    this$0.setSelectionVisible(false);
                }
            }
        } else if ("caretWidth".equals(evt.getPropertyName())) {
            Integer newWidth = (Integer)(Integer)evt.getNewValue();
            if (newWidth != null) {
                DefaultCaret.access$302(this$0, newWidth.intValue());
            } else {
                DefaultCaret.access$302(this$0, -1);
            }
            this$0.repaint();
        } else if ("caretAspectRatio".equals(evt.getPropertyName())) {
            Number newRatio = (Number)(Number)evt.getNewValue();
            if (newRatio != null) {
                DefaultCaret.access$402(this$0, newRatio.floatValue());
            } else {
                DefaultCaret.access$402(this$0, -1);
            }
            this$0.repaint();
        }
    }
    
    public void lostOwnership(Clipboard clipboard, Transferable contents) {
        if (DefaultCaret.access$500(this$0)) {
            DefaultCaret.access$502(this$0, false);
            if (this$0.component != null && !this$0.component.hasFocus()) {
                this$0.setSelectionVisible(false);
            }
        }
    }
}
