package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import javax.swing.event.*;

class StyledEditorKit$AttributeTracker implements CaretListener, PropertyChangeListener, Serializable {
    /*synthetic*/ final StyledEditorKit this$0;
    
    StyledEditorKit$AttributeTracker(/*synthetic*/ final StyledEditorKit this$0) {
        this.this$0 = this$0;
        
    }
    
    void updateInputAttributes(int dot, int mark, JTextComponent c) {
        Document aDoc = c.getDocument();
        if (!(aDoc instanceof StyledDocument)) {
            return;
        }
        int start = Math.min(dot, mark);
        StyledDocument doc = (StyledDocument)(StyledDocument)aDoc;
        Element run;
        this$0.currentParagraph = doc.getParagraphElement(start);
        if (this$0.currentParagraph.getStartOffset() == start || dot != mark) {
            run = doc.getCharacterElement(start);
        } else {
            run = doc.getCharacterElement(Math.max(start - 1, 0));
        }
        if (run != this$0.currentRun) {
            this$0.currentRun = run;
            this$0.createInputAttributes(this$0.currentRun, this$0.getInputAttributes());
        }
    }
    
    public void propertyChange(PropertyChangeEvent evt) {
        Object newValue = evt.getNewValue();
        Object source = evt.getSource();
        if ((source instanceof JTextComponent) && (newValue instanceof Document)) {
            updateInputAttributes(0, 0, (JTextComponent)(JTextComponent)source);
        }
    }
    
    public void caretUpdate(CaretEvent e) {
        updateInputAttributes(e.getDot(), e.getMark(), (JTextComponent)(JTextComponent)e.getSource());
    }
}
