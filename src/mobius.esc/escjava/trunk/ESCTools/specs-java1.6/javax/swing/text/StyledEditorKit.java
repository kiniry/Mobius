package javax.swing.text;

import java.io.*;
import java.awt.*;
import javax.swing.event.*;
import javax.swing.Action;
import javax.swing.JEditorPane;

public class StyledEditorKit extends DefaultEditorKit {
    
    public StyledEditorKit() {
        
        createInputAttributeUpdated();
        createInputAttributes();
    }
    
    public MutableAttributeSet getInputAttributes() {
        return inputAttributes;
    }
    
    public Element getCharacterAttributeRun() {
        return currentRun;
    }
    
    public Action[] getActions() {
        return TextAction.augmentList(super.getActions(), this.defaultActions);
    }
    
    public Document createDefaultDocument() {
        return new DefaultStyledDocument();
    }
    
    public void install(JEditorPane c) {
        c.addCaretListener(inputAttributeUpdater);
        c.addPropertyChangeListener(inputAttributeUpdater);
        Caret caret = c.getCaret();
        if (caret != null) {
            inputAttributeUpdater.updateInputAttributes(caret.getDot(), caret.getMark(), c);
        }
    }
    
    public void deinstall(JEditorPane c) {
        c.removeCaretListener(inputAttributeUpdater);
        c.removePropertyChangeListener(inputAttributeUpdater);
        currentRun = null;
        currentParagraph = null;
    }
    
    public ViewFactory getViewFactory() {
        return defaultFactory;
    }
    
    public Object clone() {
        StyledEditorKit o = (StyledEditorKit)(StyledEditorKit)super.clone();
        o.currentRun = o.currentParagraph = null;
        o.createInputAttributeUpdated();
        o.createInputAttributes();
        return o;
    }
    
    private void createInputAttributes() {
        inputAttributes = new StyledEditorKit$1(this);
    }
    
    private void createInputAttributeUpdated() {
        inputAttributeUpdater = new StyledEditorKit$AttributeTracker(this);
    }
    private static final ViewFactory defaultFactory = new StyledEditorKit$StyledViewFactory();
    Element currentRun;
    Element currentParagraph;
    MutableAttributeSet inputAttributes;
    private StyledEditorKit$AttributeTracker inputAttributeUpdater;
    {
    }
    
    protected void createInputAttributes(Element element, MutableAttributeSet set) {
        if (element.getAttributes().getAttributeCount() > 0 || element.getEndOffset() - element.getStartOffset() > 1 || element.getEndOffset() < element.getDocument().getLength()) {
            set.removeAttributes(set);
            set.addAttributes(element.getAttributes());
            set.removeAttribute(StyleConstants.ComponentAttribute);
            set.removeAttribute(StyleConstants.IconAttribute);
            set.removeAttribute(AbstractDocument.ElementNameAttribute);
            set.removeAttribute(StyleConstants.ComposedTextAttribute);
        }
    }
    {
    }
    private static final Action[] defaultActions = {new StyledEditorKit$FontFamilyAction("font-family-SansSerif", "SansSerif"), new StyledEditorKit$FontFamilyAction("font-family-Monospaced", "Monospaced"), new StyledEditorKit$FontFamilyAction("font-family-Serif", "Serif"), new StyledEditorKit$FontSizeAction("font-size-8", 8), new StyledEditorKit$FontSizeAction("font-size-10", 10), new StyledEditorKit$FontSizeAction("font-size-12", 12), new StyledEditorKit$FontSizeAction("font-size-14", 14), new StyledEditorKit$FontSizeAction("font-size-16", 16), new StyledEditorKit$FontSizeAction("font-size-18", 18), new StyledEditorKit$FontSizeAction("font-size-24", 24), new StyledEditorKit$FontSizeAction("font-size-36", 36), new StyledEditorKit$FontSizeAction("font-size-48", 48), new StyledEditorKit$AlignmentAction("left-justify", StyleConstants.ALIGN_LEFT), new StyledEditorKit$AlignmentAction("center-justify", StyleConstants.ALIGN_CENTER), new StyledEditorKit$AlignmentAction("right-justify", StyleConstants.ALIGN_RIGHT), new StyledEditorKit$BoldAction(), new StyledEditorKit$ItalicAction(), new StyledEditorKit$StyledInsertBreakAction(), new StyledEditorKit$UnderlineAction()};
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
}
