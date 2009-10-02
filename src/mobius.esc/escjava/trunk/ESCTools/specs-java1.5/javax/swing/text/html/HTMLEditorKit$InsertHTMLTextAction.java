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

public class HTMLEditorKit$InsertHTMLTextAction extends HTMLEditorKit$HTMLTextAction {
    
    public HTMLEditorKit$InsertHTMLTextAction(String name, String html, HTML$Tag parentTag, HTML$Tag addTag) {
        this(name, html, parentTag, addTag, null, null);
    }
    
    public HTMLEditorKit$InsertHTMLTextAction(String name, String html, HTML$Tag parentTag, HTML$Tag addTag, HTML$Tag alternateParentTag, HTML$Tag alternateAddTag) {
        this(name, html, parentTag, addTag, alternateParentTag, alternateAddTag, true);
    }
    
    HTMLEditorKit$InsertHTMLTextAction(String name, String html, HTML$Tag parentTag, HTML$Tag addTag, HTML$Tag alternateParentTag, HTML$Tag alternateAddTag, boolean adjustSelection) {
        super(name);
        this.html = html;
        this.parentTag = parentTag;
        this.addTag = addTag;
        this.alternateParentTag = alternateParentTag;
        this.alternateAddTag = alternateAddTag;
        this.adjustSelection = adjustSelection;
    }
    
    protected void insertHTML(JEditorPane editor, HTMLDocument doc, int offset, String html, int popDepth, int pushDepth, HTML$Tag addTag) {
        try {
            getHTMLEditorKit(editor).insertHTML(doc, offset, html, popDepth, pushDepth, addTag);
        } catch (IOException ioe) {
            throw new RuntimeException("Unable to insert: " + ioe);
        } catch (BadLocationException ble) {
            throw new RuntimeException("Unable to insert: " + ble);
        }
    }
    
    protected void insertAtBoundary(JEditorPane editor, HTMLDocument doc, int offset, Element insertElement, String html, HTML$Tag parentTag, HTML$Tag addTag) {
        insertAtBoundry(editor, doc, offset, insertElement, html, parentTag, addTag);
    }
    
    
    protected void insertAtBoundry(JEditorPane editor, HTMLDocument doc, int offset, Element insertElement, String html, HTML$Tag parentTag, HTML$Tag addTag) {
        Element e;
        Element commonParent;
        boolean isFirst = (offset == 0);
        if (offset > 0 || insertElement == null) {
            e = doc.getDefaultRootElement();
            while (e != null && e.getStartOffset() != offset && !e.isLeaf()) {
                e = e.getElement(e.getElementIndex(offset));
            }
            commonParent = (e != null) ? e.getParentElement() : null;
        } else {
            commonParent = insertElement;
        }
        if (commonParent != null) {
            int pops = 0;
            int pushes = 0;
            if (isFirst && insertElement != null) {
                e = commonParent;
                while (e != null && !e.isLeaf()) {
                    e = e.getElement(e.getElementIndex(offset));
                    pops++;
                }
            } else {
                e = commonParent;
                offset--;
                while (e != null && !e.isLeaf()) {
                    e = e.getElement(e.getElementIndex(offset));
                    pops++;
                }
                e = commonParent;
                offset++;
                while (e != null && e != insertElement) {
                    e = e.getElement(e.getElementIndex(offset));
                    pushes++;
                }
            }
            pops = Math.max(0, pops - 1);
            insertHTML(editor, doc, offset, html, pops, pushes, addTag);
        }
    }
    
    boolean insertIntoTag(JEditorPane editor, HTMLDocument doc, int offset, HTML$Tag tag, HTML$Tag addTag) {
        Element e = findElementMatchingTag(doc, offset, tag);
        if (e != null && e.getStartOffset() == offset) {
            insertAtBoundary(editor, doc, offset, e, html, tag, addTag);
            return true;
        } else if (offset > 0) {
            int depth = elementCountToTag(doc, offset - 1, tag);
            if (depth != -1) {
                insertHTML(editor, doc, offset, html, depth, 0, addTag);
                return true;
            }
        }
        return false;
    }
    
    void adjustSelection(JEditorPane pane, HTMLDocument doc, int startOffset, int oldLength) {
        int newLength = doc.getLength();
        if (newLength != oldLength && startOffset < newLength) {
            if (startOffset > 0) {
                String text;
                try {
                    text = doc.getText(startOffset - 1, 1);
                } catch (BadLocationException ble) {
                    text = null;
                }
                if (text != null && text.length() > 0 && text.charAt(0) == '\n') {
                    pane.select(startOffset, startOffset);
                } else {
                    pane.select(startOffset + 1, startOffset + 1);
                }
            } else {
                pane.select(1, 1);
            }
        }
    }
    
    public void actionPerformed(ActionEvent ae) {
        JEditorPane editor = getEditor(ae);
        if (editor != null) {
            HTMLDocument doc = getHTMLDocument(editor);
            int offset = editor.getSelectionStart();
            int length = doc.getLength();
            boolean inserted;
            if (!insertIntoTag(editor, doc, offset, parentTag, addTag) && alternateParentTag != null) {
                inserted = insertIntoTag(editor, doc, offset, alternateParentTag, alternateAddTag);
            } else {
                inserted = true;
            }
            if (adjustSelection && inserted) {
                adjustSelection(editor, doc, offset, length);
            }
        }
    }
    protected String html;
    protected HTML$Tag parentTag;
    protected HTML$Tag addTag;
    protected HTML$Tag alternateParentTag;
    protected HTML$Tag alternateAddTag;
    boolean adjustSelection;
}
