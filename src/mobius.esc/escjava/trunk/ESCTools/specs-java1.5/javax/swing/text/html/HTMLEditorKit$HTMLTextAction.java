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

public abstract class HTMLEditorKit$HTMLTextAction extends StyledEditorKit$StyledTextAction {
    
    public HTMLEditorKit$HTMLTextAction(String name) {
        super(name);
    }
    
    protected HTMLDocument getHTMLDocument(JEditorPane e) {
        Document d = e.getDocument();
        if (d instanceof HTMLDocument) {
            return (HTMLDocument)(HTMLDocument)d;
        }
        throw new IllegalArgumentException("document must be HTMLDocument");
    }
    
    protected HTMLEditorKit getHTMLEditorKit(JEditorPane e) {
        EditorKit k = e.getEditorKit();
        if (k instanceof HTMLEditorKit) {
            return (HTMLEditorKit)(HTMLEditorKit)k;
        }
        throw new IllegalArgumentException("EditorKit must be HTMLEditorKit");
    }
    
    protected Element[] getElementsAt(HTMLDocument doc, int offset) {
        return getElementsAt(doc.getDefaultRootElement(), offset, 0);
    }
    
    private Element[] getElementsAt(Element parent, int offset, int depth) {
        if (parent.isLeaf()) {
            Element[] retValue = new Element[depth + 1];
            retValue[depth] = parent;
            return retValue;
        }
        Element[] retValue = getElementsAt(parent.getElement(parent.getElementIndex(offset)), offset, depth + 1);
        retValue[depth] = parent;
        return retValue;
    }
    
    protected int elementCountToTag(HTMLDocument doc, int offset, HTML$Tag tag) {
        int depth = -1;
        Element e = doc.getCharacterElement(offset);
        while (e != null && e.getAttributes().getAttribute(StyleConstants.NameAttribute) != tag) {
            e = e.getParentElement();
            depth++;
        }
        if (e == null) {
            return -1;
        }
        return depth;
    }
    
    protected Element findElementMatchingTag(HTMLDocument doc, int offset, HTML$Tag tag) {
        Element e = doc.getDefaultRootElement();
        Element lastMatch = null;
        while (e != null) {
            if (e.getAttributes().getAttribute(StyleConstants.NameAttribute) == tag) {
                lastMatch = e;
            }
            e = e.getElement(e.getElementIndex(offset));
        }
        return lastMatch;
    }
}
