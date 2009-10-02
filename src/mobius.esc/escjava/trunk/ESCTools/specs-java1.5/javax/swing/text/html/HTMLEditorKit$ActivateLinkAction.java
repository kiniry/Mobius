package javax.swing.text.html;

import java.awt.*;
import java.awt.event.*;
import java.io.*;
import java.net.MalformedURLException;
import java.net.URL;
import javax.swing.text.*;
import javax.swing.*;
import javax.swing.border.*;
import javax.swing.event.*;
import java.util.*;
import javax.accessibility.*;
import java.lang.ref.*;

class HTMLEditorKit$ActivateLinkAction extends TextAction {
    
    public HTMLEditorKit$ActivateLinkAction(String actionName) {
        super(actionName);
    }
    
    private void activateLink(String href, HTMLDocument doc, JEditorPane editor, int offset) {
        try {
            URL page = (URL)(URL)doc.getProperty(Document.StreamDescriptionProperty);
            URL url = new URL(page, href);
            HyperlinkEvent linkEvent = new HyperlinkEvent(editor, HyperlinkEvent$EventType.ACTIVATED, url, url.toExternalForm(), doc.getCharacterElement(offset));
            editor.fireHyperlinkUpdate(linkEvent);
        } catch (MalformedURLException m) {
        }
    }
    
    private void doObjectAction(JEditorPane editor, Element elem) {
        View view = getView(editor, elem);
        if (view != null && view instanceof ObjectView) {
            Component comp = ((ObjectView)(ObjectView)view).getComponent();
            if (comp != null && comp instanceof Accessible) {
                AccessibleContext ac = ((Accessible)(Accessible)comp).getAccessibleContext();
                if (ac != null) {
                    AccessibleAction aa = ac.getAccessibleAction();
                    if (aa != null) {
                        aa.doAccessibleAction(0);
                    }
                }
            }
        }
    }
    
    private View getRootView(JEditorPane editor) {
        return editor.getUI().getRootView(editor);
    }
    
    private View getView(JEditorPane editor, Element elem) {
        Object lock = lock(editor);
        try {
            View rootView = getRootView(editor);
            int start = elem.getStartOffset();
            if (rootView != null) {
                return getView(rootView, elem, start);
            }
            return null;
        } finally {
            unlock(lock);
        }
    }
    
    private View getView(View parent, Element elem, int start) {
        if (parent.getElement() == elem) {
            return parent;
        }
        int index = parent.getViewIndex(start, Position$Bias.Forward);
        if (index != -1 && index < parent.getViewCount()) {
            return getView(parent.getView(index), elem, start);
        }
        return null;
    }
    
    private Object lock(JEditorPane editor) {
        Document document = editor.getDocument();
        if (document instanceof AbstractDocument) {
            ((AbstractDocument)(AbstractDocument)document).readLock();
            return document;
        }
        return null;
    }
    
    private void unlock(Object key) {
        if (key != null) {
            ((AbstractDocument)(AbstractDocument)key).readUnlock();
        }
    }
    
    public void actionPerformed(ActionEvent e) {
        JTextComponent c = getTextComponent(e);
        if (c.isEditable() || !(c instanceof JEditorPane)) {
            return;
        }
        JEditorPane editor = (JEditorPane)(JEditorPane)c;
        Document d = editor.getDocument();
        if (d == null || !(d instanceof HTMLDocument)) {
            return;
        }
        HTMLDocument doc = (HTMLDocument)(HTMLDocument)d;
        ElementIterator ei = new ElementIterator(doc);
        int currentOffset = editor.getCaretPosition();
        String urlString = null;
        String objString = null;
        Element currentElement = null;
        while ((currentElement = ei.next()) != null) {
            String name = currentElement.getName();
            AttributeSet attr = currentElement.getAttributes();
            Object href = HTMLEditorKit.access$000(attr, HTML$Attribute.HREF);
            if (href != null) {
                if (currentOffset >= currentElement.getStartOffset() && currentOffset <= currentElement.getEndOffset()) {
                    activateLink((String)(String)href, doc, editor, currentOffset);
                    return;
                }
            } else if (name.equals(HTML$Tag.OBJECT.toString())) {
                Object obj = HTMLEditorKit.access$000(attr, HTML$Attribute.CLASSID);
                if (obj != null) {
                    if (currentOffset >= currentElement.getStartOffset() && currentOffset <= currentElement.getEndOffset()) {
                        doObjectAction(editor, currentElement);
                        return;
                    }
                }
            }
        }
    }
}
