package javax.swing.text.html;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.util.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.accessibility.*;

class AccessibleHTML implements Accessible {
    
    /*synthetic*/ static void access$1900(AccessibleHTML x0, Document x1) {
        x0.setDocument(x1);
    }
    
    /*synthetic*/ static AccessibleHTML$ElementInfo access$1700(AccessibleHTML x0) {
        return x0.getRootInfo();
    }
    
    /*synthetic*/ static Rectangle access$1600(AccessibleHTML x0) {
        return x0.getRootEditorRect();
    }
    
    /*synthetic*/ static void access$1500(AccessibleHTML x0, Object x1) {
        x0.unlock(x1);
    }
    
    /*synthetic*/ static View access$1400(AccessibleHTML x0) {
        return x0.getRootView();
    }
    
    /*synthetic*/ static Object access$1300(AccessibleHTML x0) {
        return x0.lock();
    }
    
    /*synthetic*/ static AccessibleHTML$ElementInfo access$500(AccessibleHTML x0) {
        return x0.rootElementInfo;
    }
    
    /*synthetic*/ static JEditorPane access$400(AccessibleHTML x0) {
        return x0.getTextComponent();
    }
    
    /*synthetic*/ static JEditorPane access$300(AccessibleHTML x0) {
        return x0.editor;
    }
    
    /*synthetic*/ static Document access$200(AccessibleHTML x0) {
        return x0.model;
    }
    {
    }
    private JEditorPane editor;
    private Document model;
    private DocumentListener docListener;
    private PropertyChangeListener propChangeListener;
    private AccessibleHTML$ElementInfo rootElementInfo;
    private AccessibleHTML$RootHTMLAccessibleContext rootHTMLAccessibleContext;
    
    public AccessibleHTML(JEditorPane pane) {
        
        editor = pane;
        propChangeListener = new AccessibleHTML$PropertyChangeHandler(this, null);
        setDocument(editor.getDocument());
        docListener = new AccessibleHTML$DocumentHandler(this, null);
    }
    
    private void setDocument(Document document) {
        if (model != null) {
            model.removeDocumentListener(docListener);
        }
        if (editor != null) {
            editor.removePropertyChangeListener(propChangeListener);
        }
        this.model = document;
        if (model != null) {
            if (rootElementInfo != null) {
                rootElementInfo.invalidate(false);
            }
            buildInfo();
            model.addDocumentListener(docListener);
        } else {
            rootElementInfo = null;
        }
        if (editor != null) {
            editor.addPropertyChangeListener(propChangeListener);
        }
    }
    
    private Document getDocument() {
        return model;
    }
    
    private JEditorPane getTextComponent() {
        return editor;
    }
    
    private AccessibleHTML$ElementInfo getRootInfo() {
        return rootElementInfo;
    }
    
    private View getRootView() {
        return getTextComponent().getUI().getRootView(getTextComponent());
    }
    
    private Rectangle getRootEditorRect() {
        Rectangle alloc = getTextComponent().getBounds();
        if ((alloc.width > 0) && (alloc.height > 0)) {
            alloc.x = alloc.y = 0;
            Insets insets = editor.getInsets();
            alloc.x += insets.left;
            alloc.y += insets.top;
            alloc.width -= insets.left + insets.right;
            alloc.height -= insets.top + insets.bottom;
            return alloc;
        }
        return null;
    }
    
    private Object lock() {
        Document document = getDocument();
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
    
    private void buildInfo() {
        Object lock = lock();
        try {
            Document doc = getDocument();
            Element root = doc.getDefaultRootElement();
            rootElementInfo = new AccessibleHTML$ElementInfo(this, root);
            rootElementInfo.validate();
        } finally {
            unlock(lock);
        }
    }
    
    AccessibleHTML$ElementInfo createElementInfo(Element e, AccessibleHTML$ElementInfo parent) {
        AttributeSet attrs = e.getAttributes();
        if (attrs != null) {
            Object name = attrs.getAttribute(StyleConstants.NameAttribute);
            if (name == HTML$Tag.IMG) {
                return new AccessibleHTML$IconElementInfo(this, e, parent);
            } else if (name == HTML$Tag.CONTENT || name == HTML$Tag.CAPTION) {
                return new AccessibleHTML$TextElementInfo(this, e, parent);
            } else if (name == HTML$Tag.TABLE) {
                return new AccessibleHTML$TableElementInfo(this, e, parent);
            }
        }
        return null;
    }
    
    public AccessibleContext getAccessibleContext() {
        if (rootHTMLAccessibleContext == null) {
            rootHTMLAccessibleContext = new AccessibleHTML$RootHTMLAccessibleContext(this, rootElementInfo);
        }
        return rootHTMLAccessibleContext;
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
