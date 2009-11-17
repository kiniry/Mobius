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
import javax.swing.plaf.TextUI;
import java.util.*;
import javax.accessibility.*;
import java.lang.ref.*;

public class HTMLEditorKit$LinkController extends MouseAdapter implements MouseMotionListener, Serializable {
    
    public HTMLEditorKit$LinkController() {
        
    }
    private Element curElem = null;
    private boolean curElemImage = false;
    private String href = null;
    private Position$Bias[] bias = new Position$Bias[1];
    private int curOffset;
    
    public void mouseClicked(MouseEvent e) {
        JEditorPane editor = (JEditorPane)(JEditorPane)e.getSource();
        if (!editor.isEditable() && SwingUtilities.isLeftMouseButton(e)) {
            Point pt = new Point(e.getX(), e.getY());
            int pos = editor.viewToModel(pt);
            if (pos >= 0) {
                activateLink(pos, editor, e.getX(), e.getY());
            }
        }
    }
    
    public void mouseDragged(MouseEvent e) {
    }
    
    public void mouseMoved(MouseEvent e) {
        JEditorPane editor = (JEditorPane)(JEditorPane)e.getSource();
        HTMLEditorKit kit = (HTMLEditorKit)(HTMLEditorKit)editor.getEditorKit();
        boolean adjustCursor = true;
        Cursor newCursor = kit.getDefaultCursor();
        if (!editor.isEditable()) {
            Point pt = new Point(e.getX(), e.getY());
            int pos = editor.getUI().viewToModel(editor, pt, bias);
            if (bias[0] == Position$Bias.Backward && pos > 0) {
                pos--;
            }
            if (pos >= 0 && (editor.getDocument() instanceof HTMLDocument)) {
                HTMLDocument hdoc = (HTMLDocument)(HTMLDocument)editor.getDocument();
                Element elem = hdoc.getCharacterElement(pos);
                if (!doesElementContainLocation(editor, elem, pos, e.getX(), e.getY())) {
                    elem = null;
                }
                if (curElem != elem || curElemImage) {
                    Element lastElem = curElem;
                    curElem = elem;
                    String href = null;
                    curElemImage = false;
                    if (elem != null) {
                        AttributeSet a = elem.getAttributes();
                        AttributeSet anchor = (AttributeSet)(AttributeSet)a.getAttribute(HTML$Tag.A);
                        if (anchor == null) {
                            curElemImage = (a.getAttribute(StyleConstants.NameAttribute) == HTML$Tag.IMG);
                            if (curElemImage) {
                                href = getMapHREF(editor, hdoc, elem, a, pos, e.getX(), e.getY());
                            }
                        } else {
                            href = (String)(String)anchor.getAttribute(HTML$Attribute.HREF);
                        }
                    }
                    if (href != this.href) {
                        fireEvents(editor, hdoc, href, lastElem);
                        this.href = href;
                        if (href != null) {
                            newCursor = kit.getLinkCursor();
                        }
                    } else {
                        adjustCursor = false;
                    }
                } else {
                    adjustCursor = false;
                }
                curOffset = pos;
            }
        }
        if (adjustCursor && editor.getCursor() != newCursor) {
            editor.setCursor(newCursor);
        }
    }
    
    private String getMapHREF(JEditorPane html, HTMLDocument hdoc, Element elem, AttributeSet attr, int offset, int x, int y) {
        Object useMap = attr.getAttribute(HTML$Attribute.USEMAP);
        if (useMap != null && (useMap instanceof String)) {
            Map m = hdoc.getMap((String)(String)useMap);
            if (m != null && offset < hdoc.getLength()) {
                Rectangle bounds;
                TextUI ui = html.getUI();
                try {
                    Shape lBounds = ui.modelToView(html, offset, Position$Bias.Forward);
                    Shape rBounds = ui.modelToView(html, offset + 1, Position$Bias.Backward);
                    bounds = lBounds.getBounds();
                    bounds.add((rBounds instanceof Rectangle) ? (Rectangle)(Rectangle)rBounds : rBounds.getBounds());
                } catch (BadLocationException ble) {
                    bounds = null;
                }
                if (bounds != null) {
                    AttributeSet area = m.getArea(x - bounds.x, y - bounds.y, bounds.width, bounds.height);
                    if (area != null) {
                        return (String)(String)area.getAttribute(HTML$Attribute.HREF);
                    }
                }
            }
        }
        return null;
    }
    
    private boolean doesElementContainLocation(JEditorPane editor, Element e, int offset, int x, int y) {
        if (e != null && offset > 0 && e.getStartOffset() == offset) {
            try {
                TextUI ui = editor.getUI();
                Shape s1 = ui.modelToView(editor, offset, Position$Bias.Forward);
                if (s1 == null) {
                    return false;
                }
                Rectangle r1 = (s1 instanceof Rectangle) ? (Rectangle)(Rectangle)s1 : s1.getBounds();
                Shape s2 = ui.modelToView(editor, e.getEndOffset(), Position$Bias.Backward);
                if (s2 != null) {
                    Rectangle r2 = (s2 instanceof Rectangle) ? (Rectangle)(Rectangle)s2 : s2.getBounds();
                    r1.add(r2);
                }
                return r1.contains(x, y);
            } catch (BadLocationException ble) {
            }
        }
        return true;
    }
    
    protected void activateLink(int pos, JEditorPane editor) {
        activateLink(pos, editor, -1, -1);
    }
    
    void activateLink(int pos, JEditorPane html, int x, int y) {
        Document doc = html.getDocument();
        if (doc instanceof HTMLDocument) {
            HTMLDocument hdoc = (HTMLDocument)(HTMLDocument)doc;
            Element e = hdoc.getCharacterElement(pos);
            AttributeSet a = e.getAttributes();
            AttributeSet anchor = (AttributeSet)(AttributeSet)a.getAttribute(HTML$Tag.A);
            HyperlinkEvent linkEvent = null;
            String description;
            if (anchor == null) {
                href = getMapHREF(html, hdoc, e, a, pos, x, y);
            } else {
                href = (String)(String)anchor.getAttribute(HTML$Attribute.HREF);
            }
            if (href != null) {
                linkEvent = createHyperlinkEvent(html, hdoc, href, anchor, e);
            }
            if (linkEvent != null) {
                html.fireHyperlinkUpdate(linkEvent);
            }
        }
    }
    
    HyperlinkEvent createHyperlinkEvent(JEditorPane html, HTMLDocument hdoc, String href, AttributeSet anchor, Element element) {
        URL u;
        try {
            URL base = hdoc.getBase();
            u = new URL(base, href);
            if (href != null && "file".equals(u.getProtocol()) && href.startsWith("#")) {
                String baseFile = base.getFile();
                String newFile = u.getFile();
                if (baseFile != null && newFile != null && !newFile.startsWith(baseFile)) {
                    u = new URL(base, baseFile + href);
                }
            }
        } catch (MalformedURLException m) {
            u = null;
        }
        HyperlinkEvent linkEvent = null;
        if (!hdoc.isFrameDocument()) {
            linkEvent = new HyperlinkEvent(html, HyperlinkEvent$EventType.ACTIVATED, u, href, element);
        } else {
            String target = (anchor != null) ? (String)(String)anchor.getAttribute(HTML$Attribute.TARGET) : null;
            if ((target == null) || (target.equals(""))) {
                target = hdoc.getBaseTarget();
            }
            if ((target == null) || (target.equals(""))) {
                target = "_self";
            }
            linkEvent = new HTMLFrameHyperlinkEvent(html, HyperlinkEvent$EventType.ACTIVATED, u, href, element, target);
        }
        return linkEvent;
    }
    
    void fireEvents(JEditorPane editor, HTMLDocument doc, String href, Element lastElem) {
        if (this.href != null) {
            URL u;
            try {
                u = new URL(doc.getBase(), this.href);
            } catch (MalformedURLException m) {
                u = null;
            }
            HyperlinkEvent exit = new HyperlinkEvent(editor, HyperlinkEvent$EventType.EXITED, u, this.href, lastElem);
            editor.fireHyperlinkUpdate(exit);
        }
        if (href != null) {
            URL u;
            try {
                u = new URL(doc.getBase(), href);
            } catch (MalformedURLException m) {
                u = null;
            }
            HyperlinkEvent entered = new HyperlinkEvent(editor, HyperlinkEvent$EventType.ENTERED, u, href, curElem);
            editor.fireHyperlinkUpdate(entered);
        }
    }
}
