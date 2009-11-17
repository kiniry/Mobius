package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.net.*;
import java.util.*;
import java.io.*;
import java.util.*;
import javax.swing.plaf.*;
import javax.swing.text.*;
import javax.swing.event.*;
import javax.swing.text.html.*;
import javax.accessibility.*;

public class JEditorPane$JEditorPaneAccessibleHypertextSupport extends JEditorPane$AccessibleJEditorPane implements AccessibleHypertext {
    /*synthetic*/ final JEditorPane this$0;
    {
    }
    {
    }
    JEditorPane$JEditorPaneAccessibleHypertextSupport$LinkVector hyperlinks;
    boolean linksValid = false;
    
    private void buildLinkTable() {
        hyperlinks.removeAllElements();
        Document d = this$0.getDocument();
        if (d != null) {
            ElementIterator ei = new ElementIterator(d);
            Element e;
            AttributeSet as;
            AttributeSet anchor;
            String href;
            while ((e = ei.next()) != null) {
                if (e.isLeaf()) {
                    as = e.getAttributes();
                    anchor = (AttributeSet)(AttributeSet)as.getAttribute(HTML$Tag.A);
                    href = (anchor != null) ? (String)(String)anchor.getAttribute(HTML$Attribute.HREF) : null;
                    if (href != null) {
                        hyperlinks.addElement(new JEditorPane$JEditorPaneAccessibleHypertextSupport$HTMLLink(this, e));
                    }
                }
            }
        }
        linksValid = true;
    }
    
    public JEditorPane$JEditorPaneAccessibleHypertextSupport(/*synthetic*/ final JEditorPane this$0) {
        super(this$0);
        this.this$0 = this$0;
        hyperlinks = new JEditorPane$JEditorPaneAccessibleHypertextSupport$LinkVector(this, null);
        Document d = this$0.getDocument();
        if (d != null) {
            d.addDocumentListener(new JEditorPane$JEditorPaneAccessibleHypertextSupport$1(this, this$0));
        }
    }
    
    public int getLinkCount() {
        if (linksValid == false) {
            buildLinkTable();
        }
        return hyperlinks.size();
    }
    
    public int getLinkIndex(int charIndex) {
        if (linksValid == false) {
            buildLinkTable();
        }
        Element e = null;
        Document doc = this$0.getDocument();
        if (doc != null) {
            for (e = doc.getDefaultRootElement(); !e.isLeaf(); ) {
                int index = e.getElementIndex(charIndex);
                e = e.getElement(index);
            }
        }
        return hyperlinks.baseElementIndex(e);
    }
    
    public AccessibleHyperlink getLink(int linkIndex) {
        if (linksValid == false) {
            buildLinkTable();
        }
        if (linkIndex >= 0 && linkIndex < hyperlinks.size()) {
            return (AccessibleHyperlink)(AccessibleHyperlink)hyperlinks.elementAt(linkIndex);
        } else {
            return null;
        }
    }
    
    public String getLinkText(int linkIndex) {
        if (linksValid == false) {
            buildLinkTable();
        }
        Element e = (Element)(Element)hyperlinks.elementAt(linkIndex);
        if (e != null) {
            Document d = this$0.getDocument();
            if (d != null) {
                try {
                    return d.getText(e.getStartOffset(), e.getEndOffset() - e.getStartOffset());
                } catch (BadLocationException exception) {
                    return null;
                }
            }
        }
        return null;
    }
}
