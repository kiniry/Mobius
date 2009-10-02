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

public class JEditorPane$JEditorPaneAccessibleHypertextSupport$HTMLLink extends AccessibleHyperlink {
    /*synthetic*/ final JEditorPane$JEditorPaneAccessibleHypertextSupport this$1;
    Element element;
    
    public JEditorPane$JEditorPaneAccessibleHypertextSupport$HTMLLink(/*synthetic*/ final JEditorPane$JEditorPaneAccessibleHypertextSupport this$1, Element e) {
        this.this$1 = this$1;
        
        element = e;
    }
    
    public boolean isValid() {
        return this$1.linksValid;
    }
    
    public int getAccessibleActionCount() {
        return 1;
    }
    
    public boolean doAccessibleAction(int i) {
        if (i == 0 && isValid() == true) {
            URL u = (URL)(URL)getAccessibleActionObject(i);
            if (u != null) {
                HyperlinkEvent linkEvent = new HyperlinkEvent(this$1.this$0, HyperlinkEvent$EventType.ACTIVATED, u);
                this$1.this$0.fireHyperlinkUpdate(linkEvent);
                return true;
            }
        }
        return false;
    }
    
    public String getAccessibleActionDescription(int i) {
        if (i == 0 && isValid() == true) {
            Document d = this$1.this$0.getDocument();
            if (d != null) {
                try {
                    return d.getText(getStartIndex(), getEndIndex() - getStartIndex());
                } catch (BadLocationException exception) {
                    return null;
                }
            }
        }
        return null;
    }
    
    public Object getAccessibleActionObject(int i) {
        if (i == 0 && isValid() == true) {
            AttributeSet as = element.getAttributes();
            AttributeSet anchor = (AttributeSet)(AttributeSet)as.getAttribute(HTML$Tag.A);
            String href = (anchor != null) ? (String)(String)anchor.getAttribute(HTML$Attribute.HREF) : null;
            if (href != null) {
                URL u;
                try {
                    u = new URL(this$1.this$0.getPage(), href);
                } catch (MalformedURLException m) {
                    u = null;
                }
                return u;
            }
        }
        return null;
    }
    
    public Object getAccessibleActionAnchor(int i) {
        return getAccessibleActionDescription(i);
    }
    
    public int getStartIndex() {
        return element.getStartOffset();
    }
    
    public int getEndIndex() {
        return element.getEndOffset();
    }
}
