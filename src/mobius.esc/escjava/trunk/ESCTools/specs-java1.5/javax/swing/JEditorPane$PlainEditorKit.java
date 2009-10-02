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

class JEditorPane$PlainEditorKit extends DefaultEditorKit implements ViewFactory {
    
    JEditorPane$PlainEditorKit() {
        
    }
    
    public ViewFactory getViewFactory() {
        return this;
    }
    
    public View create(Element elem) {
        Document doc = elem.getDocument();
        Object i18nFlag = doc.getProperty("i18n");
        if ((i18nFlag != null) && i18nFlag.equals(Boolean.TRUE)) {
            return createI18N(elem);
        } else {
            return new WrappedPlainView(elem);
        }
    }
    
    View createI18N(Element elem) {
        String kind = elem.getName();
        if (kind != null) {
            if (kind.equals(AbstractDocument.ContentElementName)) {
                return new JEditorPane$PlainEditorKit$PlainParagraph(elem);
            } else if (kind.equals(AbstractDocument.ParagraphElementName)) {
                return new BoxView(elem, View.Y_AXIS);
            }
        }
        return null;
    }
    {
    }
}
