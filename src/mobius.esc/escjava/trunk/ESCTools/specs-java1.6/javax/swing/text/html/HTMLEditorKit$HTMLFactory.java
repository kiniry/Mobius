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

public class HTMLEditorKit$HTMLFactory implements ViewFactory {
    
    public HTMLEditorKit$HTMLFactory() {
        
    }
    
    public View create(Element elem) {
        Object o = elem.getAttributes().getAttribute(StyleConstants.NameAttribute);
        if (o instanceof HTML$Tag) {
            HTML$Tag kind = (HTML$Tag)(HTML$Tag)o;
            if (kind == HTML$Tag.CONTENT) {
                return new InlineView(elem);
            } else if (kind == HTML$Tag.IMPLIED) {
                String ws = (String)(String)elem.getAttributes().getAttribute(CSS$Attribute.WHITE_SPACE);
                if ((ws != null) && ws.equals("pre")) {
                    return new LineView(elem);
                }
                return new javax.swing.text.html.ParagraphView(elem);
            } else if ((kind == HTML$Tag.P) || (kind == HTML$Tag.H1) || (kind == HTML$Tag.H2) || (kind == HTML$Tag.H3) || (kind == HTML$Tag.H4) || (kind == HTML$Tag.H5) || (kind == HTML$Tag.H6) || (kind == HTML$Tag.DT)) {
                return new javax.swing.text.html.ParagraphView(elem);
            } else if ((kind == HTML$Tag.MENU) || (kind == HTML$Tag.DIR) || (kind == HTML$Tag.UL) || (kind == HTML$Tag.OL)) {
                return new ListView(elem);
            } else if (kind == HTML$Tag.BODY) {
                return new HTMLEditorKit$HTMLFactory$BodyBlockView(elem);
            } else if (kind == HTML$Tag.HTML) {
                return new BlockView(elem, View.Y_AXIS);
            } else if ((kind == HTML$Tag.LI) || (kind == HTML$Tag.CENTER) || (kind == HTML$Tag.DL) || (kind == HTML$Tag.DD) || (kind == HTML$Tag.DIV) || (kind == HTML$Tag.BLOCKQUOTE) || (kind == HTML$Tag.PRE) || (kind == HTML$Tag.FORM)) {
                return new BlockView(elem, View.Y_AXIS);
            } else if (kind == HTML$Tag.NOFRAMES) {
                return new NoFramesView(elem, View.Y_AXIS);
            } else if (kind == HTML$Tag.IMG) {
                return new ImageView(elem);
            } else if (kind == HTML$Tag.ISINDEX) {
                return new IsindexView(elem);
            } else if (kind == HTML$Tag.HR) {
                return new HRuleView(elem);
            } else if (kind == HTML$Tag.BR) {
                return new BRView(elem);
            } else if (kind == HTML$Tag.TABLE) {
                return new javax.swing.text.html.TableView(elem);
            } else if ((kind == HTML$Tag.INPUT) || (kind == HTML$Tag.SELECT) || (kind == HTML$Tag.TEXTAREA)) {
                return new FormView(elem);
            } else if (kind == HTML$Tag.OBJECT) {
                return new ObjectView(elem);
            } else if (kind == HTML$Tag.FRAMESET) {
                if (elem.getAttributes().isDefined(HTML$Attribute.ROWS)) {
                    return new FrameSetView(elem, View.Y_AXIS);
                } else if (elem.getAttributes().isDefined(HTML$Attribute.COLS)) {
                    return new FrameSetView(elem, View.X_AXIS);
                }
                throw new RuntimeException("Can\'t build a" + kind + ", " + elem + ":" + "no ROWS or COLS defined.");
            } else if (kind == HTML$Tag.FRAME) {
                return new FrameView(elem);
            } else if (kind instanceof HTML$UnknownTag) {
                return new HiddenTagView(elem);
            } else if (kind == HTML$Tag.COMMENT) {
                return new CommentView(elem);
            } else if (kind == HTML$Tag.HEAD) {
                return new HTMLEditorKit$HTMLFactory$1(this, elem, View.X_AXIS);
            } else if ((kind == HTML$Tag.TITLE) || (kind == HTML$Tag.META) || (kind == HTML$Tag.LINK) || (kind == HTML$Tag.STYLE) || (kind == HTML$Tag.SCRIPT) || (kind == HTML$Tag.AREA) || (kind == HTML$Tag.MAP) || (kind == HTML$Tag.PARAM) || (kind == HTML$Tag.APPLET)) {
                return new HiddenTagView(elem);
            }
        }
        String nm = elem.getName();
        if (nm != null) {
            if (nm.equals(AbstractDocument.ContentElementName)) {
                return new LabelView(elem);
            } else if (nm.equals(AbstractDocument.ParagraphElementName)) {
                return new ParagraphView(elem);
            } else if (nm.equals(AbstractDocument.SectionElementName)) {
                return new BoxView(elem, View.Y_AXIS);
            } else if (nm.equals(StyleConstants.ComponentElementName)) {
                return new ComponentView(elem);
            } else if (nm.equals(StyleConstants.IconElementName)) {
                return new IconView(elem);
            }
        }
        return new LabelView(elem);
    }
    {
    }
}
