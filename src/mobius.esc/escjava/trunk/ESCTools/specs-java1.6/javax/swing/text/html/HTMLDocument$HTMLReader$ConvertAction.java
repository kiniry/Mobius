package javax.swing.text.html;

import java.util.*;
import java.io.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.swing.undo.*;

class HTMLDocument$HTMLReader$ConvertAction extends HTMLDocument$HTMLReader$TagAction {
    /*synthetic*/ final HTMLDocument$HTMLReader this$1;
    
    HTMLDocument$HTMLReader$ConvertAction(/*synthetic*/ final HTMLDocument$HTMLReader this$1) {
        super(this$1);
        this.this$1 = this$1;
    }
    
    public void start(HTML$Tag t, MutableAttributeSet attr) {
        this$1.pushCharacterStyle();
        if (!this$1.foundInsertTag) {
            boolean insert = HTMLDocument.HTMLReader.access$900(this$1, t, attr, false);
            if (this$1.foundInsertTag) {
                if (!this$1.inParagraph) {
                    this$1.inParagraph = this$1.impliedP = true;
                }
            }
            if (!insert) {
                return;
            }
        }
        if (attr.isDefined(HTMLEditorKit$ParserCallback.IMPLIED)) {
            attr.removeAttribute(HTMLEditorKit$ParserCallback.IMPLIED);
        }
        if (this$1.styleAttributes != null) {
            this$1.charAttr.addAttributes(this$1.styleAttributes);
        }
        this$1.charAttr.addAttribute(t, attr.copyAttributes());
        StyleSheet sheet = this$1.this$0.getStyleSheet();
        if (t == HTML$Tag.B) {
            sheet.addCSSAttribute(this$1.charAttr, CSS$Attribute.FONT_WEIGHT, "bold");
        } else if (t == HTML$Tag.I) {
            sheet.addCSSAttribute(this$1.charAttr, CSS$Attribute.FONT_STYLE, "italic");
        } else if (t == HTML$Tag.U) {
            Object v = this$1.charAttr.getAttribute(CSS$Attribute.TEXT_DECORATION);
            String value = "underline";
            value = (v != null) ? value + "," + v.toString() : value;
            sheet.addCSSAttribute(this$1.charAttr, CSS$Attribute.TEXT_DECORATION, value);
        } else if (t == HTML$Tag.STRIKE) {
            Object v = this$1.charAttr.getAttribute(CSS$Attribute.TEXT_DECORATION);
            String value = "line-through";
            value = (v != null) ? value + "," + v.toString() : value;
            sheet.addCSSAttribute(this$1.charAttr, CSS$Attribute.TEXT_DECORATION, value);
        } else if (t == HTML$Tag.SUP) {
            Object v = this$1.charAttr.getAttribute(CSS$Attribute.VERTICAL_ALIGN);
            String value = "sup";
            value = (v != null) ? value + "," + v.toString() : value;
            sheet.addCSSAttribute(this$1.charAttr, CSS$Attribute.VERTICAL_ALIGN, value);
        } else if (t == HTML$Tag.SUB) {
            Object v = this$1.charAttr.getAttribute(CSS$Attribute.VERTICAL_ALIGN);
            String value = "sub";
            value = (v != null) ? value + "," + v.toString() : value;
            sheet.addCSSAttribute(this$1.charAttr, CSS$Attribute.VERTICAL_ALIGN, value);
        } else if (t == HTML$Tag.FONT) {
            String color = (String)(String)attr.getAttribute(HTML$Attribute.COLOR);
            if (color != null) {
                sheet.addCSSAttribute(this$1.charAttr, CSS$Attribute.COLOR, color);
            }
            String face = (String)(String)attr.getAttribute(HTML$Attribute.FACE);
            if (face != null) {
                sheet.addCSSAttribute(this$1.charAttr, CSS$Attribute.FONT_FAMILY, face);
            }
            String size = (String)(String)attr.getAttribute(HTML$Attribute.SIZE);
            if (size != null) {
                sheet.addCSSAttributeFromHTML(this$1.charAttr, CSS$Attribute.FONT_SIZE, size);
            }
        }
    }
    
    public void end(HTML$Tag t) {
        this$1.popCharacterStyle();
    }
}
