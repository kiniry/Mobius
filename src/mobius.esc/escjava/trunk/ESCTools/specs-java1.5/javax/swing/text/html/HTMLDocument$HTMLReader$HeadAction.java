package javax.swing.text.html;

import java.util.*;
import java.io.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.swing.undo.*;

class HTMLDocument$HTMLReader$HeadAction extends HTMLDocument$HTMLReader$BlockAction {
    /*synthetic*/ final HTMLDocument$HTMLReader this$1;
    
    HTMLDocument$HTMLReader$HeadAction(/*synthetic*/ final HTMLDocument$HTMLReader this$1) {
        this.this$1 = this$1;
        super(this$1);
    }
    
    public void start(HTML$Tag t, MutableAttributeSet a) {
        this$1.inHead = true;
        if ((this$1.insertTag == null && !HTMLDocument.HTMLReader.access$800(this$1)) || (this$1.insertTag == HTML$Tag.HEAD) || (HTMLDocument.HTMLReader.access$800(this$1) && (this$1.foundInsertTag || !a.isDefined(HTMLEditorKit$ParserCallback.IMPLIED)))) {
            super.start(t, a);
        }
    }
    
    public void end(HTML$Tag t) {
        this$1.inHead = this$1.inStyle = false;
        if (this$1.styles != null) {
            boolean isDefaultCSS = this$1.isStyleCSS;
            for (int counter = 0, maxCounter = this$1.styles.size(); counter < maxCounter; ) {
                Object value = this$1.styles.elementAt(counter);
                if (value == HTML$Tag.LINK) {
                    handleLink((AttributeSet)(AttributeSet)this$1.styles.elementAt(++counter));
                    counter++;
                } else {
                    String type = (String)(String)this$1.styles.elementAt(++counter);
                    boolean isCSS = (type == null) ? isDefaultCSS : type.equals("text/css");
                    while (++counter < maxCounter && (this$1.styles.elementAt(counter) instanceof String)) {
                        if (isCSS) {
                            this$1.addCSSRules((String)(String)this$1.styles.elementAt(counter));
                        }
                    }
                }
            }
        }
        if ((this$1.insertTag == null && !HTMLDocument.HTMLReader.access$800(this$1)) || this$1.insertTag == HTML$Tag.HEAD || (HTMLDocument.HTMLReader.access$800(this$1) && this$1.foundInsertTag)) {
            super.end(t);
        }
    }
    
    boolean isEmpty(HTML$Tag t) {
        return false;
    }
    
    private void handleLink(AttributeSet attr) {
        String type = (String)(String)attr.getAttribute(HTML$Attribute.TYPE);
        if (type == null) {
            type = this$1.this$0.getDefaultStyleSheetType();
        }
        if (type.equals("text/css")) {
            String rel = (String)(String)attr.getAttribute(HTML$Attribute.REL);
            String title = (String)(String)attr.getAttribute(HTML$Attribute.TITLE);
            String media = (String)(String)attr.getAttribute(HTML$Attribute.MEDIA);
            if (media == null) {
                media = "all";
            } else {
                media = media.toLowerCase();
            }
            if (rel != null) {
                rel = rel.toLowerCase();
                if ((media.indexOf("all") != -1 || media.indexOf("screen") != -1) && (rel.equals("stylesheet") || (rel.equals("alternate stylesheet") && title.equals(this$1.defaultStyle)))) {
                    this$1.linkCSSStyleSheet((String)(String)attr.getAttribute(HTML$Attribute.HREF));
                }
            }
        }
    }
}
