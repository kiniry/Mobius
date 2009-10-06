package javax.swing.text.html;

import java.util.*;
import java.io.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.swing.undo.*;

class HTMLDocument$HTMLReader$MetaAction extends HTMLDocument$HTMLReader$HiddenAction {
    /*synthetic*/ final HTMLDocument$HTMLReader this$1;
    
    HTMLDocument$HTMLReader$MetaAction(/*synthetic*/ final HTMLDocument$HTMLReader this$1) {
        super(this$1);
        this.this$1 = this$1;
    }
    
    public void start(HTML$Tag t, MutableAttributeSet a) {
        Object equiv = a.getAttribute(HTML$Attribute.HTTPEQUIV);
        if (equiv != null) {
            equiv = ((String)(String)equiv).toLowerCase();
            if (equiv.equals("content-style-type")) {
                String value = (String)(String)a.getAttribute(HTML$Attribute.CONTENT);
                this$1.this$0.setDefaultStyleSheetType(value);
                this$1.isStyleCSS = "text/css".equals(this$1.this$0.getDefaultStyleSheetType());
            } else if (equiv.equals("default-style")) {
                this$1.defaultStyle = (String)(String)a.getAttribute(HTML$Attribute.CONTENT);
            }
        }
        super.start(t, a);
    }
    
    boolean isEmpty(HTML$Tag t) {
        return true;
    }
}
