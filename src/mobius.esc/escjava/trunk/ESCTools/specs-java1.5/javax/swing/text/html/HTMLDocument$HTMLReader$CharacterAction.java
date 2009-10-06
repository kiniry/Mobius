package javax.swing.text.html;

import java.util.*;
import java.io.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.swing.undo.*;

public class HTMLDocument$HTMLReader$CharacterAction extends HTMLDocument$HTMLReader$TagAction {
    /*synthetic*/ final HTMLDocument$HTMLReader this$1;
    
    public HTMLDocument$HTMLReader$CharacterAction(/*synthetic*/ final HTMLDocument$HTMLReader this$1) {
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
        this$1.charAttr.addAttribute(t, attr.copyAttributes());
        if (this$1.styleAttributes != null) {
            this$1.charAttr.addAttributes(this$1.styleAttributes);
        }
    }
    
    public void end(HTML$Tag t) {
        this$1.popCharacterStyle();
    }
}
