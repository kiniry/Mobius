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

class HTMLEditorKit$InsertHRAction extends HTMLEditorKit$InsertHTMLTextAction {
    
    HTMLEditorKit$InsertHRAction() {
        super("InsertHR", "<hr>", null, HTML$Tag.IMPLIED, null, null, false);
    }
    
    public void actionPerformed(ActionEvent ae) {
        JEditorPane editor = getEditor(ae);
        if (editor != null) {
            HTMLDocument doc = getHTMLDocument(editor);
            int offset = editor.getSelectionStart();
            Element paragraph = doc.getParagraphElement(offset);
            if (paragraph.getParentElement() != null) {
                parentTag = (HTML$Tag)(HTML$Tag)paragraph.getParentElement().getAttributes().getAttribute(StyleConstants.NameAttribute);
                super.actionPerformed(ae);
            }
        }
    }
}
