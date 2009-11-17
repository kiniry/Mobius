package javax.swing.plaf.basic;

import java.io.*;
import java.awt.*;
import javax.swing.*;
import javax.swing.text.*;
import javax.swing.text.html.*;

class BasicHTML$BasicEditorKit extends HTMLEditorKit {
    
    BasicHTML$BasicEditorKit() {
        
    }
    private static StyleSheet defaultStyles;
    
    public StyleSheet getStyleSheet() {
        if (defaultStyles == null) {
            defaultStyles = new StyleSheet();
            StringReader r = new StringReader("p { margin-top: 0; margin-bottom: 0; margin-left: 0; margin-right: 0 }body { margin-top: 0; margin-bottom: 0; margin-left: 0; margin-right: 0 }");
            try {
                defaultStyles.loadRules(r, null);
            } catch (Throwable e) {
            }
            r.close();
            defaultStyles.addStyleSheet(super.getStyleSheet());
        }
        return defaultStyles;
    }
    
    public Document createDefaultDocument(Font defaultFont, Color foreground) {
        StyleSheet styles = getStyleSheet();
        StyleSheet ss = new StyleSheet();
        ss.addStyleSheet(styles);
        BasicHTML$BasicDocument doc = new BasicHTML$BasicDocument(ss, defaultFont, foreground);
        doc.setAsynchronousLoadPriority(Integer.MAX_VALUE);
        doc.setPreservesUnknownTags(false);
        return doc;
    }
    
    public ViewFactory getViewFactory() {
        return BasicHTML.access$000();
    }
}
