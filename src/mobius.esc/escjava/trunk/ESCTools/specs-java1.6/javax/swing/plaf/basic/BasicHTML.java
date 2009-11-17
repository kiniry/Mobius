package javax.swing.plaf.basic;

import java.io.*;
import java.awt.*;
import java.net.URL;
import javax.swing.*;
import javax.swing.text.*;
import javax.swing.text.html.*;

public class BasicHTML {
    
    /*synthetic*/ static ViewFactory access$000() {
        return basicHTMLViewFactory;
    }
    
    public BasicHTML() {
        
    }
    
    public static View createHTMLView(JComponent c, String html) {
        BasicHTML$BasicEditorKit kit = getFactory();
        Document doc = kit.createDefaultDocument(c.getFont(), c.getForeground());
        Object base = c.getClientProperty(documentBaseKey);
        if (base instanceof URL) {
            ((HTMLDocument)(HTMLDocument)doc).setBase((URL)(URL)base);
        }
        Reader r = new StringReader(html);
        try {
            kit.read(r, doc, 0);
        } catch (Throwable e) {
        }
        ViewFactory f = kit.getViewFactory();
        View hview = f.create(doc.getDefaultRootElement());
        View v = new BasicHTML$Renderer(c, f, hview);
        return v;
    }
    
    public static boolean isHTMLString(String s) {
        if (s != null) {
            if ((s.length() >= 6) && (s.charAt(0) == '<') && (s.charAt(5) == '>')) {
                String tag = s.substring(1, 5);
                return tag.equalsIgnoreCase(propertyKey);
            }
        }
        return false;
    }
    
    public static void updateRenderer(JComponent c, String text) {
        View value = null;
        View oldValue = (View)(View)c.getClientProperty(BasicHTML.propertyKey);
        Boolean htmlDisabled = (Boolean)(Boolean)c.getClientProperty(htmlDisable);
        if (htmlDisabled != Boolean.TRUE && BasicHTML.isHTMLString(text)) {
            value = BasicHTML.createHTMLView(c, text);
        }
        if (value != oldValue && oldValue != null) {
            for (int i = 0; i < oldValue.getViewCount(); i++) {
                oldValue.getView(i).setParent(null);
            }
        }
        c.putClientProperty(BasicHTML.propertyKey, value);
    }
    private static final String htmlDisable = "html.disable";
    public static final String propertyKey = "html";
    public static final String documentBaseKey = "html.base";
    
    static BasicHTML$BasicEditorKit getFactory() {
        if (basicHTMLFactory == null) {
            basicHTMLViewFactory = new BasicHTML$BasicHTMLViewFactory();
            basicHTMLFactory = new BasicHTML$BasicEditorKit();
        }
        return basicHTMLFactory;
    }
    private static BasicHTML$BasicEditorKit basicHTMLFactory;
    private static ViewFactory basicHTMLViewFactory;
    private static final String styleChanges = "p { margin-top: 0; margin-bottom: 0; margin-left: 0; margin-right: 0 }body { margin-top: 0; margin-bottom: 0; margin-left: 0; margin-right: 0 }";
    {
    }
    {
    }
    {
    }
    {
    }
}
