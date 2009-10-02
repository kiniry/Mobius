package javax.swing.plaf.basic;

import java.io.*;
import java.awt.*;
import javax.swing.*;
import javax.swing.text.*;
import javax.swing.text.html.*;

class BasicHTML$BasicDocument extends HTMLDocument {
    
    BasicHTML$BasicDocument(StyleSheet s, Font defaultFont, Color foreground) {
        super(s);
        setPreservesUnknownTags(false);
        setFontAndColor(defaultFont, foreground);
    }
    
    private void setFontAndColor(Font font, Color fg) {
        getStyleSheet().addRule(com.sun.java.swing.SwingUtilities2.displayPropertiesToCSS(font, fg));
    }
}
