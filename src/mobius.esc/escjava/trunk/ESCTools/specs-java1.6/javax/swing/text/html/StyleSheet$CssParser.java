package javax.swing.text.html;

import java.util.*;
import java.awt.*;
import java.io.*;
import java.net.*;
import javax.swing.border.*;
import javax.swing.text.*;

class StyleSheet$CssParser implements CSSParser$CSSParserCallback {
    /*synthetic*/ final StyleSheet this$0;
    
    StyleSheet$CssParser(/*synthetic*/ final StyleSheet this$0) {
        this.this$0 = this$0;
        
    }
    
    public AttributeSet parseDeclaration(String string) {
        try {
            return parseDeclaration(new StringReader(string));
        } catch (IOException ioe) {
        }
        return null;
    }
    
    public AttributeSet parseDeclaration(Reader r) throws IOException {
        parse(base, r, true, false);
        return declaration.copyAttributes();
    }
    
    public void parse(URL base, Reader r, boolean parseDeclaration, boolean isLink) throws IOException {
        this.base = base;
        this.isLink = isLink;
        this.parsingDeclaration = parseDeclaration;
        declaration.removeAttributes(declaration);
        selectorTokens.removeAllElements();
        selectors.removeAllElements();
        propertyName = null;
        parser.parse(r, this, parseDeclaration);
    }
    
    public void handleImport(String importString) {
        URL url = CSS.getURL(base, importString);
        if (url != null) {
            this$0.importStyleSheet(url);
        }
    }
    
    public void handleSelector(String selector) {
        selector = selector.toLowerCase();
        int length = selector.length();
        if (selector.endsWith(",")) {
            if (length > 1) {
                selector = selector.substring(0, length - 1);
                selectorTokens.addElement(selector);
            }
            addSelector();
        } else if (length > 0) {
            selectorTokens.addElement(selector);
        }
    }
    
    public void startRule() {
        if (selectorTokens.size() > 0) {
            addSelector();
        }
        propertyName = null;
    }
    
    public void handleProperty(String property) {
        propertyName = property;
    }
    
    public void handleValue(String value) {
        if (propertyName != null && value != null && value.length() > 0) {
            CSS$Attribute cssKey = CSS.getAttribute(propertyName);
            if (cssKey != null) {
                if (cssKey == CSS$Attribute.LIST_STYLE_IMAGE) {
                    if (value != null && !value.equals("none")) {
                        URL url = CSS.getURL(base, value);
                        if (url != null) {
                            value = url.toString();
                        }
                    }
                }
                this$0.addCSSAttribute(declaration, cssKey, value);
            }
            propertyName = null;
        }
    }
    
    public void endRule() {
        int n = selectors.size();
        for (int i = 0; i < n; i++) {
            String[] selector = (String[])(String[])selectors.elementAt(i);
            if (selector.length > 0) {
                this$0.addRule(selector, declaration, isLink);
            }
        }
        declaration.removeAttributes(declaration);
        selectors.removeAllElements();
    }
    
    private void addSelector() {
        String[] selector = new String[selectorTokens.size()];
        selectorTokens.copyInto(selector);
        selectors.addElement(selector);
        selectorTokens.removeAllElements();
    }
    Vector selectors = new Vector();
    Vector selectorTokens = new Vector();
    String propertyName;
    MutableAttributeSet declaration = new SimpleAttributeSet();
    boolean parsingDeclaration;
    boolean isLink;
    URL base;
    CSSParser parser = new CSSParser();
}
