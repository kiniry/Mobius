package javax.swing.text.html;

import java.util.*;
import java.awt.*;
import java.io.*;
import java.net.*;
import javax.swing.border.*;
import javax.swing.text.*;

class StyleSheet$SelectorMapping implements Serializable {
    
    public StyleSheet$SelectorMapping(int specificity) {
        
        this.specificity = specificity;
    }
    
    public int getSpecificity() {
        return specificity;
    }
    
    public void setStyle(Style style) {
        this.style = style;
    }
    
    public Style getStyle() {
        return style;
    }
    
    public StyleSheet$SelectorMapping getChildSelectorMapping(String selector, boolean create) {
        StyleSheet$SelectorMapping retValue = null;
        if (children != null) {
            retValue = (StyleSheet$SelectorMapping)(StyleSheet$SelectorMapping)children.get(selector);
        } else if (create) {
            children = new HashMap(7);
        }
        if (retValue == null && create) {
            int specificity = getChildSpecificity(selector);
            retValue = createChildSelectorMapping(specificity);
            children.put(selector, retValue);
        }
        return retValue;
    }
    
    protected StyleSheet$SelectorMapping createChildSelectorMapping(int specificity) {
        return new StyleSheet$SelectorMapping(specificity);
    }
    
    protected int getChildSpecificity(String selector) {
        char firstChar = selector.charAt(0);
        int specificity = getSpecificity();
        if (firstChar == '.') {
            specificity += 100;
        } else if (firstChar == '#') {
            specificity += 10000;
        } else {
            specificity += 1;
            if (selector.indexOf('.') != -1) {
                specificity += 100;
            }
            if (selector.indexOf('#') != -1) {
                specificity += 10000;
            }
        }
        return specificity;
    }
    private int specificity;
    private Style style;
    private HashMap children;
}
