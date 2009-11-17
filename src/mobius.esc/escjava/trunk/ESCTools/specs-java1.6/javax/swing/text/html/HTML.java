package javax.swing.text.html;

import java.io.*;
import java.util.Hashtable;
import javax.swing.text.AttributeSet;
import javax.swing.text.StyleConstants;
import javax.swing.text.StyleContext;

public class HTML {
    
    public HTML() {
        
    }
    {
    }
    {
    }
    {
    }
    private static final Hashtable tagHashtable = new Hashtable(73);
    private static final Hashtable scMapping = new Hashtable(8);
    static {
        for (int i = 0; i < HTML$Tag.allTags.length; i++) {
            tagHashtable.put(HTML$Tag.allTags[i].toString(), HTML$Tag.allTags[i]);
            StyleContext.registerStaticAttributeKey(HTML$Tag.allTags[i]);
        }
        StyleContext.registerStaticAttributeKey(HTML$Tag.IMPLIED);
        StyleContext.registerStaticAttributeKey(HTML$Tag.CONTENT);
        StyleContext.registerStaticAttributeKey(HTML$Tag.COMMENT);
        for (int i = 0; i < HTML$Attribute.allAttributes.length; i++) {
            StyleContext.registerStaticAttributeKey(HTML$Attribute.allAttributes[i]);
        }
        StyleContext.registerStaticAttributeKey(HTML.NULL_ATTRIBUTE_VALUE);
        scMapping.put(StyleConstants.Bold, HTML$Tag.B);
        scMapping.put(StyleConstants.Italic, HTML$Tag.I);
        scMapping.put(StyleConstants.Underline, HTML$Tag.U);
        scMapping.put(StyleConstants.StrikeThrough, HTML$Tag.STRIKE);
        scMapping.put(StyleConstants.Superscript, HTML$Tag.SUP);
        scMapping.put(StyleConstants.Subscript, HTML$Tag.SUB);
        scMapping.put(StyleConstants.FontFamily, HTML$Tag.FONT);
        scMapping.put(StyleConstants.FontSize, HTML$Tag.FONT);
    }
    
    public static HTML$Tag[] getAllTags() {
        HTML$Tag[] tags = new HTML$Tag[HTML$Tag.allTags.length];
        System.arraycopy(HTML$Tag.allTags, 0, tags, 0, HTML$Tag.allTags.length);
        return tags;
    }
    
    public static HTML$Tag getTag(String tagName) {
        Object t = tagHashtable.get(tagName);
        return (t == null ? null : (HTML$Tag)(HTML$Tag)t);
    }
    
    static HTML$Tag getTagForStyleConstantsKey(StyleConstants sc) {
        return (HTML$Tag)(HTML$Tag)scMapping.get(sc);
    }
    
    public static int getIntegerAttributeValue(AttributeSet attr, HTML$Attribute key, int def) {
        int value = def;
        String istr = (String)(String)attr.getAttribute(key);
        if (istr != null) {
            try {
                value = Integer.valueOf(istr).intValue();
            } catch (NumberFormatException e) {
                value = def;
            }
        }
        return value;
    }
    public static final String NULL_ATTRIBUTE_VALUE = "#DEFAULT";
    private static final Hashtable attHashtable = new Hashtable(77);
    static {
        for (int i = 0; i < HTML$Attribute.allAttributes.length; i++) {
            attHashtable.put(HTML$Attribute.allAttributes[i].toString(), HTML$Attribute.allAttributes[i]);
        }
    }
    
    public static HTML$Attribute[] getAllAttributeKeys() {
        HTML$Attribute[] attributes = new HTML$Attribute[HTML$Attribute.allAttributes.length];
        System.arraycopy(HTML$Attribute.allAttributes, 0, attributes, 0, HTML$Attribute.allAttributes.length);
        return attributes;
    }
    
    public static HTML$Attribute getAttributeKey(String attName) {
        Object a = attHashtable.get(attName);
        if (a == null) {
            return null;
        }
        return (HTML$Attribute)(HTML$Attribute)a;
    }
}
