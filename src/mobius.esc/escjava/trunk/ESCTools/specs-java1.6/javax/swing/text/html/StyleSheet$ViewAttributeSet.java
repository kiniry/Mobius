package javax.swing.text.html;

import java.util.*;
import java.awt.*;
import java.io.*;
import java.net.*;
import javax.swing.border.*;
import javax.swing.text.*;

class StyleSheet$ViewAttributeSet extends MuxingAttributeSet {
    /*synthetic*/ final StyleSheet this$0;
    
    StyleSheet$ViewAttributeSet(/*synthetic*/ final StyleSheet this$0, View v) {
        this.this$0 = this$0;
        
        host = v;
        Document doc = v.getDocument();
        StyleSheet$SearchBuffer sb = StyleSheet$SearchBuffer.obtainSearchBuffer();
        Vector muxList = sb.getVector();
        try {
            if (doc instanceof HTMLDocument) {
                StyleSheet styles = this$0;
                Element elem = v.getElement();
                AttributeSet a = elem.getAttributes();
                AttributeSet htmlAttr = styles.translateHTMLToCSS(a);
                if (htmlAttr.getAttributeCount() != 0) {
                    muxList.addElement(htmlAttr);
                }
                if (elem.isLeaf()) {
                    Enumeration keys = a.getAttributeNames();
                    while (keys.hasMoreElements()) {
                        Object key = keys.nextElement();
                        if (key instanceof HTML$Tag) {
                            if ((HTML$Tag)(HTML$Tag)key == HTML$Tag.A) {
                                Object o = a.getAttribute((HTML$Tag)(HTML$Tag)key);
                                if (o != null && o instanceof AttributeSet) {
                                    AttributeSet attr = (AttributeSet)(AttributeSet)o;
                                    if (attr.getAttribute(HTML$Attribute.HREF) == null) {
                                        continue;
                                    }
                                }
                            }
                            AttributeSet cssRule = styles.getRule((HTML$Tag)(HTML$Tag)key, elem);
                            if (cssRule != null) {
                                muxList.addElement(cssRule);
                            }
                        }
                    }
                } else {
                    HTML$Tag t = (HTML$Tag)(HTML$Tag)a.getAttribute(StyleConstants.NameAttribute);
                    AttributeSet cssRule = styles.getRule(t, elem);
                    if (cssRule != null) {
                        muxList.addElement(cssRule);
                    }
                }
            }
            AttributeSet[] attrs = new AttributeSet[muxList.size()];
            muxList.copyInto(attrs);
            setAttributes(attrs);
        } finally {
            StyleSheet$SearchBuffer.releaseSearchBuffer(sb);
        }
    }
    
    public boolean isDefined(Object key) {
        if (key instanceof StyleConstants) {
            Object cssKey = StyleSheet.access$000(this$0).styleConstantsKeyToCSSKey((StyleConstants)(StyleConstants)key);
            if (cssKey != null) {
                key = cssKey;
            }
        }
        return super.isDefined(key);
    }
    
    public Object getAttribute(Object key) {
        if (key instanceof StyleConstants) {
            Object cssKey = StyleSheet.access$000(this$0).styleConstantsKeyToCSSKey((StyleConstants)(StyleConstants)key);
            if (cssKey != null) {
                Object value = doGetAttribute(cssKey);
                if (value instanceof CSS$CssValue) {
                    return ((CSS$CssValue)(CSS$CssValue)value).toStyleConstants((StyleConstants)(StyleConstants)key, host);
                }
            }
        }
        return doGetAttribute(key);
    }
    
    Object doGetAttribute(Object key) {
        Object retValue = super.getAttribute(key);
        if (retValue != null) {
            return retValue;
        }
        if (key instanceof CSS$Attribute) {
            CSS$Attribute css = (CSS$Attribute)(CSS$Attribute)key;
            if (css.isInherited()) {
                AttributeSet parent = getResolveParent();
                if (parent != null) return parent.getAttribute(key);
            }
        }
        return null;
    }
    
    public AttributeSet getResolveParent() {
        if (host == null) {
            return null;
        }
        View parent = host.getParent();
        return (parent != null) ? parent.getAttributes() : null;
    }
    View host;
}
