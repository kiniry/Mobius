package javax.swing.text.html;

import java.util.*;
import java.awt.*;
import java.io.*;
import java.net.*;
import javax.swing.border.*;
import javax.swing.text.*;

class StyleSheet$LargeConversionSet extends SimpleAttributeSet {
    /*synthetic*/ final StyleSheet this$0;
    
    public StyleSheet$LargeConversionSet(/*synthetic*/ final StyleSheet this$0, AttributeSet source) {
        this.this$0 = this$0;
        super(source);
    }
    
    public StyleSheet$LargeConversionSet(/*synthetic*/ final StyleSheet this$0) {
        this.this$0 = this$0;
        
    }
    
    public boolean isDefined(Object key) {
        if (key instanceof StyleConstants) {
            Object cssKey = StyleSheet.access$000(this$0).styleConstantsKeyToCSSKey((StyleConstants)(StyleConstants)key);
            if (cssKey != null) {
                return super.isDefined(cssKey);
            }
        }
        return super.isDefined(key);
    }
    
    public Object getAttribute(Object key) {
        if (key instanceof StyleConstants) {
            Object cssKey = StyleSheet.access$000(this$0).styleConstantsKeyToCSSKey((StyleConstants)(StyleConstants)key);
            if (cssKey != null) {
                Object value = super.getAttribute(cssKey);
                if (value != null) {
                    return StyleSheet.access$000(this$0).cssValueToStyleConstantsValue((StyleConstants)(StyleConstants)key, value);
                }
            }
        }
        return super.getAttribute(key);
    }
}
