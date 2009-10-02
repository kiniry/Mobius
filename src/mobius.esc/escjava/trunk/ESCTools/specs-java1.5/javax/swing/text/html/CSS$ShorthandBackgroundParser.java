package javax.swing.text.html;

import java.io.*;
import javax.swing.text.*;

class CSS$ShorthandBackgroundParser {
    
    CSS$ShorthandBackgroundParser() {
        
    }
    
    static void parseShorthandBackground(CSS css, String value, MutableAttributeSet attr) {
        String[] strings = CSS.parseStrings(value);
        int count = strings.length;
        int index = 0;
        short found = 0;
        while (index < count) {
            String string = strings[index++];
            if ((found & 1) == 0 && isImage(string)) {
                css.addInternalCSSValue(attr, CSS$Attribute.BACKGROUND_IMAGE, string);
                found |= 1;
            } else if ((found & 2) == 0 && isRepeat(string)) {
                css.addInternalCSSValue(attr, CSS$Attribute.BACKGROUND_REPEAT, string);
                found |= 2;
            } else if ((found & 4) == 0 && isAttachment(string)) {
                css.addInternalCSSValue(attr, CSS$Attribute.BACKGROUND_ATTACHMENT, string);
                found |= 4;
            } else if ((found & 8) == 0 && isPosition(string)) {
                if (index < count && isPosition(strings[index])) {
                    css.addInternalCSSValue(attr, CSS$Attribute.BACKGROUND_POSITION, string + " " + strings[index++]);
                } else {
                    css.addInternalCSSValue(attr, CSS$Attribute.BACKGROUND_POSITION, string);
                }
                found |= 8;
            } else if ((found & 16) == 0 && isColor(string)) {
                css.addInternalCSSValue(attr, CSS$Attribute.BACKGROUND_COLOR, string);
                found |= 16;
            }
        }
        if ((found & 1) == 0) {
            css.addInternalCSSValue(attr, CSS$Attribute.BACKGROUND_IMAGE, null);
        }
        if ((found & 2) == 0) {
            css.addInternalCSSValue(attr, CSS$Attribute.BACKGROUND_REPEAT, "repeat");
        }
        if ((found & 4) == 0) {
            css.addInternalCSSValue(attr, CSS$Attribute.BACKGROUND_ATTACHMENT, "scroll");
        }
        if ((found & 8) == 0) {
            css.addInternalCSSValue(attr, CSS$Attribute.BACKGROUND_POSITION, null);
        }
    }
    
    static boolean isImage(String string) {
        return (string.startsWith("url(") && string.endsWith(")"));
    }
    
    static boolean isRepeat(String string) {
        return (string.equals("repeat-x") || string.equals("repeat-y") || string.equals("repeat") || string.equals("no-repeat"));
    }
    
    static boolean isAttachment(String string) {
        return (string.equals("fixed") || string.equals("scroll"));
    }
    
    static boolean isPosition(String string) {
        return (string.equals("top") || string.equals("bottom") || string.equals("left") || string.equals("right") || string.equals("center") || (string.length() > 0 && Character.isDigit(string.charAt(0))));
    }
    
    static boolean isColor(String string) {
        return (CSS.stringToColor(string) != null);
    }
}
