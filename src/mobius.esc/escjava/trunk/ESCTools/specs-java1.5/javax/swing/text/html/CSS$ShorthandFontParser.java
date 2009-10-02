package javax.swing.text.html;

import java.io.*;
import javax.swing.text.*;

class CSS$ShorthandFontParser {
    
    CSS$ShorthandFontParser() {
        
    }
    
    static void parseShorthandFont(CSS css, String value, MutableAttributeSet attr) {
        String[] strings = CSS.parseStrings(value);
        int count = strings.length;
        int index = 0;
        short found = 0;
        int maxC = Math.min(3, count);
        while (index < maxC) {
            if ((found & 1) == 0 && isFontStyle(strings[index])) {
                css.addInternalCSSValue(attr, CSS$Attribute.FONT_STYLE, strings[index++]);
                found |= 1;
            } else if ((found & 2) == 0 && isFontVariant(strings[index])) {
                css.addInternalCSSValue(attr, CSS$Attribute.FONT_VARIANT, strings[index++]);
                found |= 2;
            } else if ((found & 4) == 0 && isFontWeight(strings[index])) {
                css.addInternalCSSValue(attr, CSS$Attribute.FONT_WEIGHT, strings[index++]);
                found |= 4;
            } else if (strings[index].equals("normal")) {
                index++;
            } else {
                break;
            }
        }
        if ((found & 1) == 0) {
            css.addInternalCSSValue(attr, CSS$Attribute.FONT_STYLE, "normal");
        }
        if ((found & 2) == 0) {
            css.addInternalCSSValue(attr, CSS$Attribute.FONT_VARIANT, "normal");
        }
        if ((found & 4) == 0) {
            css.addInternalCSSValue(attr, CSS$Attribute.FONT_WEIGHT, "normal");
        }
        if (index < count) {
            String fontSize = strings[index];
            int slashIndex = fontSize.indexOf('/');
            if (slashIndex != -1) {
                fontSize = fontSize.substring(0, slashIndex);
                strings[index] = strings[index].substring(slashIndex);
            } else {
                index++;
            }
            css.addInternalCSSValue(attr, CSS$Attribute.FONT_SIZE, fontSize);
        } else {
            css.addInternalCSSValue(attr, CSS$Attribute.FONT_SIZE, "medium");
        }
        if (index < count && strings[index].startsWith("/")) {
            String lineHeight = null;
            if (strings[index].equals("/")) {
                if (++index < count) {
                    lineHeight = strings[index++];
                }
            } else {
                lineHeight = strings[index++].substring(1);
            }
            if (lineHeight != null) {
                css.addInternalCSSValue(attr, CSS$Attribute.LINE_HEIGHT, lineHeight);
            } else {
                css.addInternalCSSValue(attr, CSS$Attribute.LINE_HEIGHT, "normal");
            }
        } else {
            css.addInternalCSSValue(attr, CSS$Attribute.LINE_HEIGHT, "normal");
        }
        if (index < count) {
            String family = strings[index++];
            while (index < count) {
                family += " " + strings[index++];
            }
            css.addInternalCSSValue(attr, CSS$Attribute.FONT_FAMILY, family);
        } else {
            css.addInternalCSSValue(attr, CSS$Attribute.FONT_FAMILY, "SansSerif");
        }
    }
    
    private static boolean isFontStyle(String string) {
        return (string.equals("italic") || string.equals("oblique"));
    }
    
    private static boolean isFontVariant(String string) {
        return (string.equals("small-caps"));
    }
    
    private static boolean isFontWeight(String string) {
        if (string.equals("bold") || string.equals("bolder") || string.equals("italic") || string.equals("lighter")) {
            return true;
        }
        return (string.length() == 3 && string.charAt(0) >= '1' && string.charAt(0) <= '9' && string.charAt(1) == '0' && string.charAt(2) == '0');
    }
}
