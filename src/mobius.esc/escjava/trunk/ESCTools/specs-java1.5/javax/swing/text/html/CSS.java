package javax.swing.text.html;

import java.awt.Color;
import java.awt.Font;
import java.io.*;
import java.net.URL;
import java.net.MalformedURLException;
import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Vector;
import javax.swing.SizeRequirements;
import javax.swing.text.*;

public class CSS implements Serializable {
    
    /*synthetic*/ static Hashtable access$500() {
        return htmlValueToCssValueMap;
    }
    
    /*synthetic*/ static Hashtable access$400() {
        return cssValueToInternalValueMap;
    }
    
    /*synthetic*/ static StyleSheet access$300(CSS x0, StyleSheet x1) {
        return x0.getStyleSheet(x1);
    }
    {
    }
    {
    }
    
    public CSS() {
        
        baseFontSize = baseFontSizeIndex + 1;
        valueConvertor = new Hashtable();
        valueConvertor.put(CSS$Attribute.FONT_SIZE, new CSS$FontSize(this));
        valueConvertor.put(CSS$Attribute.FONT_FAMILY, new CSS$FontFamily());
        valueConvertor.put(CSS$Attribute.FONT_WEIGHT, new CSS$FontWeight());
        valueConvertor.put(CSS$Attribute.BORDER_STYLE, new CSS$BorderStyle());
        Object cv = new CSS$ColorValue();
        valueConvertor.put(CSS$Attribute.COLOR, cv);
        valueConvertor.put(CSS$Attribute.BACKGROUND_COLOR, cv);
        valueConvertor.put(CSS$Attribute.BORDER_COLOR, cv);
        Object lv = new CSS$LengthValue();
        valueConvertor.put(CSS$Attribute.MARGIN_TOP, lv);
        valueConvertor.put(CSS$Attribute.MARGIN_BOTTOM, lv);
        valueConvertor.put(CSS$Attribute.MARGIN_LEFT, lv);
        valueConvertor.put(CSS$Attribute.MARGIN_LEFT_LTR, lv);
        valueConvertor.put(CSS$Attribute.MARGIN_LEFT_RTL, lv);
        valueConvertor.put(CSS$Attribute.MARGIN_RIGHT, lv);
        valueConvertor.put(CSS$Attribute.MARGIN_RIGHT_LTR, lv);
        valueConvertor.put(CSS$Attribute.MARGIN_RIGHT_RTL, lv);
        valueConvertor.put(CSS$Attribute.PADDING_TOP, lv);
        valueConvertor.put(CSS$Attribute.PADDING_BOTTOM, lv);
        valueConvertor.put(CSS$Attribute.PADDING_LEFT, lv);
        valueConvertor.put(CSS$Attribute.PADDING_RIGHT, lv);
        Object bv = new CSS$BorderWidthValue(null, 0);
        valueConvertor.put(CSS$Attribute.BORDER_WIDTH, lv);
        valueConvertor.put(CSS$Attribute.BORDER_TOP_WIDTH, bv);
        valueConvertor.put(CSS$Attribute.BORDER_BOTTOM_WIDTH, bv);
        valueConvertor.put(CSS$Attribute.BORDER_LEFT_WIDTH, bv);
        valueConvertor.put(CSS$Attribute.BORDER_RIGHT_WIDTH, bv);
        Object nlv = new CSS$LengthValue(true);
        valueConvertor.put(CSS$Attribute.TEXT_INDENT, nlv);
        valueConvertor.put(CSS$Attribute.WIDTH, lv);
        valueConvertor.put(CSS$Attribute.HEIGHT, lv);
        valueConvertor.put(CSS$Attribute.BORDER_SPACING, lv);
        Object sv = new CSS$StringValue();
        valueConvertor.put(CSS$Attribute.FONT_STYLE, sv);
        valueConvertor.put(CSS$Attribute.TEXT_DECORATION, sv);
        valueConvertor.put(CSS$Attribute.TEXT_ALIGN, sv);
        valueConvertor.put(CSS$Attribute.VERTICAL_ALIGN, sv);
        Object valueMapper = new CSS$CssValueMapper();
        valueConvertor.put(CSS$Attribute.LIST_STYLE_TYPE, valueMapper);
        valueConvertor.put(CSS$Attribute.BACKGROUND_IMAGE, new CSS$BackgroundImage());
        valueConvertor.put(CSS$Attribute.BACKGROUND_POSITION, new CSS$BackgroundPosition());
        valueConvertor.put(CSS$Attribute.BACKGROUND_REPEAT, valueMapper);
        valueConvertor.put(CSS$Attribute.BACKGROUND_ATTACHMENT, valueMapper);
        Object generic = new CSS$CssValue();
        int n = CSS$Attribute.allAttributes.length;
        for (int i = 0; i < n; i++) {
            CSS$Attribute key = CSS$Attribute.allAttributes[i];
            if (valueConvertor.get(key) == null) {
                valueConvertor.put(key, generic);
            }
        }
    }
    
    void setBaseFontSize(int sz) {
        if (sz < 1) baseFontSize = 0; else if (sz > 7) baseFontSize = 7; else baseFontSize = sz;
    }
    
    void setBaseFontSize(String size) {
        int relSize;
        int absSize;
        int diff;
        if (size != null) {
            if (size.startsWith("+")) {
                relSize = Integer.valueOf(size.substring(1)).intValue();
                setBaseFontSize(baseFontSize + relSize);
            } else if (size.startsWith("-")) {
                relSize = -Integer.valueOf(size.substring(1)).intValue();
                setBaseFontSize(baseFontSize + relSize);
            } else {
                setBaseFontSize(Integer.valueOf(size).intValue());
            }
        }
    }
    
    int getBaseFontSize() {
        return baseFontSize;
    }
    
    void addInternalCSSValue(MutableAttributeSet attr, CSS$Attribute key, String value) {
        if (key == CSS$Attribute.FONT) {
            CSS$ShorthandFontParser.parseShorthandFont(this, value, attr);
        } else if (key == CSS$Attribute.BACKGROUND) {
            CSS$ShorthandBackgroundParser.parseShorthandBackground(this, value, attr);
        } else if (key == CSS$Attribute.MARGIN) {
            CSS$ShorthandMarginParser.parseShorthandMargin(this, value, attr, CSS$Attribute.access$000());
        } else if (key == CSS$Attribute.PADDING) {
            CSS$ShorthandMarginParser.parseShorthandMargin(this, value, attr, CSS$Attribute.access$100());
        } else if (key == CSS$Attribute.BORDER_WIDTH) {
            CSS$ShorthandMarginParser.parseShorthandMargin(this, value, attr, CSS$Attribute.access$200());
        } else {
            Object iValue = getInternalCSSValue(key, value);
            if (iValue != null) {
                attr.addAttribute(key, iValue);
            }
        }
    }
    
    Object getInternalCSSValue(CSS$Attribute key, String value) {
        CSS$CssValue conv = (CSS$CssValue)(CSS$CssValue)valueConvertor.get(key);
        Object r = conv.parseCssValue(value);
        return r != null ? r : conv.parseCssValue(key.getDefaultValue());
    }
    
    CSS$Attribute styleConstantsKeyToCSSKey(StyleConstants sc) {
        return (CSS$Attribute)(CSS$Attribute)styleConstantToCssMap.get(sc);
    }
    
    Object styleConstantsValueToCSSValue(StyleConstants sc, Object styleValue) {
        Object cssKey = styleConstantsKeyToCSSKey(sc);
        if (cssKey != null) {
            CSS$CssValue conv = (CSS$CssValue)(CSS$CssValue)valueConvertor.get(cssKey);
            return conv.fromStyleConstants(sc, styleValue);
        }
        return null;
    }
    
    Object cssValueToStyleConstantsValue(StyleConstants key, Object value) {
        if (value instanceof CSS$CssValue) {
            return ((CSS$CssValue)(CSS$CssValue)value).toStyleConstants((StyleConstants)key, null);
        }
        return null;
    }
    
    Font getFont(StyleContext sc, AttributeSet a, int defaultSize, StyleSheet ss) {
        ss = getStyleSheet(ss);
        int size = getFontSize(a, defaultSize, ss);
        CSS$StringValue vAlignV = (CSS$StringValue)(CSS$StringValue)a.getAttribute(CSS$Attribute.VERTICAL_ALIGN);
        if (vAlignV != null) {
            String vAlign = vAlignV.toString();
            if ((vAlign.indexOf("sup") >= 0) || (vAlign.indexOf("sub") >= 0)) {
                size -= 2;
            }
        }
        CSS$FontFamily familyValue = (CSS$FontFamily)(CSS$FontFamily)a.getAttribute(CSS$Attribute.FONT_FAMILY);
        String family = (familyValue != null) ? familyValue.getValue() : "SansSerif";
        int style = Font.PLAIN;
        CSS$FontWeight weightValue = (CSS$FontWeight)(CSS$FontWeight)a.getAttribute(CSS$Attribute.FONT_WEIGHT);
        if ((weightValue != null) && (weightValue.getValue() > 400)) {
            style |= Font.BOLD;
        }
        Object fs = a.getAttribute(CSS$Attribute.FONT_STYLE);
        if ((fs != null) && (fs.toString().indexOf("italic") >= 0)) {
            style |= Font.ITALIC;
        }
        if (family.equalsIgnoreCase("monospace")) {
            family = "Monospaced";
        }
        Font f = sc.getFont(family, style, size);
        if (f == null || (f.getFamily().equals("Dialog") && !family.equalsIgnoreCase("Dialog"))) {
            family = "SansSerif";
            f = sc.getFont(family, style, size);
        }
        return f;
    }
    
    static int getFontSize(AttributeSet attr, int defaultSize, StyleSheet ss) {
        CSS$FontSize sizeValue = (CSS$FontSize)(CSS$FontSize)attr.getAttribute(CSS$Attribute.FONT_SIZE);
        return (sizeValue != null) ? (int)sizeValue.getValue(attr, ss) : defaultSize;
    }
    
    Color getColor(AttributeSet a, CSS$Attribute key) {
        CSS$ColorValue cv = (CSS$ColorValue)(CSS$ColorValue)a.getAttribute(key);
        if (cv != null) {
            return cv.getValue();
        }
        return null;
    }
    
    float getPointSize(String size, StyleSheet ss) {
        int relSize;
        int absSize;
        int diff;
        int index;
        ss = getStyleSheet(ss);
        if (size != null) {
            if (size.startsWith("+")) {
                relSize = Integer.valueOf(size.substring(1)).intValue();
                return getPointSize(baseFontSize + relSize, ss);
            } else if (size.startsWith("-")) {
                relSize = -Integer.valueOf(size.substring(1)).intValue();
                return getPointSize(baseFontSize + relSize, ss);
            } else {
                absSize = Integer.valueOf(size).intValue();
                return getPointSize(absSize, ss);
            }
        }
        return 0;
    }
    
    float getLength(AttributeSet a, CSS$Attribute key, StyleSheet ss) {
        ss = getStyleSheet(ss);
        CSS$LengthValue lv = (CSS$LengthValue)(CSS$LengthValue)a.getAttribute(key);
        boolean isW3CLengthUnits = (ss == null) ? false : ss.isW3CLengthUnits();
        float len = (lv != null) ? lv.getValue(isW3CLengthUnits) : 0;
        return len;
    }
    
    AttributeSet translateHTMLToCSS(AttributeSet htmlAttrSet) {
        MutableAttributeSet cssAttrSet = new SimpleAttributeSet();
        Element elem = (Element)(Element)htmlAttrSet;
        HTML$Tag tag = getHTMLTag(htmlAttrSet);
        if ((tag == HTML$Tag.TD) || (tag == HTML$Tag.TH)) {
            AttributeSet tableAttr = elem.getParentElement().getParentElement().getAttributes();
            translateAttribute(HTML$Attribute.BORDER, tableAttr, cssAttrSet);
            String pad = (String)(String)tableAttr.getAttribute(HTML$Attribute.CELLPADDING);
            if (pad != null) {
                CSS$LengthValue v = (CSS$LengthValue)(CSS$LengthValue)getInternalCSSValue(CSS$Attribute.PADDING_TOP, pad);
                v.span = (v.span < 0) ? 0 : v.span;
                cssAttrSet.addAttribute(CSS$Attribute.PADDING_TOP, v);
                cssAttrSet.addAttribute(CSS$Attribute.PADDING_BOTTOM, v);
                cssAttrSet.addAttribute(CSS$Attribute.PADDING_LEFT, v);
                cssAttrSet.addAttribute(CSS$Attribute.PADDING_RIGHT, v);
            }
        }
        if (elem.isLeaf()) {
            translateEmbeddedAttributes(htmlAttrSet, cssAttrSet);
        } else {
            translateAttributes(tag, htmlAttrSet, cssAttrSet);
        }
        if (tag == HTML$Tag.CAPTION) {
            Object v = htmlAttrSet.getAttribute(HTML$Attribute.ALIGN);
            if ((v != null) && (v.equals("top") || v.equals("bottom"))) {
                cssAttrSet.addAttribute(CSS$Attribute.CAPTION_SIDE, v);
                cssAttrSet.removeAttribute(CSS$Attribute.TEXT_ALIGN);
            } else {
                v = htmlAttrSet.getAttribute(HTML$Attribute.VALIGN);
                if (v != null) {
                    cssAttrSet.addAttribute(CSS$Attribute.CAPTION_SIDE, v);
                }
            }
        }
        return cssAttrSet;
    }
    private static final Hashtable attributeMap = new Hashtable();
    private static final Hashtable valueMap = new Hashtable();
    private static final Hashtable htmlAttrToCssAttrMap = new Hashtable(20);
    private static final Hashtable styleConstantToCssMap = new Hashtable(17);
    private static final Hashtable htmlValueToCssValueMap = new Hashtable(8);
    private static final Hashtable cssValueToInternalValueMap = new Hashtable(13);
    static {
        for (int i = 0; i < CSS$Attribute.allAttributes.length; i++) {
            attributeMap.put(CSS$Attribute.allAttributes[i].toString(), CSS$Attribute.allAttributes[i]);
        }
        for (int i = 0; i < CSS$Value.allValues.length; i++) {
            valueMap.put(CSS$Value.allValues[i].toString(), CSS$Value.allValues[i]);
        }
        htmlAttrToCssAttrMap.put(HTML$Attribute.COLOR, new CSS$Attribute[]{CSS$Attribute.COLOR});
        htmlAttrToCssAttrMap.put(HTML$Attribute.TEXT, new CSS$Attribute[]{CSS$Attribute.COLOR});
        htmlAttrToCssAttrMap.put(HTML$Attribute.CLEAR, new CSS$Attribute[]{CSS$Attribute.CLEAR});
        htmlAttrToCssAttrMap.put(HTML$Attribute.BACKGROUND, new CSS$Attribute[]{CSS$Attribute.BACKGROUND_IMAGE});
        htmlAttrToCssAttrMap.put(HTML$Attribute.BGCOLOR, new CSS$Attribute[]{CSS$Attribute.BACKGROUND_COLOR});
        htmlAttrToCssAttrMap.put(HTML$Attribute.WIDTH, new CSS$Attribute[]{CSS$Attribute.WIDTH});
        htmlAttrToCssAttrMap.put(HTML$Attribute.HEIGHT, new CSS$Attribute[]{CSS$Attribute.HEIGHT});
        htmlAttrToCssAttrMap.put(HTML$Attribute.BORDER, new CSS$Attribute[]{CSS$Attribute.BORDER_TOP_WIDTH, CSS$Attribute.BORDER_RIGHT_WIDTH, CSS$Attribute.BORDER_BOTTOM_WIDTH, CSS$Attribute.BORDER_LEFT_WIDTH});
        htmlAttrToCssAttrMap.put(HTML$Attribute.CELLPADDING, new CSS$Attribute[]{CSS$Attribute.PADDING});
        htmlAttrToCssAttrMap.put(HTML$Attribute.CELLSPACING, new CSS$Attribute[]{CSS$Attribute.BORDER_SPACING});
        htmlAttrToCssAttrMap.put(HTML$Attribute.MARGINWIDTH, new CSS$Attribute[]{CSS$Attribute.MARGIN_LEFT, CSS$Attribute.MARGIN_RIGHT});
        htmlAttrToCssAttrMap.put(HTML$Attribute.MARGINHEIGHT, new CSS$Attribute[]{CSS$Attribute.MARGIN_TOP, CSS$Attribute.MARGIN_BOTTOM});
        htmlAttrToCssAttrMap.put(HTML$Attribute.HSPACE, new CSS$Attribute[]{CSS$Attribute.PADDING_LEFT, CSS$Attribute.PADDING_RIGHT});
        htmlAttrToCssAttrMap.put(HTML$Attribute.VSPACE, new CSS$Attribute[]{CSS$Attribute.PADDING_BOTTOM, CSS$Attribute.PADDING_TOP});
        htmlAttrToCssAttrMap.put(HTML$Attribute.FACE, new CSS$Attribute[]{CSS$Attribute.FONT_FAMILY});
        htmlAttrToCssAttrMap.put(HTML$Attribute.SIZE, new CSS$Attribute[]{CSS$Attribute.FONT_SIZE});
        htmlAttrToCssAttrMap.put(HTML$Attribute.VALIGN, new CSS$Attribute[]{CSS$Attribute.VERTICAL_ALIGN});
        htmlAttrToCssAttrMap.put(HTML$Attribute.ALIGN, new CSS$Attribute[]{CSS$Attribute.VERTICAL_ALIGN, CSS$Attribute.TEXT_ALIGN, CSS$Attribute.FLOAT});
        htmlAttrToCssAttrMap.put(HTML$Attribute.TYPE, new CSS$Attribute[]{CSS$Attribute.LIST_STYLE_TYPE});
        htmlAttrToCssAttrMap.put(HTML$Attribute.NOWRAP, new CSS$Attribute[]{CSS$Attribute.WHITE_SPACE});
        styleConstantToCssMap.put(StyleConstants.FontFamily, CSS$Attribute.FONT_FAMILY);
        styleConstantToCssMap.put(StyleConstants.FontSize, CSS$Attribute.FONT_SIZE);
        styleConstantToCssMap.put(StyleConstants.Bold, CSS$Attribute.FONT_WEIGHT);
        styleConstantToCssMap.put(StyleConstants.Italic, CSS$Attribute.FONT_STYLE);
        styleConstantToCssMap.put(StyleConstants.Underline, CSS$Attribute.TEXT_DECORATION);
        styleConstantToCssMap.put(StyleConstants.StrikeThrough, CSS$Attribute.TEXT_DECORATION);
        styleConstantToCssMap.put(StyleConstants.Superscript, CSS$Attribute.VERTICAL_ALIGN);
        styleConstantToCssMap.put(StyleConstants.Subscript, CSS$Attribute.VERTICAL_ALIGN);
        styleConstantToCssMap.put(StyleConstants.Foreground, CSS$Attribute.COLOR);
        styleConstantToCssMap.put(StyleConstants.Background, CSS$Attribute.BACKGROUND_COLOR);
        styleConstantToCssMap.put(StyleConstants.FirstLineIndent, CSS$Attribute.TEXT_INDENT);
        styleConstantToCssMap.put(StyleConstants.LeftIndent, CSS$Attribute.MARGIN_LEFT);
        styleConstantToCssMap.put(StyleConstants.RightIndent, CSS$Attribute.MARGIN_RIGHT);
        styleConstantToCssMap.put(StyleConstants.SpaceAbove, CSS$Attribute.MARGIN_TOP);
        styleConstantToCssMap.put(StyleConstants.SpaceBelow, CSS$Attribute.MARGIN_BOTTOM);
        styleConstantToCssMap.put(StyleConstants.Alignment, CSS$Attribute.TEXT_ALIGN);
        htmlValueToCssValueMap.put("disc", CSS$Value.DISC);
        htmlValueToCssValueMap.put("square", CSS$Value.SQUARE);
        htmlValueToCssValueMap.put("circle", CSS$Value.CIRCLE);
        htmlValueToCssValueMap.put("1", CSS$Value.DECIMAL);
        htmlValueToCssValueMap.put("a", CSS$Value.LOWER_ALPHA);
        htmlValueToCssValueMap.put("A", CSS$Value.UPPER_ALPHA);
        htmlValueToCssValueMap.put("i", CSS$Value.LOWER_ROMAN);
        htmlValueToCssValueMap.put("I", CSS$Value.UPPER_ROMAN);
        cssValueToInternalValueMap.put("none", CSS$Value.NONE);
        cssValueToInternalValueMap.put("disc", CSS$Value.DISC);
        cssValueToInternalValueMap.put("square", CSS$Value.SQUARE);
        cssValueToInternalValueMap.put("circle", CSS$Value.CIRCLE);
        cssValueToInternalValueMap.put("decimal", CSS$Value.DECIMAL);
        cssValueToInternalValueMap.put("lower-roman", CSS$Value.LOWER_ROMAN);
        cssValueToInternalValueMap.put("upper-roman", CSS$Value.UPPER_ROMAN);
        cssValueToInternalValueMap.put("lower-alpha", CSS$Value.LOWER_ALPHA);
        cssValueToInternalValueMap.put("upper-alpha", CSS$Value.UPPER_ALPHA);
        cssValueToInternalValueMap.put("repeat", CSS$Value.BACKGROUND_REPEAT);
        cssValueToInternalValueMap.put("no-repeat", CSS$Value.BACKGROUND_NO_REPEAT);
        cssValueToInternalValueMap.put("repeat-x", CSS$Value.BACKGROUND_REPEAT_X);
        cssValueToInternalValueMap.put("repeat-y", CSS$Value.BACKGROUND_REPEAT_Y);
        cssValueToInternalValueMap.put("scroll", CSS$Value.BACKGROUND_SCROLL);
        cssValueToInternalValueMap.put("fixed", CSS$Value.BACKGROUND_FIXED);
        Object[] keys = CSS$Attribute.allAttributes;
        try {
            for (int i = 0; i < keys.length; i++) {
                StyleContext.registerStaticAttributeKey(keys[i]);
            }
        } catch (Throwable e) {
            e.printStackTrace();
        }
        keys = CSS$Value.allValues;
        try {
            for (int i = 0; i < keys.length; i++) {
                StyleContext.registerStaticAttributeKey(keys[i]);
            }
        } catch (Throwable e) {
            e.printStackTrace();
        }
    }
    
    public static CSS$Attribute[] getAllAttributeKeys() {
        CSS$Attribute[] keys = new CSS$Attribute[CSS$Attribute.allAttributes.length];
        System.arraycopy(CSS$Attribute.allAttributes, 0, keys, 0, CSS$Attribute.allAttributes.length);
        return keys;
    }
    
    public static final CSS$Attribute getAttribute(String name) {
        return (CSS$Attribute)(CSS$Attribute)attributeMap.get(name);
    }
    
    static final CSS$Value getValue(String name) {
        return (CSS$Value)(CSS$Value)valueMap.get(name);
    }
    
    static URL getURL(URL base, String cssString) {
        if (cssString == null) {
            return null;
        }
        if (cssString.startsWith("url(") && cssString.endsWith(")")) {
            cssString = cssString.substring(4, cssString.length() - 1);
        }
        try {
            URL url = new URL(cssString);
            if (url != null) {
                return url;
            }
        } catch (MalformedURLException mue) {
        }
        if (base != null) {
            try {
                URL url = new URL(base, cssString);
                return url;
            } catch (MalformedURLException muee) {
            }
        }
        return null;
    }
    
    static String colorToHex(Color color) {
        String colorstr = new String("#");
        String str = Integer.toHexString(color.getRed());
        if (str.length() > 2) str = str.substring(0, 2); else if (str.length() < 2) colorstr += "0" + str; else colorstr += str;
        str = Integer.toHexString(color.getGreen());
        if (str.length() > 2) str = str.substring(0, 2); else if (str.length() < 2) colorstr += "0" + str; else colorstr += str;
        str = Integer.toHexString(color.getBlue());
        if (str.length() > 2) str = str.substring(0, 2); else if (str.length() < 2) colorstr += "0" + str; else colorstr += str;
        return colorstr;
    }
    
    static final Color hexToColor(String value) {
        String digits;
        int n = value.length();
        if (value.startsWith("#")) {
            digits = value.substring(1, Math.min(value.length(), 7));
        } else {
            digits = value;
        }
        String hstr = "0x" + digits;
        Color c;
        try {
            c = Color.decode(hstr);
        } catch (NumberFormatException nfe) {
            c = null;
        }
        return c;
    }
    
    static Color stringToColor(String str) {
        Color color = null;
        if (str.length() == 0) color = Color.black; else if (str.startsWith("rgb(")) {
            color = parseRGB(str);
        } else if (str.charAt(0) == '#') color = hexToColor(str); else if (str.equalsIgnoreCase("Black")) color = hexToColor("#000000"); else if (str.equalsIgnoreCase("Silver")) color = hexToColor("#C0C0C0"); else if (str.equalsIgnoreCase("Gray")) color = hexToColor("#808080"); else if (str.equalsIgnoreCase("White")) color = hexToColor("#FFFFFF"); else if (str.equalsIgnoreCase("Maroon")) color = hexToColor("#800000"); else if (str.equalsIgnoreCase("Red")) color = hexToColor("#FF0000"); else if (str.equalsIgnoreCase("Purple")) color = hexToColor("#800080"); else if (str.equalsIgnoreCase("Fuchsia")) color = hexToColor("#FF00FF"); else if (str.equalsIgnoreCase("Green")) color = hexToColor("#008000"); else if (str.equalsIgnoreCase("Lime")) color = hexToColor("#00FF00"); else if (str.equalsIgnoreCase("Olive")) color = hexToColor("#808000"); else if (str.equalsIgnoreCase("Yellow")) color = hexToColor("#FFFF00"); else if (str.equalsIgnoreCase("Navy")) color = hexToColor("#000080"); else if (str.equalsIgnoreCase("Blue")) color = hexToColor("#0000FF"); else if (str.equalsIgnoreCase("Teal")) color = hexToColor("#008080"); else if (str.equalsIgnoreCase("Aqua")) color = hexToColor("#00FFFF"); else color = hexToColor(str);
        return color;
    }
    
    private static Color parseRGB(String string) {
        int[] index = new int[1];
        index[0] = 4;
        int red = getColorComponent(string, index);
        int green = getColorComponent(string, index);
        int blue = getColorComponent(string, index);
        return new Color(red, green, blue);
    }
    
    private static int getColorComponent(String string, int[] index) {
        int length = string.length();
        char aChar;
        while (index[0] < length && (aChar = string.charAt(index[0])) != '-' && !Character.isDigit(aChar) && aChar != '.') {
            index[0]++;
        }
        int start = index[0];
        if (start < length && string.charAt(index[0]) == '-') {
            index[0]++;
        }
        while (index[0] < length && Character.isDigit(string.charAt(index[0]))) {
            index[0]++;
        }
        if (index[0] < length && string.charAt(index[0]) == '.') {
            index[0]++;
            while (index[0] < length && Character.isDigit(string.charAt(index[0]))) {
                index[0]++;
            }
        }
        if (start != index[0]) {
            try {
                float value = Float.parseFloat(string.substring(start, index[0]));
                if (index[0] < length && string.charAt(index[0]) == '%') {
                    index[0]++;
                    value = value * 255.0F / 100.0F;
                }
                return Math.min(255, Math.max(0, (int)value));
            } catch (NumberFormatException nfe) {
            }
        }
        return 0;
    }
    
    static int getIndexOfSize(float pt, int[] sizeMap) {
        for (int i = 0; i < sizeMap.length; i++) if (pt <= sizeMap[i]) return i + 1;
        return sizeMap.length;
    }
    
    static int getIndexOfSize(float pt, StyleSheet ss) {
        int[] sizeMap = (ss != null) ? ss.getSizeMap() : StyleSheet.sizeMapDefault;
        return getIndexOfSize(pt, sizeMap);
    }
    
    static String[] parseStrings(String value) {
        int current;
        int last;
        int length = (value == null) ? 0 : value.length();
        Vector temp = new Vector(4);
        current = 0;
        while (current < length) {
            while (current < length && Character.isWhitespace(value.charAt(current))) {
                current++;
            }
            last = current;
            while (current < length && !Character.isWhitespace(value.charAt(current))) {
                current++;
            }
            if (last != current) {
                temp.addElement(value.substring(last, current));
            }
            current++;
        }
        String[] retValue = new String[temp.size()];
        temp.copyInto(retValue);
        return retValue;
    }
    
    float getPointSize(int index, StyleSheet ss) {
        ss = getStyleSheet(ss);
        int[] sizeMap = (ss != null) ? ss.getSizeMap() : StyleSheet.sizeMapDefault;
        --index;
        if (index < 0) return sizeMap[0]; else if (index > sizeMap.length - 1) return sizeMap[sizeMap.length - 1]; else return sizeMap[index];
    }
    
    private void translateEmbeddedAttributes(AttributeSet htmlAttrSet, MutableAttributeSet cssAttrSet) {
        Enumeration keys = htmlAttrSet.getAttributeNames();
        if (htmlAttrSet.getAttribute(StyleConstants.NameAttribute) == HTML$Tag.HR) {
            translateAttributes(HTML$Tag.HR, htmlAttrSet, cssAttrSet);
        }
        while (keys.hasMoreElements()) {
            Object key = keys.nextElement();
            if (key instanceof HTML$Tag) {
                HTML$Tag tag = (HTML$Tag)(HTML$Tag)key;
                Object o = htmlAttrSet.getAttribute(tag);
                if (o != null && o instanceof AttributeSet) {
                    translateAttributes(tag, (AttributeSet)(AttributeSet)o, cssAttrSet);
                }
            } else if (key instanceof CSS$Attribute) {
                cssAttrSet.addAttribute(key, htmlAttrSet.getAttribute(key));
            }
        }
    }
    
    private void translateAttributes(HTML$Tag tag, AttributeSet htmlAttrSet, MutableAttributeSet cssAttrSet) {
        Enumeration names = htmlAttrSet.getAttributeNames();
        while (names.hasMoreElements()) {
            Object name = names.nextElement();
            if (name instanceof HTML$Attribute) {
                HTML$Attribute key = (HTML$Attribute)(HTML$Attribute)name;
                if (key == HTML$Attribute.ALIGN) {
                    String htmlAttrValue = (String)(String)htmlAttrSet.getAttribute(HTML$Attribute.ALIGN);
                    if (htmlAttrValue != null) {
                        CSS$Attribute cssAttr = getCssAlignAttribute(tag, htmlAttrSet);
                        if (cssAttr != null) {
                            Object o = getCssValue(cssAttr, htmlAttrValue);
                            if (o != null) {
                                cssAttrSet.addAttribute(cssAttr, o);
                            }
                        }
                    }
                } else {
                    if (key == HTML$Attribute.SIZE && !isHTMLFontTag(tag)) {
                        continue;
                    }
                    translateAttribute(key, htmlAttrSet, cssAttrSet);
                }
            } else if (name instanceof CSS$Attribute) {
                cssAttrSet.addAttribute(name, htmlAttrSet.getAttribute(name));
            }
        }
    }
    
    private void translateAttribute(HTML$Attribute key, AttributeSet htmlAttrSet, MutableAttributeSet cssAttrSet) {
        CSS$Attribute[] cssAttrList = getCssAttribute(key);
        String htmlAttrValue = (String)(String)htmlAttrSet.getAttribute(key);
        if (cssAttrList == null || htmlAttrValue == null) {
            return;
        }
        for (int i = 0; i < cssAttrList.length; i++) {
            Object o = getCssValue(cssAttrList[i], htmlAttrValue);
            if (o != null) {
                cssAttrSet.addAttribute(cssAttrList[i], o);
            }
        }
    }
    
    Object getCssValue(CSS$Attribute cssAttr, String htmlAttrValue) {
        CSS$CssValue value = (CSS$CssValue)(CSS$CssValue)valueConvertor.get(cssAttr);
        Object o = value.parseHtmlValue(htmlAttrValue);
        return o;
    }
    
    private CSS$Attribute[] getCssAttribute(HTML$Attribute hAttr) {
        return (CSS$Attribute[])(CSS$Attribute[])htmlAttrToCssAttrMap.get(hAttr);
    }
    
    private CSS$Attribute getCssAlignAttribute(HTML$Tag tag, AttributeSet htmlAttrSet) {
        return CSS$Attribute.TEXT_ALIGN;
    }
    
    private HTML$Tag getHTMLTag(AttributeSet htmlAttrSet) {
        Object o = htmlAttrSet.getAttribute(StyleConstants.NameAttribute);
        if (o instanceof HTML$Tag) {
            HTML$Tag tag = (HTML$Tag)(HTML$Tag)o;
            return tag;
        }
        return null;
    }
    
    private boolean isHTMLFontTag(HTML$Tag tag) {
        return (tag != null && ((tag == HTML$Tag.FONT) || (tag == HTML$Tag.BASEFONT)));
    }
    
    private boolean isFloater(String alignValue) {
        return (alignValue.equals("left") || alignValue.equals("right"));
    }
    
    private boolean validTextAlignValue(String alignValue) {
        return (isFloater(alignValue) || alignValue.equals("center"));
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    
    static SizeRequirements calculateTiledRequirements(CSS$LayoutIterator iter, SizeRequirements r) {
        long minimum = 0;
        long maximum = 0;
        long preferred = 0;
        int lastMargin = 0;
        int totalSpacing = 0;
        int n = iter.getCount();
        for (int i = 0; i < n; i++) {
            iter.setIndex(i);
            int margin0 = lastMargin;
            int margin1 = (int)iter.getLeadingCollapseSpan();
            totalSpacing += Math.max(margin0, margin1);
            ;
            preferred += (int)iter.getPreferredSpan(0);
            minimum += iter.getMinimumSpan(0);
            maximum += iter.getMaximumSpan(0);
            lastMargin = (int)iter.getTrailingCollapseSpan();
        }
        totalSpacing += lastMargin;
        totalSpacing += 2 * iter.getBorderWidth();
        minimum += totalSpacing;
        preferred += totalSpacing;
        maximum += totalSpacing;
        if (r == null) {
            r = new SizeRequirements();
        }
        r.minimum = (minimum > Integer.MAX_VALUE) ? Integer.MAX_VALUE : (int)minimum;
        r.preferred = (preferred > Integer.MAX_VALUE) ? Integer.MAX_VALUE : (int)preferred;
        r.maximum = (maximum > Integer.MAX_VALUE) ? Integer.MAX_VALUE : (int)maximum;
        return r;
    }
    
    static void calculateTiledLayout(CSS$LayoutIterator iter, int targetSpan) {
        long preferred = 0;
        long currentPreferred = 0;
        int lastMargin = 0;
        int totalSpacing = 0;
        int n = iter.getCount();
        int adjustmentWeightsCount = CSS$LayoutIterator.WorstAdjustmentWeight + 1;
        long[] gain = new long[adjustmentWeightsCount];
        long[] loss = new long[adjustmentWeightsCount];
        for (int i = 0; i < adjustmentWeightsCount; i++) {
            gain[i] = loss[i] = 0;
        }
        for (int i = 0; i < n; i++) {
            iter.setIndex(i);
            int margin0 = lastMargin;
            int margin1 = (int)iter.getLeadingCollapseSpan();
            iter.setOffset(Math.max(margin0, margin1));
            totalSpacing += iter.getOffset();
            currentPreferred = (long)iter.getPreferredSpan(targetSpan);
            iter.setSpan((int)currentPreferred);
            preferred += currentPreferred;
            gain[iter.getAdjustmentWeight()] += (long)iter.getMaximumSpan(targetSpan) - currentPreferred;
            loss[iter.getAdjustmentWeight()] += currentPreferred - (long)iter.getMinimumSpan(targetSpan);
            lastMargin = (int)iter.getTrailingCollapseSpan();
        }
        totalSpacing += lastMargin;
        totalSpacing += 2 * iter.getBorderWidth();
        for (int i = 1; i < adjustmentWeightsCount; i++) {
            gain[i] += gain[i - 1];
            loss[i] += loss[i - 1];
        }
        int allocated = targetSpan - totalSpacing;
        long desiredAdjustment = allocated - preferred;
        long[] adjustmentsArray = (desiredAdjustment > 0) ? gain : loss;
        desiredAdjustment = Math.abs(desiredAdjustment);
        int adjustmentLevel = 0;
        for (; adjustmentLevel <= CSS$LayoutIterator.WorstAdjustmentWeight; adjustmentLevel++) {
            if (adjustmentsArray[adjustmentLevel] >= desiredAdjustment) {
                break;
            }
        }
        float adjustmentFactor = 0.0F;
        if (adjustmentLevel <= CSS$LayoutIterator.WorstAdjustmentWeight) {
            desiredAdjustment -= (adjustmentLevel > 0) ? adjustmentsArray[adjustmentLevel - 1] : 0;
            if (desiredAdjustment != 0) {
                float maximumAdjustment = adjustmentsArray[adjustmentLevel] - ((adjustmentLevel > 0) ? adjustmentsArray[adjustmentLevel - 1] : 0);
                adjustmentFactor = desiredAdjustment / maximumAdjustment;
            }
        }
        int totalOffset = (int)iter.getBorderWidth();
        ;
        for (int i = 0; i < n; i++) {
            iter.setIndex(i);
            iter.setOffset(iter.getOffset() + totalOffset);
            if (iter.getAdjustmentWeight() < adjustmentLevel) {
                iter.setSpan((int)((allocated > preferred) ? Math.floor(iter.getMaximumSpan(targetSpan)) : Math.ceil(iter.getMinimumSpan(targetSpan))));
            } else if (iter.getAdjustmentWeight() == adjustmentLevel) {
                int availableSpan = (allocated > preferred) ? (int)iter.getMaximumSpan(targetSpan) - iter.getSpan() : iter.getSpan() - (int)iter.getMinimumSpan(targetSpan);
                int adj = (int)Math.floor(adjustmentFactor * availableSpan);
                iter.setSpan(iter.getSpan() + ((allocated > preferred) ? adj : -adj));
            }
            totalOffset = (int)Math.min((long)iter.getOffset() + (long)iter.getSpan(), Integer.MAX_VALUE);
        }
        int roundError = targetSpan - totalOffset - (int)iter.getTrailingCollapseSpan() - (int)iter.getBorderWidth();
        int adj = (roundError > 0) ? 1 : -1;
        roundError *= adj;
        boolean canAdjust = true;
        while (roundError > 0 && canAdjust) {
            canAdjust = false;
            int offsetAdjust = 0;
            for (int i = 0; i < n; i++) {
                iter.setIndex(i);
                iter.setOffset(iter.getOffset() + offsetAdjust);
                int curSpan = iter.getSpan();
                if (roundError > 0) {
                    int boundGap = (adj > 0) ? (int)Math.floor(iter.getMaximumSpan(targetSpan)) - curSpan : curSpan - (int)Math.ceil(iter.getMinimumSpan(targetSpan));
                    if (boundGap >= 1) {
                        canAdjust = true;
                        iter.setSpan(curSpan + adj);
                        offsetAdjust += adj;
                        roundError--;
                    }
                }
            }
        }
    }
    {
    }
    
    private void writeObject(java.io.ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        Enumeration keys = valueConvertor.keys();
        s.writeInt(valueConvertor.size());
        if (keys != null) {
            while (keys.hasMoreElements()) {
                Object key = keys.nextElement();
                Object value = valueConvertor.get(key);
                if (!(key instanceof Serializable) && (key = StyleContext.getStaticAttributeKey(key)) == null) {
                    key = null;
                    value = null;
                } else if (!(value instanceof Serializable) && (value = StyleContext.getStaticAttributeKey(value)) == null) {
                    key = null;
                    value = null;
                }
                s.writeObject(key);
                s.writeObject(value);
            }
        }
    }
    
    private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException {
        s.defaultReadObject();
        int numValues = s.readInt();
        valueConvertor = new Hashtable(Math.max(1, numValues));
        while (numValues-- > 0) {
            Object key = s.readObject();
            Object value = s.readObject();
            Object staticKey = StyleContext.getStaticAttribute(key);
            if (staticKey != null) {
                key = staticKey;
            }
            Object staticValue = StyleContext.getStaticAttribute(value);
            if (staticValue != null) {
                value = staticValue;
            }
            if (key != null && value != null) {
                valueConvertor.put(key, value);
            }
        }
    }
    
    private StyleSheet getStyleSheet(StyleSheet ss) {
        if (ss != null) {
            styleSheet = ss;
        }
        return styleSheet;
    }
    private transient Hashtable valueConvertor;
    private int baseFontSize;
    private transient StyleSheet styleSheet = null;
    static int baseFontSizeIndex = 3;
}
