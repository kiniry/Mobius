package javax.swing.text.html;

import java.io.*;
import javax.swing.text.*;

public final class CSS$Attribute {
    
    /*synthetic*/ static CSS.Attribute[] access$200() {
        return ALL_BORDER_WIDTHS;
    }
    
    /*synthetic*/ static CSS.Attribute[] access$100() {
        return ALL_PADDING;
    }
    
    /*synthetic*/ static CSS.Attribute[] access$000() {
        return ALL_MARGINS;
    }
    
    private CSS$Attribute(String name, String defaultValue, boolean inherited) {
        
        this.name = name;
        this.defaultValue = defaultValue;
        this.inherited = inherited;
    }
    
    public String toString() {
        return name;
    }
    
    public String getDefaultValue() {
        return defaultValue;
    }
    
    public boolean isInherited() {
        return inherited;
    }
    private String name;
    private String defaultValue;
    private boolean inherited;
    public static final CSS$Attribute BACKGROUND = new CSS$Attribute("background", null, false);
    public static final CSS$Attribute BACKGROUND_ATTACHMENT = new CSS$Attribute("background-attachment", "scroll", false);
    public static final CSS$Attribute BACKGROUND_COLOR = new CSS$Attribute("background-color", "transparent", false);
    public static final CSS$Attribute BACKGROUND_IMAGE = new CSS$Attribute("background-image", "none", false);
    public static final CSS$Attribute BACKGROUND_POSITION = new CSS$Attribute("background-position", null, false);
    public static final CSS$Attribute BACKGROUND_REPEAT = new CSS$Attribute("background-repeat", "repeat", false);
    public static final CSS$Attribute BORDER = new CSS$Attribute("border", null, false);
    public static final CSS$Attribute BORDER_BOTTOM = new CSS$Attribute("border-bottom", null, false);
    public static final CSS$Attribute BORDER_BOTTOM_WIDTH = new CSS$Attribute("border-bottom-width", "medium", false);
    public static final CSS$Attribute BORDER_COLOR = new CSS$Attribute("border-color", "black", false);
    public static final CSS$Attribute BORDER_LEFT = new CSS$Attribute("border-left", null, false);
    public static final CSS$Attribute BORDER_LEFT_WIDTH = new CSS$Attribute("border-left-width", "medium", false);
    public static final CSS$Attribute BORDER_RIGHT = new CSS$Attribute("border-right", null, false);
    public static final CSS$Attribute BORDER_RIGHT_WIDTH = new CSS$Attribute("border-right-width", "medium", false);
    public static final CSS$Attribute BORDER_STYLE = new CSS$Attribute("border-style", "none", false);
    public static final CSS$Attribute BORDER_TOP = new CSS$Attribute("border-top", null, false);
    public static final CSS$Attribute BORDER_TOP_WIDTH = new CSS$Attribute("border-top-width", "medium", false);
    public static final CSS$Attribute BORDER_WIDTH = new CSS$Attribute("border-width", "medium", false);
    public static final CSS$Attribute CLEAR = new CSS$Attribute("clear", "none", false);
    public static final CSS$Attribute COLOR = new CSS$Attribute("color", "black", true);
    public static final CSS$Attribute DISPLAY = new CSS$Attribute("display", "block", false);
    public static final CSS$Attribute FLOAT = new CSS$Attribute("float", "none", false);
    public static final CSS$Attribute FONT = new CSS$Attribute("font", null, true);
    public static final CSS$Attribute FONT_FAMILY = new CSS$Attribute("font-family", null, true);
    public static final CSS$Attribute FONT_SIZE = new CSS$Attribute("font-size", "medium", true);
    public static final CSS$Attribute FONT_STYLE = new CSS$Attribute("font-style", "normal", true);
    public static final CSS$Attribute FONT_VARIANT = new CSS$Attribute("font-variant", "normal", true);
    public static final CSS$Attribute FONT_WEIGHT = new CSS$Attribute("font-weight", "normal", true);
    public static final CSS$Attribute HEIGHT = new CSS$Attribute("height", "auto", false);
    public static final CSS$Attribute LETTER_SPACING = new CSS$Attribute("letter-spacing", "normal", true);
    public static final CSS$Attribute LINE_HEIGHT = new CSS$Attribute("line-height", "normal", true);
    public static final CSS$Attribute LIST_STYLE = new CSS$Attribute("list-style", null, true);
    public static final CSS$Attribute LIST_STYLE_IMAGE = new CSS$Attribute("list-style-image", "none", true);
    public static final CSS$Attribute LIST_STYLE_POSITION = new CSS$Attribute("list-style-position", "outside", true);
    public static final CSS$Attribute LIST_STYLE_TYPE = new CSS$Attribute("list-style-type", "disc", true);
    public static final CSS$Attribute MARGIN = new CSS$Attribute("margin", null, false);
    public static final CSS$Attribute MARGIN_BOTTOM = new CSS$Attribute("margin-bottom", "0", false);
    public static final CSS$Attribute MARGIN_LEFT = new CSS$Attribute("margin-left", "0", false);
    public static final CSS$Attribute MARGIN_RIGHT = new CSS$Attribute("margin-right", "0", false);
    static final CSS$Attribute MARGIN_LEFT_LTR = new CSS$Attribute("margin-left-ltr", Integer.toString(Integer.MIN_VALUE), false);
    static final CSS$Attribute MARGIN_LEFT_RTL = new CSS$Attribute("margin-left-rtl", Integer.toString(Integer.MIN_VALUE), false);
    static final CSS$Attribute MARGIN_RIGHT_LTR = new CSS$Attribute("margin-right-ltr", Integer.toString(Integer.MIN_VALUE), false);
    static final CSS$Attribute MARGIN_RIGHT_RTL = new CSS$Attribute("margin-right-rtl", Integer.toString(Integer.MIN_VALUE), false);
    public static final CSS$Attribute MARGIN_TOP = new CSS$Attribute("margin-top", "0", false);
    public static final CSS$Attribute PADDING = new CSS$Attribute("padding", null, false);
    public static final CSS$Attribute PADDING_BOTTOM = new CSS$Attribute("padding-bottom", "0", false);
    public static final CSS$Attribute PADDING_LEFT = new CSS$Attribute("padding-left", "0", false);
    public static final CSS$Attribute PADDING_RIGHT = new CSS$Attribute("padding-right", "0", false);
    public static final CSS$Attribute PADDING_TOP = new CSS$Attribute("padding-top", "0", false);
    public static final CSS$Attribute TEXT_ALIGN = new CSS$Attribute("text-align", null, true);
    public static final CSS$Attribute TEXT_DECORATION = new CSS$Attribute("text-decoration", "none", true);
    public static final CSS$Attribute TEXT_INDENT = new CSS$Attribute("text-indent", "0", true);
    public static final CSS$Attribute TEXT_TRANSFORM = new CSS$Attribute("text-transform", "none", true);
    public static final CSS$Attribute VERTICAL_ALIGN = new CSS$Attribute("vertical-align", "baseline", false);
    public static final CSS$Attribute WORD_SPACING = new CSS$Attribute("word-spacing", "normal", true);
    public static final CSS$Attribute WHITE_SPACE = new CSS$Attribute("white-space", "normal", true);
    public static final CSS$Attribute WIDTH = new CSS$Attribute("width", "auto", false);
    static final CSS$Attribute BORDER_SPACING = new CSS$Attribute("border-spacing", "0", true);
    static final CSS$Attribute CAPTION_SIDE = new CSS$Attribute("caption-side", "left", true);
    static final CSS$Attribute[] allAttributes = {BACKGROUND, BACKGROUND_ATTACHMENT, BACKGROUND_COLOR, BACKGROUND_IMAGE, BACKGROUND_POSITION, BACKGROUND_REPEAT, BORDER, BORDER_BOTTOM, BORDER_BOTTOM_WIDTH, BORDER_COLOR, BORDER_LEFT, BORDER_LEFT_WIDTH, BORDER_RIGHT, BORDER_RIGHT_WIDTH, BORDER_STYLE, BORDER_TOP, BORDER_TOP_WIDTH, BORDER_WIDTH, CLEAR, COLOR, DISPLAY, FLOAT, FONT, FONT_FAMILY, FONT_SIZE, FONT_STYLE, FONT_VARIANT, FONT_WEIGHT, HEIGHT, LETTER_SPACING, LINE_HEIGHT, LIST_STYLE, LIST_STYLE_IMAGE, LIST_STYLE_POSITION, LIST_STYLE_TYPE, MARGIN, MARGIN_BOTTOM, MARGIN_LEFT, MARGIN_RIGHT, MARGIN_TOP, PADDING, PADDING_BOTTOM, PADDING_LEFT, PADDING_RIGHT, PADDING_TOP, TEXT_ALIGN, TEXT_DECORATION, TEXT_INDENT, TEXT_TRANSFORM, VERTICAL_ALIGN, WORD_SPACING, WHITE_SPACE, WIDTH, BORDER_SPACING, CAPTION_SIDE, MARGIN_LEFT_LTR, MARGIN_LEFT_RTL, MARGIN_RIGHT_LTR, MARGIN_RIGHT_RTL};
    private static final CSS$Attribute[] ALL_MARGINS = {MARGIN_TOP, MARGIN_RIGHT, MARGIN_BOTTOM, MARGIN_LEFT};
    private static final CSS$Attribute[] ALL_PADDING = {PADDING_TOP, PADDING_RIGHT, PADDING_BOTTOM, PADDING_LEFT};
    private static final CSS$Attribute[] ALL_BORDER_WIDTHS = {BORDER_TOP_WIDTH, BORDER_RIGHT_WIDTH, BORDER_BOTTOM_WIDTH, BORDER_LEFT_WIDTH};
}
