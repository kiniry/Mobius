package javax.swing.text;

import java.awt.Color;
import java.awt.Component;
import javax.swing.Icon;

public class StyleConstants {
    {
    }
    public static final String ComponentElementName = "component";
    public static final String IconElementName = "icon";
    public static final Object NameAttribute = new StyleConstants("name");
    public static final Object ResolveAttribute = new StyleConstants("resolver");
    public static final Object ModelAttribute = new StyleConstants("model");
    
    public String toString() {
        return representation;
    }
    public static final Object BidiLevel = new StyleConstants$CharacterConstants("bidiLevel", null);
    public static final Object FontFamily = new StyleConstants$FontConstants("family", null);
    public static final Object Family = FontFamily;
    public static final Object FontSize = new StyleConstants$FontConstants("size", null);
    public static final Object Size = FontSize;
    public static final Object Bold = new StyleConstants$FontConstants("bold", null);
    public static final Object Italic = new StyleConstants$FontConstants("italic", null);
    public static final Object Underline = new StyleConstants$CharacterConstants("underline", null);
    public static final Object StrikeThrough = new StyleConstants$CharacterConstants("strikethrough", null);
    public static final Object Superscript = new StyleConstants$CharacterConstants("superscript", null);
    public static final Object Subscript = new StyleConstants$CharacterConstants("subscript", null);
    public static final Object Foreground = new StyleConstants$ColorConstants("foreground", null);
    public static final Object Background = new StyleConstants$ColorConstants("background", null);
    public static final Object ComponentAttribute = new StyleConstants$CharacterConstants("component", null);
    public static final Object IconAttribute = new StyleConstants$CharacterConstants("icon", null);
    public static final Object ComposedTextAttribute = new StyleConstants("composed text");
    public static final Object FirstLineIndent = new StyleConstants$ParagraphConstants("FirstLineIndent", null);
    public static final Object LeftIndent = new StyleConstants$ParagraphConstants("LeftIndent", null);
    public static final Object RightIndent = new StyleConstants$ParagraphConstants("RightIndent", null);
    public static final Object LineSpacing = new StyleConstants$ParagraphConstants("LineSpacing", null);
    public static final Object SpaceAbove = new StyleConstants$ParagraphConstants("SpaceAbove", null);
    public static final Object SpaceBelow = new StyleConstants$ParagraphConstants("SpaceBelow", null);
    public static final Object Alignment = new StyleConstants$ParagraphConstants("Alignment", null);
    public static final Object TabSet = new StyleConstants$ParagraphConstants("TabSet", null);
    public static final Object Orientation = new StyleConstants$ParagraphConstants("Orientation", null);
    public static final int ALIGN_LEFT = 0;
    public static final int ALIGN_CENTER = 1;
    public static final int ALIGN_RIGHT = 2;
    public static final int ALIGN_JUSTIFIED = 3;
    
    public static int getBidiLevel(AttributeSet a) {
        Integer o = (Integer)(Integer)a.getAttribute(BidiLevel);
        if (o != null) {
            return o.intValue();
        }
        return 0;
    }
    
    public static void setBidiLevel(MutableAttributeSet a, int o) {
        a.addAttribute(BidiLevel, new Integer(o));
    }
    
    public static Component getComponent(AttributeSet a) {
        return (Component)(Component)a.getAttribute(ComponentAttribute);
    }
    
    public static void setComponent(MutableAttributeSet a, Component c) {
        a.addAttribute(AbstractDocument.ElementNameAttribute, ComponentElementName);
        a.addAttribute(ComponentAttribute, c);
    }
    
    public static Icon getIcon(AttributeSet a) {
        return (Icon)(Icon)a.getAttribute(IconAttribute);
    }
    
    public static void setIcon(MutableAttributeSet a, Icon c) {
        a.addAttribute(AbstractDocument.ElementNameAttribute, IconElementName);
        a.addAttribute(IconAttribute, c);
    }
    
    public static String getFontFamily(AttributeSet a) {
        String family = (String)(String)a.getAttribute(FontFamily);
        if (family == null) {
            family = "Monospaced";
        }
        return family;
    }
    
    public static void setFontFamily(MutableAttributeSet a, String fam) {
        a.addAttribute(FontFamily, fam);
    }
    
    public static int getFontSize(AttributeSet a) {
        Integer size = (Integer)(Integer)a.getAttribute(FontSize);
        if (size != null) {
            return size.intValue();
        }
        return 12;
    }
    
    public static void setFontSize(MutableAttributeSet a, int s) {
        a.addAttribute(FontSize, new Integer(s));
    }
    
    public static boolean isBold(AttributeSet a) {
        Boolean bold = (Boolean)(Boolean)a.getAttribute(Bold);
        if (bold != null) {
            return bold.booleanValue();
        }
        return false;
    }
    
    public static void setBold(MutableAttributeSet a, boolean b) {
        a.addAttribute(Bold, Boolean.valueOf(b));
    }
    
    public static boolean isItalic(AttributeSet a) {
        Boolean italic = (Boolean)(Boolean)a.getAttribute(Italic);
        if (italic != null) {
            return italic.booleanValue();
        }
        return false;
    }
    
    public static void setItalic(MutableAttributeSet a, boolean b) {
        a.addAttribute(Italic, Boolean.valueOf(b));
    }
    
    public static boolean isUnderline(AttributeSet a) {
        Boolean underline = (Boolean)(Boolean)a.getAttribute(Underline);
        if (underline != null) {
            return underline.booleanValue();
        }
        return false;
    }
    
    public static boolean isStrikeThrough(AttributeSet a) {
        Boolean strike = (Boolean)(Boolean)a.getAttribute(StrikeThrough);
        if (strike != null) {
            return strike.booleanValue();
        }
        return false;
    }
    
    public static boolean isSuperscript(AttributeSet a) {
        Boolean superscript = (Boolean)(Boolean)a.getAttribute(Superscript);
        if (superscript != null) {
            return superscript.booleanValue();
        }
        return false;
    }
    
    public static boolean isSubscript(AttributeSet a) {
        Boolean subscript = (Boolean)(Boolean)a.getAttribute(Subscript);
        if (subscript != null) {
            return subscript.booleanValue();
        }
        return false;
    }
    
    public static void setUnderline(MutableAttributeSet a, boolean b) {
        a.addAttribute(Underline, Boolean.valueOf(b));
    }
    
    public static void setStrikeThrough(MutableAttributeSet a, boolean b) {
        a.addAttribute(StrikeThrough, Boolean.valueOf(b));
    }
    
    public static void setSuperscript(MutableAttributeSet a, boolean b) {
        a.addAttribute(Superscript, Boolean.valueOf(b));
    }
    
    public static void setSubscript(MutableAttributeSet a, boolean b) {
        a.addAttribute(Subscript, Boolean.valueOf(b));
    }
    
    public static Color getForeground(AttributeSet a) {
        Color fg = (Color)(Color)a.getAttribute(Foreground);
        if (fg == null) {
            fg = Color.black;
        }
        return fg;
    }
    
    public static void setForeground(MutableAttributeSet a, Color fg) {
        a.addAttribute(Foreground, fg);
    }
    
    public static Color getBackground(AttributeSet a) {
        Color fg = (Color)(Color)a.getAttribute(Background);
        if (fg == null) {
            fg = Color.black;
        }
        return fg;
    }
    
    public static void setBackground(MutableAttributeSet a, Color fg) {
        a.addAttribute(Background, fg);
    }
    
    public static float getFirstLineIndent(AttributeSet a) {
        Float indent = (Float)(Float)a.getAttribute(FirstLineIndent);
        if (indent != null) {
            return indent.floatValue();
        }
        return 0;
    }
    
    public static void setFirstLineIndent(MutableAttributeSet a, float i) {
        a.addAttribute(FirstLineIndent, new Float(i));
    }
    
    public static float getRightIndent(AttributeSet a) {
        Float indent = (Float)(Float)a.getAttribute(RightIndent);
        if (indent != null) {
            return indent.floatValue();
        }
        return 0;
    }
    
    public static void setRightIndent(MutableAttributeSet a, float i) {
        a.addAttribute(RightIndent, new Float(i));
    }
    
    public static float getLeftIndent(AttributeSet a) {
        Float indent = (Float)(Float)a.getAttribute(LeftIndent);
        if (indent != null) {
            return indent.floatValue();
        }
        return 0;
    }
    
    public static void setLeftIndent(MutableAttributeSet a, float i) {
        a.addAttribute(LeftIndent, new Float(i));
    }
    
    public static float getLineSpacing(AttributeSet a) {
        Float space = (Float)(Float)a.getAttribute(LineSpacing);
        if (space != null) {
            return space.floatValue();
        }
        return 0;
    }
    
    public static void setLineSpacing(MutableAttributeSet a, float i) {
        a.addAttribute(LineSpacing, new Float(i));
    }
    
    public static float getSpaceAbove(AttributeSet a) {
        Float space = (Float)(Float)a.getAttribute(SpaceAbove);
        if (space != null) {
            return space.floatValue();
        }
        return 0;
    }
    
    public static void setSpaceAbove(MutableAttributeSet a, float i) {
        a.addAttribute(SpaceAbove, new Float(i));
    }
    
    public static float getSpaceBelow(AttributeSet a) {
        Float space = (Float)(Float)a.getAttribute(SpaceBelow);
        if (space != null) {
            return space.floatValue();
        }
        return 0;
    }
    
    public static void setSpaceBelow(MutableAttributeSet a, float i) {
        a.addAttribute(SpaceBelow, new Float(i));
    }
    
    public static int getAlignment(AttributeSet a) {
        Integer align = (Integer)(Integer)a.getAttribute(Alignment);
        if (align != null) {
            return align.intValue();
        }
        return ALIGN_LEFT;
    }
    
    public static void setAlignment(MutableAttributeSet a, int align) {
        a.addAttribute(Alignment, new Integer(align));
    }
    
    public static TabSet getTabSet(AttributeSet a) {
        TabSet tabs = (TabSet)(TabSet)a.getAttribute(TabSet);
        return tabs;
    }
    
    public static void setTabSet(MutableAttributeSet a, TabSet tabs) {
        a.addAttribute(TabSet, tabs);
    }
    static Object[] keys = {NameAttribute, ResolveAttribute, BidiLevel, FontFamily, FontSize, Bold, Italic, Underline, StrikeThrough, Superscript, Subscript, Foreground, Background, ComponentAttribute, IconAttribute, FirstLineIndent, LeftIndent, RightIndent, LineSpacing, SpaceAbove, SpaceBelow, Alignment, TabSet, Orientation, ModelAttribute, ComposedTextAttribute};
    
    StyleConstants(String representation) {
        
        this.representation = representation;
    }
    private String representation;
    {
    }
    {
    }
    {
    }
    {
    }
}
