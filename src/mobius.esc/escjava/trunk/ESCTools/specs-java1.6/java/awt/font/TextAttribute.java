package java.awt.font;

import java.io.InvalidObjectException;
import java.text.AttributedCharacterIterator.Attribute;
import java.util.Map;
import java.util.HashMap;

public final class TextAttribute extends AttributedCharacterIterator$Attribute {
    private static final Map instanceMap = new HashMap(29);
    
    protected TextAttribute(String name) {
        super(name);
        if (this.getClass() == TextAttribute.class) {
            instanceMap.put(name, this);
        }
    }
    
    protected Object readResolve() throws InvalidObjectException {
        if (this.getClass() != TextAttribute.class) {
            throw new InvalidObjectException("subclass didn\'t correctly implement readResolve");
        }
        TextAttribute instance = (TextAttribute)(TextAttribute)instanceMap.get(getName());
        if (instance != null) {
            return instance;
        } else {
            throw new InvalidObjectException("unknown attribute name");
        }
    }
    static final long serialVersionUID = 7744112784117861702L;
    public static final TextAttribute FAMILY = new TextAttribute("family");
    public static final TextAttribute WEIGHT = new TextAttribute("weight");
    public static final Float WEIGHT_EXTRA_LIGHT = new Float(0.5F);
    public static final Float WEIGHT_LIGHT = new Float(0.75F);
    public static final Float WEIGHT_DEMILIGHT = new Float(0.875F);
    public static final Float WEIGHT_REGULAR = new Float(1.0F);
    public static final Float WEIGHT_SEMIBOLD = new Float(1.25F);
    public static final Float WEIGHT_MEDIUM = new Float(1.5F);
    public static final Float WEIGHT_DEMIBOLD = new Float(1.75F);
    public static final Float WEIGHT_BOLD = new Float(2.0F);
    public static final Float WEIGHT_HEAVY = new Float(2.25F);
    public static final Float WEIGHT_EXTRABOLD = new Float(2.5F);
    public static final Float WEIGHT_ULTRABOLD = new Float(2.75F);
    public static final TextAttribute WIDTH = new TextAttribute("width");
    public static final Float WIDTH_CONDENSED = new Float(0.75F);
    public static final Float WIDTH_SEMI_CONDENSED = new Float(0.875F);
    public static final Float WIDTH_REGULAR = new Float(1.0F);
    public static final Float WIDTH_SEMI_EXTENDED = new Float(1.25F);
    public static final Float WIDTH_EXTENDED = new Float(1.5F);
    public static final TextAttribute POSTURE = new TextAttribute("posture");
    public static final Float POSTURE_REGULAR = new Float(0.0F);
    public static final Float POSTURE_OBLIQUE = new Float(0.2F);
    public static final TextAttribute SIZE = new TextAttribute("size");
    public static final TextAttribute TRANSFORM = new TextAttribute("transform");
    public static final TextAttribute SUPERSCRIPT = new TextAttribute("superscript");
    public static final Integer SUPERSCRIPT_SUPER = new Integer(1);
    public static final Integer SUPERSCRIPT_SUB = new Integer(-1);
    public static final TextAttribute FONT = new TextAttribute("font");
    public static final TextAttribute CHAR_REPLACEMENT = new TextAttribute("char_replacement");
    public static final TextAttribute FOREGROUND = new TextAttribute("foreground");
    public static final TextAttribute BACKGROUND = new TextAttribute("background");
    public static final TextAttribute UNDERLINE = new TextAttribute("underline");
    public static final Integer UNDERLINE_ON = new Integer((byte)0);
    public static final TextAttribute STRIKETHROUGH = new TextAttribute("strikethrough");
    public static final Boolean STRIKETHROUGH_ON = new Boolean(true);
    public static final TextAttribute RUN_DIRECTION = new TextAttribute("run_direction");
    public static final Boolean RUN_DIRECTION_LTR = new Boolean(false);
    public static final Boolean RUN_DIRECTION_RTL = new Boolean(true);
    public static final TextAttribute BIDI_EMBEDDING = new TextAttribute("bidi_embedding");
    public static final TextAttribute JUSTIFICATION = new TextAttribute("justification");
    public static final Float JUSTIFICATION_FULL = new Float(1.0F);
    public static final Float JUSTIFICATION_NONE = new Float(0.0F);
    public static final TextAttribute INPUT_METHOD_HIGHLIGHT = new TextAttribute("input method highlight");
    public static final TextAttribute INPUT_METHOD_UNDERLINE = new TextAttribute("input method underline");
    public static final Integer UNDERLINE_LOW_ONE_PIXEL = new Integer(1);
    public static final Integer UNDERLINE_LOW_TWO_PIXEL = new Integer(2);
    public static final Integer UNDERLINE_LOW_DOTTED = new Integer(3);
    public static final Integer UNDERLINE_LOW_GRAY = new Integer(4);
    public static final Integer UNDERLINE_LOW_DASHED = new Integer(5);
    public static final TextAttribute SWAP_COLORS = new TextAttribute("swap_colors");
    public static final Boolean SWAP_COLORS_ON = new Boolean(true);
    public static final TextAttribute NUMERIC_SHAPING = new TextAttribute("numeric_shaping");
}
