package java.awt;

import java.awt.geom.AffineTransform;
import java.awt.geom.Rectangle2D;
import java.awt.image.ColorModel;

public final class SystemColor extends Color implements java.io.Serializable {
    public static final int DESKTOP = 0;
    public static final int ACTIVE_CAPTION = 1;
    public static final int ACTIVE_CAPTION_TEXT = 2;
    public static final int ACTIVE_CAPTION_BORDER = 3;
    public static final int INACTIVE_CAPTION = 4;
    public static final int INACTIVE_CAPTION_TEXT = 5;
    public static final int INACTIVE_CAPTION_BORDER = 6;
    public static final int WINDOW = 7;
    public static final int WINDOW_BORDER = 8;
    public static final int WINDOW_TEXT = 9;
    public static final int MENU = 10;
    public static final int MENU_TEXT = 11;
    public static final int TEXT = 12;
    public static final int TEXT_TEXT = 13;
    public static final int TEXT_HIGHLIGHT = 14;
    public static final int TEXT_HIGHLIGHT_TEXT = 15;
    public static final int TEXT_INACTIVE_TEXT = 16;
    public static final int CONTROL = 17;
    public static final int CONTROL_TEXT = 18;
    public static final int CONTROL_HIGHLIGHT = 19;
    public static final int CONTROL_LT_HIGHLIGHT = 20;
    public static final int CONTROL_SHADOW = 21;
    public static final int CONTROL_DK_SHADOW = 22;
    public static final int SCROLLBAR = 23;
    public static final int INFO = 24;
    public static final int INFO_TEXT = 25;
    public static final int NUM_COLORS = 26;
    public static final SystemColor desktop = new SystemColor((byte)DESKTOP);
    public static final SystemColor activeCaption = new SystemColor((byte)ACTIVE_CAPTION);
    public static final SystemColor activeCaptionText = new SystemColor((byte)ACTIVE_CAPTION_TEXT);
    public static final SystemColor activeCaptionBorder = new SystemColor((byte)ACTIVE_CAPTION_BORDER);
    public static final SystemColor inactiveCaption = new SystemColor((byte)INACTIVE_CAPTION);
    public static final SystemColor inactiveCaptionText = new SystemColor((byte)INACTIVE_CAPTION_TEXT);
    public static final SystemColor inactiveCaptionBorder = new SystemColor((byte)INACTIVE_CAPTION_BORDER);
    public static final SystemColor window = new SystemColor((byte)WINDOW);
    public static final SystemColor windowBorder = new SystemColor((byte)WINDOW_BORDER);
    public static final SystemColor windowText = new SystemColor((byte)WINDOW_TEXT);
    public static final SystemColor menu = new SystemColor((byte)MENU);
    public static final SystemColor menuText = new SystemColor((byte)MENU_TEXT);
    public static final SystemColor text = new SystemColor((byte)TEXT);
    public static final SystemColor textText = new SystemColor((byte)TEXT_TEXT);
    public static final SystemColor textHighlight = new SystemColor((byte)TEXT_HIGHLIGHT);
    public static final SystemColor textHighlightText = new SystemColor((byte)TEXT_HIGHLIGHT_TEXT);
    public static final SystemColor textInactiveText = new SystemColor((byte)TEXT_INACTIVE_TEXT);
    public static final SystemColor control = new SystemColor((byte)CONTROL);
    public static final SystemColor controlText = new SystemColor((byte)CONTROL_TEXT);
    public static final SystemColor controlHighlight = new SystemColor((byte)CONTROL_HIGHLIGHT);
    public static final SystemColor controlLtHighlight = new SystemColor((byte)CONTROL_LT_HIGHLIGHT);
    public static final SystemColor controlShadow = new SystemColor((byte)CONTROL_SHADOW);
    public static final SystemColor controlDkShadow = new SystemColor((byte)CONTROL_DK_SHADOW);
    public static final SystemColor scrollbar = new SystemColor((byte)SCROLLBAR);
    public static final SystemColor info = new SystemColor((byte)INFO);
    public static final SystemColor infoText = new SystemColor((byte)INFO_TEXT);
    private static int[] systemColors = {-16753572, -16777088, -1, -4144960, -8355712, -4144960, -4144960, -1, -16777216, -16777216, -4144960, -16777216, -4144960, -16777216, -16777088, -1, -8355712, -4144960, -16777216, -1, -2039584, -8355712, -16777216, -2039584, -2039808, -16777216};
    private static final long serialVersionUID = 4503142729533789064L;
    static {
        updateSystemColors();
    }
    
    private static void updateSystemColors() {
        if (!GraphicsEnvironment.isHeadless()) {
            Toolkit.getDefaultToolkit().loadSystemColors(systemColors);
        }
    }
    
    private SystemColor(byte index) {
        super(0, 0, 0);
        value = index;
    }
    
    public int getRGB() {
        return systemColors[value];
    }
    
    public PaintContext createContext(ColorModel cm, Rectangle r, Rectangle2D r2d, AffineTransform xform, RenderingHints hints) {
        return new ColorPaintContext(value, cm);
    }
    
    public String toString() {
        return getClass().getName() + "[i=" + (value) + "]";
    }
}
