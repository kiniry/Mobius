package java.awt;

import java.awt.Graphics2D;
import java.awt.font.FontRenderContext;
import java.awt.font.LineMetrics;
import java.awt.geom.Rectangle2D;
import java.text.CharacterIterator;

public abstract class FontMetrics implements java.io.Serializable {
    static {
        Toolkit.loadLibraries();
        if (!GraphicsEnvironment.isHeadless()) {
            initIDs();
        }
    }
    protected Font font;
    private static final long serialVersionUID = 1681126225205050147L;
    
    protected FontMetrics(Font font) {
        
        this.font = font;
    }
    
    public Font getFont() {
        return font;
    }
    
    public int getLeading() {
        return 0;
    }
    
    public int getAscent() {
        return font.getSize();
    }
    
    public int getDescent() {
        return 0;
    }
    
    public int getHeight() {
        return getLeading() + getAscent() + getDescent();
    }
    
    public int getMaxAscent() {
        return getAscent();
    }
    
    public int getMaxDescent() {
        return getDescent();
    }
    
    
    public int getMaxDecent() {
        return getMaxDescent();
    }
    
    public int getMaxAdvance() {
        return -1;
    }
    
    public int charWidth(int codePoint) {
        if (!Character.isValidCodePoint(codePoint)) {
            codePoint = 65535;
        }
        if (codePoint < 256) {
            return getWidths()[codePoint];
        } else {
            char[] buffer = new char[2];
            int len = Character.toChars(codePoint, buffer, 0);
            return charsWidth(buffer, 0, len);
        }
    }
    
    public int charWidth(char ch) {
        if (ch < 256) {
            return getWidths()[ch];
        }
        char[] data = {ch};
        return charsWidth(data, 0, 1);
    }
    
    public int stringWidth(String str) {
        int len = str.length();
        char[] data = new char[len];
        str.getChars(0, len, data, 0);
        return charsWidth(data, 0, len);
    }
    
    public int charsWidth(char[] data, int off, int len) {
        return stringWidth(new String(data, off, len));
    }
    
    public int bytesWidth(byte[] data, int off, int len) {
        return stringWidth(new String(data, 0, off, len));
    }
    
    public int[] getWidths() {
        int[] widths = new int[256];
        for (char ch = 0; ch < 256; ch++) {
            widths[ch] = charWidth(ch);
        }
        return widths;
    }
    
    public boolean hasUniformLineMetrics() {
        return font.hasUniformLineMetrics();
    }
    
    public LineMetrics getLineMetrics(String str, Graphics context) {
        return font.getLineMetrics(str, myFRC(context));
    }
    
    public LineMetrics getLineMetrics(String str, int beginIndex, int limit, Graphics context) {
        return font.getLineMetrics(str, beginIndex, limit, myFRC(context));
    }
    
    public LineMetrics getLineMetrics(char[] chars, int beginIndex, int limit, Graphics context) {
        return font.getLineMetrics(chars, beginIndex, limit, myFRC(context));
    }
    
    public LineMetrics getLineMetrics(CharacterIterator ci, int beginIndex, int limit, Graphics context) {
        return font.getLineMetrics(ci, beginIndex, limit, myFRC(context));
    }
    
    public Rectangle2D getStringBounds(String str, Graphics context) {
        return font.getStringBounds(str, myFRC(context));
    }
    
    public Rectangle2D getStringBounds(String str, int beginIndex, int limit, Graphics context) {
        return font.getStringBounds(str, beginIndex, limit, myFRC(context));
    }
    
    public Rectangle2D getStringBounds(char[] chars, int beginIndex, int limit, Graphics context) {
        return font.getStringBounds(chars, beginIndex, limit, myFRC(context));
    }
    
    public Rectangle2D getStringBounds(CharacterIterator ci, int beginIndex, int limit, Graphics context) {
        return font.getStringBounds(ci, beginIndex, limit, myFRC(context));
    }
    
    public Rectangle2D getMaxCharBounds(Graphics context) {
        return font.getMaxCharBounds(myFRC(context));
    }
    
    private FontRenderContext myFRC(Graphics context) {
        if (context instanceof Graphics2D) {
            return ((Graphics2D)(Graphics2D)context).getFontRenderContext();
        }
        return new FontRenderContext(null, false, false);
    }
    
    public String toString() {
        return getClass().getName() + "[font=" + getFont() + "ascent=" + getAscent() + ", descent=" + getDescent() + ", height=" + getHeight() + "]";
    }
    
    private static native void initIDs();
}
