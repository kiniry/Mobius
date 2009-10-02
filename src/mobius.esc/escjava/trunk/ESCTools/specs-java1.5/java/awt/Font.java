package java.awt;

import java.awt.font.FontRenderContext;
import java.awt.font.GlyphVector;
import java.awt.font.LineMetrics;
import java.awt.font.TextAttribute;
import java.awt.font.TextLayout;
import java.awt.font.TransformAttribute;
import java.awt.geom.AffineTransform;
import java.awt.geom.Rectangle2D;
import java.awt.peer.FontPeer;
import java.io.*;
import java.lang.ref.SoftReference;
import java.security.AccessController;
import java.text.AttributedCharacterIterator.Attribute;
import java.text.CharacterIterator;
import java.text.StringCharacterIterator;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.Locale;
import java.util.Map;
import sun.font.StandardGlyphVector;
import sun.font.CreatedFontTracker;
import sun.font.Font2D;
import sun.font.Font2DHandle;
import sun.font.FontManager;
import sun.font.GlyphLayout;
import sun.font.FontLineMetrics;
import sun.font.CoreMetrics;

public class Font implements java.io.Serializable {
    static {
        Toolkit.loadLibraries();
        initIDs();
    }
    private Hashtable fRequestedAttributes;
    private static final Map EMPTY_MAP = new Hashtable(5, (float)0.9);
    private static final TransformAttribute IDENT_TX_ATTRIBUTE = new TransformAttribute(new AffineTransform());
    public static final int PLAIN = 0;
    public static final int BOLD = 1;
    public static final int ITALIC = 2;
    public static final int ROMAN_BASELINE = 0;
    public static final int CENTER_BASELINE = 1;
    public static final int HANGING_BASELINE = 2;
    public static final int TRUETYPE_FONT = 0;
    public static final int TYPE1_FONT = 1;
    protected String name;
    protected int style;
    protected int size;
    protected float pointSize;
    private transient FontPeer peer;
    private transient long pData;
    private transient Font2DHandle font2DHandle;
    private transient int superscript;
    private transient float width = 1.0F;
    private transient boolean createdFont = false;
    private transient double[] matrix;
    private transient boolean nonIdentityTx;
    private static final AffineTransform identityTx = new AffineTransform();
    private static final long serialVersionUID = -4206021311591459213L;
    
    
    public FontPeer getPeer() {
        return getPeer_NoClientCode();
    }
    
    final FontPeer getPeer_NoClientCode() {
        if (peer == null) {
            Toolkit tk = Toolkit.getDefaultToolkit();
            this.peer = tk.getFontPeer(name, style);
        }
        return peer;
    }
    
    private Hashtable getRequestedAttributes() {
        if (fRequestedAttributes == null) {
            fRequestedAttributes = new Hashtable(7, (float)0.9);
            fRequestedAttributes.put(TextAttribute.TRANSFORM, IDENT_TX_ATTRIBUTE);
            fRequestedAttributes.put(TextAttribute.FAMILY, name);
            fRequestedAttributes.put(TextAttribute.SIZE, new Float(size));
            fRequestedAttributes.put(TextAttribute.WEIGHT, (style & BOLD) != 0 ? TextAttribute.WEIGHT_BOLD : TextAttribute.WEIGHT_REGULAR);
            fRequestedAttributes.put(TextAttribute.POSTURE, (style & ITALIC) != 0 ? TextAttribute.POSTURE_OBLIQUE : TextAttribute.POSTURE_REGULAR);
            fRequestedAttributes.put(TextAttribute.SUPERSCRIPT, new Integer(superscript));
            fRequestedAttributes.put(TextAttribute.WIDTH, new Float(width));
        }
        return fRequestedAttributes;
    }
    
    private void initializeFont(Hashtable attributes) {
        if (attributes != null) {
            Object obj = attributes.get(TextAttribute.TRANSFORM);
            if (obj instanceof TransformAttribute) {
                nonIdentityTx = !((TransformAttribute)(TransformAttribute)obj).isIdentity();
            } else if (obj instanceof AffineTransform) {
                nonIdentityTx = !((AffineTransform)(AffineTransform)obj).isIdentity();
            }
            obj = attributes.get(TextAttribute.SUPERSCRIPT);
            if (obj instanceof Integer) {
                superscript = ((Integer)(Integer)obj).intValue();
                nonIdentityTx |= superscript != 0;
            }
            obj = attributes.get(TextAttribute.WIDTH);
            if (obj instanceof Integer) {
                width = ((Float)(Float)obj).floatValue();
                nonIdentityTx |= width != 1;
            }
        }
    }
    
    private Font2D getFont2D() {
        if (FontManager.usingPerAppContextComposites && font2DHandle != null && font2DHandle.font2D instanceof sun.font.CompositeFont && ((sun.font.CompositeFont)((.sun.font.CompositeFont)font2DHandle.font2D)).isStdComposite()) {
            return FontManager.findFont2D(name, style, FontManager.LOGICAL_FALLBACK);
        } else if (font2DHandle == null) {
            font2DHandle = FontManager.findFont2D(name, style, FontManager.LOGICAL_FALLBACK).handle;
        }
        return font2DHandle.font2D;
    }
    
    private Font2DHandle getFont2DHandleForCreatedFont() {
        if (font2DHandle != null && createdFont && !(font2DHandle.font2D instanceof sun.font.CompositeFont)) {
            return font2DHandle;
        } else {
            return null;
        }
    }
    
    public Font(String name, int style, int size) {
        
        this.name = (name != null) ? name : "Default";
        this.style = (style & ~3) == 0 ? style : 0;
        this.size = size;
        this.pointSize = size;
    }
    
    private Font(String name, int style, float sizePts) {
        
        this.name = (name != null) ? name : "Default";
        this.style = (style & ~3) == 0 ? style : 0;
        this.size = (int)(sizePts + 0.5);
        this.pointSize = sizePts;
    }
    
    private Font(File fontFile, int fontFormat, boolean isCopy, CreatedFontTracker tracker) throws FontFormatException {
        
        this.createdFont = true;
        this.font2DHandle = FontManager.createFont2D(fontFile, fontFormat, isCopy, tracker).handle;
        this.name = this.font2DHandle.font2D.getFontName(Locale.getDefault());
        this.style = Font.PLAIN;
        this.size = 1;
        this.pointSize = 1.0F;
    }
    
    private Font(Map attributes, boolean created, Font2DHandle handle) {
        
        this.createdFont = created;
        if (created) {
            this.font2DHandle = handle;
        }
        initFromMap(attributes);
    }
    
    public Font(Map attributes) {
        
        initFromMap(attributes);
    }
    
    private void initFromMap(Map attributes) {
        this.name = "Dialog";
        this.pointSize = 12;
        this.size = 12;
        if ((attributes != null) && (!attributes.equals(EMPTY_MAP))) {
            Object obj;
            fRequestedAttributes = new Hashtable(attributes);
            if ((obj = attributes.get(TextAttribute.FAMILY)) != null) {
                this.name = (String)(String)obj;
            }
            if ((obj = attributes.get(TextAttribute.WEIGHT)) != null) {
                if (obj.equals(TextAttribute.WEIGHT_BOLD)) {
                    this.style |= BOLD;
                }
            }
            if ((obj = attributes.get(TextAttribute.POSTURE)) != null) {
                if (obj.equals(TextAttribute.POSTURE_OBLIQUE)) {
                    this.style |= ITALIC;
                }
            }
            if ((obj = attributes.get(TextAttribute.SIZE)) != null) {
                this.pointSize = ((Float)(Float)obj).floatValue();
                this.size = (int)(this.pointSize + 0.5);
            }
            if ((obj = attributes.get(TextAttribute.TRANSFORM)) != null) {
                if (obj instanceof TransformAttribute) {
                    nonIdentityTx = !((TransformAttribute)(TransformAttribute)obj).isIdentity();
                } else if (obj instanceof AffineTransform) {
                    nonIdentityTx = !((AffineTransform)(AffineTransform)obj).isIdentity();
                }
            }
            if ((obj = attributes.get(TextAttribute.SUPERSCRIPT)) != null) {
                if (obj instanceof Integer) {
                    superscript = ((Integer)(Integer)obj).intValue();
                    nonIdentityTx |= superscript != 0;
                }
            }
            if ((obj = attributes.get(TextAttribute.WIDTH)) != null) {
                if (obj instanceof Float) {
                    width = ((Float)(Float)obj).floatValue();
                    nonIdentityTx |= width != 1;
                }
            }
        }
    }
    
    public static Font getFont(Map attributes) {
        Font font = (Font)(Font)attributes.get(TextAttribute.FONT);
        if (font != null) {
            return font;
        }
        return get(new Font$Key(attributes));
    }
    private static SoftReference cacheRef = new SoftReference(new HashMap());
    
    private static Font get(Font$Key key) {
        Font f = null;
        Map cache = (Map)(Map)cacheRef.get();
        if (cache == null) {
            cache = new HashMap();
            cacheRef = new SoftReference(cache);
        } else {
            f = (Font)(Font)cache.get(key);
        }
        if (f == null) {
            f = new Font(key.attrs);
            cache.put(key, f);
        }
        return f;
    }
    {
    }
    
    private static boolean hasTempPermission() {
        if (System.getSecurityManager() == null) {
            return true;
        }
        File f = null;
        boolean hasPerm = false;
        try {
            f = File.createTempFile("+~JT", ".tmp", null);
            f.delete();
            f = null;
            hasPerm = true;
        } catch (Throwable t) {
        }
        return hasPerm;
    }
    
    public static Font createFont(int fontFormat, InputStream fontStream) throws java.awt.FontFormatException, java.io.IOException {
        if (fontFormat != Font.TRUETYPE_FONT && fontFormat != Font.TYPE1_FONT) {
            throw new IllegalArgumentException("font format not recognized");
        }
        boolean copiedFontData = false;
        try {
            final File tFile = (File)AccessController.doPrivileged(new Font$1());
            int totalSize = 0;
            CreatedFontTracker tracker = null;
            try {
                final OutputStream outStream = (OutputStream)AccessController.doPrivileged(new Font$2(tFile));
                if (!hasTempPermission()) {
                    tracker = CreatedFontTracker.getTracker();
                }
                try {
                    byte[] buf = new byte[8192];
                    for (; ; ) {
                        int bytesRead = fontStream.read(buf);
                        if (bytesRead < 0) {
                            break;
                        }
                        if (tracker != null) {
                            if (totalSize + bytesRead > tracker.MAX_FILE_SIZE) {
                                throw new IOException("File too big.");
                            }
                            if (totalSize + tracker.getNumBytes() > tracker.MAX_TOTAL_BYTES) {
                                throw new IOException("Total files too big.");
                            }
                            totalSize += bytesRead;
                            tracker.addBytes(bytesRead);
                        }
                        outStream.write(buf, 0, bytesRead);
                    }
                } finally {
                    outStream.close();
                }
                copiedFontData = true;
                Font font = new Font(tFile, fontFormat, true, tracker);
                return font;
            } finally {
                if (!copiedFontData) {
                    if (tracker != null) {
                        tracker.subBytes(totalSize);
                    }
                    AccessController.doPrivileged(new Font$3(tFile));
                }
            }
        } catch (Throwable t) {
            if (t instanceof FontFormatException) {
                throw (FontFormatException)(FontFormatException)t;
            }
            if (t instanceof IOException) {
                throw (IOException)(IOException)t;
            }
            Throwable cause = t.getCause();
            if (cause instanceof FontFormatException) {
                throw (FontFormatException)(FontFormatException)cause;
            }
            throw new IOException("Problem reading font data.");
        }
    }
    
    public static Font createFont(int fontFormat, File fontFile) throws java.awt.FontFormatException, java.io.IOException {
        fontFile = new File(fontFile.getPath());
        if (fontFormat != Font.TRUETYPE_FONT && fontFormat != Font.TYPE1_FONT) {
            throw new IllegalArgumentException("font format not recognized");
        }
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            FilePermission filePermission = new FilePermission(fontFile.getPath(), "read");
            sm.checkPermission(filePermission);
        }
        if (!fontFile.canRead()) {
            throw new IOException("Can\'t read " + fontFile);
        }
        return new Font(fontFile, fontFormat, false, null);
    }
    
    public AffineTransform getTransform() {
        if (nonIdentityTx) {
            AffineTransform at = null;
            Object obj = getRequestedAttributes().get(TextAttribute.TRANSFORM);
            if (obj != null) {
                if (obj instanceof TransformAttribute) {
                    at = ((TransformAttribute)(TransformAttribute)obj).getTransform();
                } else {
                    if (obj instanceof AffineTransform) {
                        at = new AffineTransform((AffineTransform)(AffineTransform)obj);
                    }
                }
            } else {
                at = new AffineTransform();
            }
            if (superscript != 0) {
                double trans = 0;
                int n = 0;
                boolean up = superscript > 0;
                int sign = up ? -1 : 1;
                int ss = up ? superscript : -superscript;
                while ((ss & 7) > n) {
                    int newn = ss & 7;
                    trans += sign * (ssinfo[newn] - ssinfo[n]);
                    ss >>= 3;
                    sign = -sign;
                    n = newn;
                }
                trans *= pointSize;
                double scale = Math.pow(2.0 / 3.0, n);
                at.preConcatenate(AffineTransform.getTranslateInstance(0, trans));
                at.scale(scale, scale);
            }
            if (width != 1.0F) {
                at.scale(width, 1.0F);
            }
            return at;
        }
        return new AffineTransform();
    }
    private static final float[] ssinfo = {0.0F, 0.375F, 0.625F, 0.7916667F, 0.9027778F, 0.9768519F, 1.0262346F, 1.0591564F};
    
    public String getFamily() {
        return getFamily_NoClientCode();
    }
    
    final String getFamily_NoClientCode() {
        return getFamily(Locale.getDefault());
    }
    
    public String getFamily(Locale l) {
        if (l == null) {
            throw new NullPointerException("null locale doesn\'t mean default");
        }
        return getFont2D().getFamilyName(l);
    }
    
    public String getPSName() {
        return getFont2D().getPostscriptName();
    }
    
    public String getName() {
        return name;
    }
    
    public String getFontName() {
        return getFontName(Locale.getDefault());
    }
    
    public String getFontName(Locale l) {
        if (l == null) {
            throw new NullPointerException("null locale doesn\'t mean default");
        }
        return getFont2D().getFontName(l);
    }
    
    public int getStyle() {
        return style;
    }
    
    public int getSize() {
        return size;
    }
    
    public float getSize2D() {
        return pointSize;
    }
    
    public boolean isPlain() {
        return style == 0;
    }
    
    public boolean isBold() {
        return (style & BOLD) != 0;
    }
    
    public boolean isItalic() {
        return (style & ITALIC) != 0;
    }
    
    public boolean isTransformed() {
        return nonIdentityTx;
    }
    
    public static Font getFont(String nm) {
        return getFont(nm, null);
    }
    
    public static Font decode(String str) {
        String fontName = str;
        String styleName = "";
        int fontSize = 12;
        int fontStyle = Font.PLAIN;
        if (str == null) {
            return new Font("Dialog", fontStyle, fontSize);
        }
        int lastHyphen = str.lastIndexOf('-');
        int lastSpace = str.lastIndexOf(' ');
        char sepChar = (lastHyphen > lastSpace) ? '-' : ' ';
        int sizeIndex = str.lastIndexOf(sepChar);
        int styleIndex = str.lastIndexOf(sepChar, sizeIndex - 1);
        int strlen = str.length();
        if (sizeIndex > 0 && sizeIndex + 1 < strlen) {
            try {
                fontSize = Integer.valueOf(str.substring(sizeIndex + 1)).intValue();
                if (fontSize <= 0) {
                    fontSize = 12;
                }
            } catch (NumberFormatException e) {
                styleIndex = sizeIndex;
                sizeIndex = strlen;
                if (str.charAt(sizeIndex - 1) == sepChar) {
                    sizeIndex--;
                }
            }
        }
        if (styleIndex >= 0 && styleIndex + 1 < strlen) {
            styleName = str.substring(styleIndex + 1, sizeIndex);
            styleName = styleName.toLowerCase(Locale.ENGLISH);
            if (styleName.equals("bolditalic")) {
                fontStyle = Font.BOLD | Font.ITALIC;
            } else if (styleName.equals("italic")) {
                fontStyle = Font.ITALIC;
            } else if (styleName.equals("bold")) {
                fontStyle = Font.BOLD;
            } else if (styleName.equals("plain")) {
                fontStyle = Font.PLAIN;
            } else {
                styleIndex = sizeIndex;
                if (str.charAt(styleIndex - 1) == sepChar) {
                    styleIndex--;
                }
            }
            fontName = str.substring(0, styleIndex);
        } else {
            int fontEnd = strlen;
            if (styleIndex > 0) {
                fontEnd = styleIndex;
            } else if (sizeIndex > 0) {
                fontEnd = sizeIndex;
            }
            if (fontEnd > 0 && str.charAt(fontEnd - 1) == sepChar) {
                fontEnd--;
            }
            fontName = str.substring(0, fontEnd);
        }
        return new Font(fontName, fontStyle, fontSize);
    }
    
    public static Font getFont(String nm, Font font) {
        String str = null;
        try {
            str = System.getProperty(nm);
        } catch (SecurityException e) {
        }
        if (str == null) {
            return font;
        }
        return decode(str);
    }
    
    public int hashCode() {
        return name.hashCode() ^ style ^ size;
    }
    
    public boolean equals(Object obj) {
        if (obj == this) {
            return true;
        }
        if (obj != null) {
            try {
                Font font = (Font)(Font)obj;
                if ((size == font.size) && (pointSize == font.pointSize) && (style == font.style) && (superscript == font.superscript) && (width == font.width) && name.equals(font.name)) {
                    double[] thismat = this.getMatrix();
                    double[] thatmat = font.getMatrix();
                    return thismat[0] == thatmat[0] && thismat[1] == thatmat[1] && thismat[2] == thatmat[2] && thismat[3] == thatmat[3] && thismat[4] == thatmat[4] && thismat[5] == thatmat[5];
                }
            } catch (ClassCastException e) {
            }
        }
        return false;
    }
    
    public String toString() {
        String strStyle;
        if (isBold()) {
            strStyle = isItalic() ? "bolditalic" : "bold";
        } else {
            strStyle = isItalic() ? "italic" : "plain";
        }
        return getClass().getName() + "[family=" + getFamily() + ",name=" + name + ",style=" + strStyle + ",size=" + size + "]";
    }
    private int fontSerializedDataVersion = 1;
    
    private void writeObject(java.io.ObjectOutputStream s) throws java.lang.ClassNotFoundException, java.io.IOException {
        s.defaultWriteObject();
    }
    
    private void readObject(java.io.ObjectInputStream s) throws java.lang.ClassNotFoundException, java.io.IOException {
        s.defaultReadObject();
        if (pointSize == 0) {
            pointSize = (float)size;
        }
        width = 1.0F;
        initializeFont(fRequestedAttributes);
    }
    
    public int getNumGlyphs() {
        return getFont2D().getNumGlyphs();
    }
    
    public int getMissingGlyphCode() {
        return getFont2D().getMissingGlyphCode();
    }
    private static double[] cachedMat;
    
    private double[] getMatrix() {
        if (matrix == null) {
            double ptSize = this.getSize2D();
            if (nonIdentityTx) {
                AffineTransform tx = getTransform();
                tx.scale(ptSize, ptSize);
                tx.getMatrix(matrix = new double[6]);
            } else {
                synchronized (Font.class) {
                    double[] m = cachedMat;
                    if (m == null || m[0] != ptSize) {
                        cachedMat = m = new double[]{ptSize, 0, 0, ptSize, 0, 0};
                    }
                    matrix = m;
                }
            }
        }
        return matrix;
    }
    
    public byte getBaselineFor(char c) {
        return getFont2D().getBaselineFor(c);
    }
    
    public Map getAttributes() {
        return (Map)(Map)getRequestedAttributes().clone();
    }
    
    public AttributedCharacterIterator$Attribute[] getAvailableAttributes() {
        AttributedCharacterIterator$Attribute[] attributes = {TextAttribute.FAMILY, TextAttribute.WEIGHT, TextAttribute.POSTURE, TextAttribute.SIZE, TextAttribute.TRANSFORM, TextAttribute.SUPERSCRIPT, TextAttribute.WIDTH};
        return attributes;
    }
    
    public Font deriveFont(int style, float size) {
        Hashtable newAttributes = (Hashtable)(Hashtable)getRequestedAttributes().clone();
        applyStyle(style, newAttributes);
        applySize(size, newAttributes);
        return new Font(newAttributes, createdFont, font2DHandle);
    }
    
    public Font deriveFont(int style, AffineTransform trans) {
        Hashtable newAttributes = (Hashtable)(Hashtable)getRequestedAttributes().clone();
        applyStyle(style, newAttributes);
        applyTransform(trans, newAttributes);
        return new Font(newAttributes, createdFont, font2DHandle);
    }
    
    public Font deriveFont(float size) {
        Hashtable newAttributes = (Hashtable)(Hashtable)getRequestedAttributes().clone();
        applySize(size, newAttributes);
        return new Font(newAttributes, createdFont, font2DHandle);
    }
    
    public Font deriveFont(AffineTransform trans) {
        Hashtable newAttributes = (Hashtable)(Hashtable)getRequestedAttributes().clone();
        applyTransform(trans, newAttributes);
        return new Font(newAttributes, createdFont, font2DHandle);
    }
    
    public Font deriveFont(int style) {
        Hashtable newAttributes = (Hashtable)(Hashtable)getRequestedAttributes().clone();
        applyStyle(style, newAttributes);
        return new Font(newAttributes, createdFont, font2DHandle);
    }
    
    public Font deriveFont(Map attributes) {
        if (attributes == null || attributes.size() == 0) {
            return this;
        }
        Hashtable newAttrs = new Hashtable(getAttributes());
        AttributedCharacterIterator$Attribute[] validAttribs = getAvailableAttributes();
        Object obj;
        for (int i = 0; i < validAttribs.length; i++) {
            if ((obj = attributes.get(validAttribs[i])) != null) {
                newAttrs.put(validAttribs[i], obj);
            }
        }
        return new Font(newAttrs, createdFont, font2DHandle);
    }
    
    public boolean canDisplay(char c) {
        return getFont2D().canDisplay(c);
    }
    
    public boolean canDisplay(int codePoint) {
        if (!Character.isValidCodePoint(codePoint)) {
            throw new IllegalArgumentException("invalid code point: " + Integer.toHexString(codePoint));
        }
        return getFont2D().canDisplay(codePoint);
    }
    
    public int canDisplayUpTo(String str) {
        return canDisplayUpTo(new StringCharacterIterator(str), 0, str.length());
    }
    
    public int canDisplayUpTo(char[] text, int start, int limit) {
        while (start < limit && canDisplay(text[start])) {
            ++start;
        }
        return start == limit ? -1 : start;
    }
    
    public int canDisplayUpTo(CharacterIterator iter, int start, int limit) {
        for (char c = iter.setIndex(start); iter.getIndex() < limit && canDisplay(c); c = iter.next()) {
        }
        int result = iter.getIndex();
        return result == limit ? -1 : result;
    }
    
    public float getItalicAngle() {
        AffineTransform at = (isTransformed()) ? getTransform() : identityTx;
        return getFont2D().getItalicAngle(this, at, false, false);
    }
    
    public boolean hasUniformLineMetrics() {
        return false;
    }
    private transient SoftReference flmref;
    
    private FontLineMetrics defaultLineMetrics(FontRenderContext frc) {
        FontLineMetrics flm = null;
        if (flmref == null || (flm = (FontLineMetrics)(FontLineMetrics)flmref.get()) == null || !flm.frc.equals(frc)) {
            float[] metrics = new float[4];
            getFont2D().getFontMetrics(this, identityTx, frc.isAntiAliased(), frc.usesFractionalMetrics(), metrics);
            float ascent = metrics[0];
            float descent = metrics[1];
            float leading = metrics[2];
            float ssOffset = 0;
            if (superscript != 0) {
                ssOffset = (float)getTransform().getTranslateY();
                ascent -= ssOffset;
                descent += ssOffset;
            }
            float height = ascent + descent + leading;
            int baselineIndex = 0;
            float[] baselineOffsets = {0, (descent / 2.0F - ascent) / 2.0F, -ascent};
            float strikethroughOffset = ssOffset - (metrics[0] / 2.5F);
            float strikethroughThickness = (float)(Math.log(pointSize / 4));
            float underlineOffset = ssOffset + strikethroughThickness / 1.5F;
            float underlineThickness = strikethroughThickness;
            float italicAngle = getItalicAngle();
            CoreMetrics cm = new CoreMetrics(ascent, descent, leading, height, baselineIndex, baselineOffsets, strikethroughOffset, strikethroughThickness, underlineOffset, underlineThickness, ssOffset, italicAngle);
            flm = new FontLineMetrics(0, cm, frc);
            flmref = new SoftReference(flm);
        }
        return (FontLineMetrics)(FontLineMetrics)flm.clone();
    }
    
    public LineMetrics getLineMetrics(String str, FontRenderContext frc) {
        FontLineMetrics flm = defaultLineMetrics(frc);
        flm.numchars = str.length();
        return flm;
    }
    
    public LineMetrics getLineMetrics(String str, int beginIndex, int limit, FontRenderContext frc) {
        FontLineMetrics flm = defaultLineMetrics(frc);
        int numChars = limit - beginIndex;
        flm.numchars = (numChars < 0) ? 0 : numChars;
        return flm;
    }
    
    public LineMetrics getLineMetrics(char[] chars, int beginIndex, int limit, FontRenderContext frc) {
        FontLineMetrics flm = defaultLineMetrics(frc);
        int numChars = limit - beginIndex;
        flm.numchars = (numChars < 0) ? 0 : numChars;
        return flm;
    }
    
    public LineMetrics getLineMetrics(CharacterIterator ci, int beginIndex, int limit, FontRenderContext frc) {
        FontLineMetrics flm = defaultLineMetrics(frc);
        int numChars = limit - beginIndex;
        flm.numchars = (numChars < 0) ? 0 : numChars;
        return flm;
    }
    
    public Rectangle2D getStringBounds(String str, FontRenderContext frc) {
        char[] array = str.toCharArray();
        return getStringBounds(array, 0, array.length, frc);
    }
    
    public Rectangle2D getStringBounds(String str, int beginIndex, int limit, FontRenderContext frc) {
        String substr = str.substring(beginIndex, limit);
        return getStringBounds(substr, frc);
    }
    
    public Rectangle2D getStringBounds(char[] chars, int beginIndex, int limit, FontRenderContext frc) {
        if (beginIndex < 0) {
            throw new IndexOutOfBoundsException("beginIndex: " + beginIndex);
        }
        if (limit > chars.length) {
            throw new IndexOutOfBoundsException("limit: " + limit);
        }
        if (beginIndex > limit) {
            throw new IndexOutOfBoundsException("range length: " + (limit - beginIndex));
        }
        boolean simple = true;
        for (int i = beginIndex; i < limit; ++i) {
            char c = chars[i];
            if (c >= '\u0590' && c <= '\u206f') {
                simple = false;
                break;
            }
        }
        if (simple) {
            GlyphVector gv = new StandardGlyphVector(this, chars, beginIndex, limit - beginIndex, frc);
            return gv.getLogicalBounds();
        } else {
            String str = new String(chars, beginIndex, limit - beginIndex);
            TextLayout tl = new TextLayout(str, this, frc);
            return new Rectangle2D$Float(0, -tl.getAscent(), tl.getAdvance(), tl.getDescent() + tl.getLeading());
        }
    }
    
    public Rectangle2D getStringBounds(CharacterIterator ci, int beginIndex, int limit, FontRenderContext frc) {
        int start = ci.getBeginIndex();
        int end = ci.getEndIndex();
        if (beginIndex < start) {
            throw new IndexOutOfBoundsException("beginIndex: " + beginIndex);
        }
        if (limit > end) {
            throw new IndexOutOfBoundsException("limit: " + limit);
        }
        if (beginIndex > limit) {
            throw new IndexOutOfBoundsException("range length: " + (limit - beginIndex));
        }
        char[] arr = new char[limit - beginIndex];
        ci.setIndex(beginIndex);
        for (int idx = 0; idx < arr.length; idx++) {
            arr[idx] = ci.current();
            ci.next();
        }
        return getStringBounds(arr, 0, arr.length, frc);
    }
    
    public Rectangle2D getMaxCharBounds(FontRenderContext frc) {
        float[] metrics = new float[4];
        getFont2D().getFontMetrics(this, frc, metrics);
        return new Rectangle2D$Float(0, -metrics[0], metrics[3], metrics[0] + metrics[1] + metrics[2]);
    }
    
    public GlyphVector createGlyphVector(FontRenderContext frc, String str) {
        return (GlyphVector)new StandardGlyphVector(this, str, frc);
    }
    
    public GlyphVector createGlyphVector(FontRenderContext frc, char[] chars) {
        return (GlyphVector)new StandardGlyphVector(this, chars, frc);
    }
    
    public GlyphVector createGlyphVector(FontRenderContext frc, CharacterIterator ci) {
        return (GlyphVector)new StandardGlyphVector(this, ci, frc);
    }
    
    public GlyphVector createGlyphVector(FontRenderContext frc, int[] glyphCodes) {
        return (GlyphVector)new StandardGlyphVector(this, glyphCodes, frc);
    }
    
    public GlyphVector layoutGlyphVector(FontRenderContext frc, char[] text, int start, int limit, int flags) {
        GlyphLayout gl = GlyphLayout.get(null);
        StandardGlyphVector gv = gl.layout(this, frc, text, start, limit, flags, null);
        GlyphLayout.done(gl);
        return gv;
    }
    public static final int LAYOUT_LEFT_TO_RIGHT = 0;
    public static final int LAYOUT_RIGHT_TO_LEFT = 1;
    public static final int LAYOUT_NO_START_CONTEXT = 2;
    public static final int LAYOUT_NO_LIMIT_CONTEXT = 4;
    
    private static void applyTransform(AffineTransform trans, Map attributes) {
        if (trans == null) {
            throw new IllegalArgumentException("transform must not be null");
        }
        if (trans.isIdentity()) {
            attributes.remove(TextAttribute.TRANSFORM);
        } else {
            attributes.put(TextAttribute.TRANSFORM, new TransformAttribute(trans));
        }
    }
    
    private static void applyStyle(int style, Map attributes) {
        if ((style & BOLD) != 0) {
            attributes.put(TextAttribute.WEIGHT, TextAttribute.WEIGHT_BOLD);
        } else {
            attributes.remove(TextAttribute.WEIGHT);
        }
        if ((style & ITALIC) != 0) {
            attributes.put(TextAttribute.POSTURE, TextAttribute.POSTURE_OBLIQUE);
        } else {
            attributes.remove(TextAttribute.POSTURE);
        }
    }
    
    private static void applySize(float size, Map attributes) {
        attributes.put(TextAttribute.SIZE, new Float(size));
    }
    
    private static native void initIDs();
    
    private native void pDispose();
    
    protected void finalize() throws Throwable {
        if (this.peer != null) {
            pDispose();
        }
        super.finalize();
    }
}
