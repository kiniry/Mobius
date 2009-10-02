package java.awt.font;

import java.awt.Font;
import java.awt.Graphics2D;
import java.awt.Shape;
import java.awt.font.NumericShaper;
import java.awt.font.TextLine.TextLineMetrics;
import java.awt.geom.AffineTransform;
import java.awt.geom.GeneralPath;
import java.awt.geom.Rectangle2D;
import java.text.AttributedString;
import java.text.AttributedCharacterIterator;
import java.util.Map;
import sun.font.CoreMetrics;
import sun.font.FontResolver;
import sun.font.GraphicComponent;
import sun.text.CodePointIterator;

public final class TextLayout implements Cloneable {
    
    /*synthetic*/ static TextHitInfo access$000(TextLayout x0, TextHitInfo x1, TextHitInfo x2) {
        return x0.getStrongHit(x1, x2);
    }
    private int characterCount;
    private boolean isVerticalLine = false;
    private byte baseline;
    private float[] baselineOffsets;
    private TextLine textLine;
    private TextLine$TextLineMetrics lineMetrics = null;
    private float visibleAdvance;
    private int hashCodeCache;
    {
    }
    private TextLayout$OptInfo optInfo;
    private boolean cacheIsValid = false;
    private float justifyRatio;
    private static final float ALREADY_JUSTIFIED = -53.9F;
    private static float dx;
    private static float dy;
    private Rectangle2D naturalBounds = null;
    private Rectangle2D boundsRect = null;
    private boolean caretsInLigaturesAreAllowed = false;
    {
    }
    public static final TextLayout$CaretPolicy DEFAULT_CARET_POLICY = new TextLayout$CaretPolicy();
    
    public TextLayout(String string, Font font, FontRenderContext frc) {
        
        if (font == null) {
            throw new IllegalArgumentException("Null font passed to TextLayout constructor.");
        }
        if (string == null) {
            throw new IllegalArgumentException("Null string passed to TextLayout constructor.");
        }
        if (string.length() == 0) {
            throw new IllegalArgumentException("Zero length string passed to TextLayout constructor.");
        }
        char[] text = string.toCharArray();
        if (sameBaselineUpTo(font, text, 0, text.length) == text.length) {
            fastInit(text, font, null, frc);
        } else {
            AttributedString as = new AttributedString(string);
            as.addAttribute(TextAttribute.FONT, font);
            standardInit(as.getIterator(), text, frc);
        }
    }
    
    public TextLayout(String string, Map attributes, FontRenderContext frc) {
        
        if (string == null) {
            throw new IllegalArgumentException("Null string passed to TextLayout constructor.");
        }
        if (attributes == null) {
            throw new IllegalArgumentException("Null map passed to TextLayout constructor.");
        }
        if (string.length() == 0) {
            throw new IllegalArgumentException("Zero length string passed to TextLayout constructor.");
        }
        char[] text = string.toCharArray();
        Font font = singleFont(text, 0, text.length, attributes);
        if (font != null) {
            fastInit(text, font, attributes, frc);
        } else {
            AttributedString as = new AttributedString(string, attributes);
            standardInit(as.getIterator(), text, frc);
        }
    }
    
    private static Font singleFont(char[] text, int start, int limit, Map attributes) {
        if (attributes.get(TextAttribute.CHAR_REPLACEMENT) != null) {
            return null;
        }
        Font font = (Font)(Font)attributes.get(TextAttribute.FONT);
        if (font == null) {
            if (attributes.get(TextAttribute.FAMILY) != null) {
                font = Font.getFont(attributes);
                if (font.canDisplayUpTo(text, start, limit) != -1) {
                    return null;
                }
            } else {
                FontResolver resolver = FontResolver.getInstance();
                CodePointIterator iter = CodePointIterator.create(text, start, limit);
                int fontIndex = resolver.nextFontRunIndex(iter);
                if (iter.charIndex() == limit) {
                    font = resolver.getFont(fontIndex, attributes);
                }
            }
        }
        if (sameBaselineUpTo(font, text, start, limit) != limit) {
            return null;
        }
        return font;
    }
    
    public TextLayout(AttributedCharacterIterator text, FontRenderContext frc) {
        
        if (text == null) {
            throw new IllegalArgumentException("Null iterator passed to TextLayout constructor.");
        }
        int start = text.getBeginIndex();
        int limit = text.getEndIndex();
        if (start == limit) {
            throw new IllegalArgumentException("Zero length iterator passed to TextLayout constructor.");
        }
        int len = limit - start;
        text.first();
        char[] chars = new char[len];
        int n = 0;
        for (char c = text.first(); c != text.DONE; c = text.next()) {
            chars[n++] = c;
        }
        text.first();
        if (text.getRunLimit() == limit) {
            Map attributes = text.getAttributes();
            Font font = singleFont(chars, 0, len, attributes);
            if (font != null) {
                fastInit(chars, font, attributes, frc);
                return;
            }
        }
        standardInit(text, chars, frc);
    }
    
    TextLayout(TextLine textLine, byte baseline, float[] baselineOffsets, float justifyRatio) {
        
        this.characterCount = textLine.characterCount();
        this.baseline = baseline;
        this.baselineOffsets = baselineOffsets;
        this.textLine = textLine;
        this.justifyRatio = justifyRatio;
    }
    
    private void paragraphInit(byte aBaseline, CoreMetrics lm, Map paragraphAttrs, char[] text) {
        baseline = aBaseline;
        baselineOffsets = TextLine.getNormalizedOffsets(lm.baselineOffsets, baseline);
        justifyRatio = TextLine.getJustifyRatio(paragraphAttrs);
        if (paragraphAttrs != null) {
            Object o = paragraphAttrs.get(TextAttribute.NUMERIC_SHAPING);
            if (o != null) {
                try {
                    NumericShaper shaper = (NumericShaper)(NumericShaper)o;
                    shaper.shape(text, 0, text.length);
                } catch (ClassCastException e) {
                }
            }
        }
    }
    
    private void fastInit(char[] chars, Font font, Map attrs, FontRenderContext frc) {
        isVerticalLine = false;
        LineMetrics lm = font.getLineMetrics(chars, 0, chars.length, frc);
        CoreMetrics cm = CoreMetrics.get(lm);
        byte glyphBaseline = (byte)cm.baselineIndex;
        if (attrs == null) {
            baseline = glyphBaseline;
            baselineOffsets = cm.baselineOffsets;
            justifyRatio = 1.0F;
        } else {
            paragraphInit(glyphBaseline, cm, attrs, chars);
        }
        characterCount = chars.length;
        optInfo = TextLayout$OptInfo.create(frc, chars, font, cm, attrs);
        if (optInfo == null) {
            textLine = TextLine.fastCreateTextLine(frc, chars, font, cm, attrs);
        }
    }
    
    private void initTextLine() {
        textLine = optInfo.createTextLine();
        optInfo = null;
    }
    
    private void standardInit(AttributedCharacterIterator text, char[] chars, FontRenderContext frc) {
        characterCount = chars.length;
        {
            Map paragraphAttrs = text.getAttributes();
            boolean haveFont = TextLine.advanceToFirstFont(text);
            if (haveFont) {
                Font defaultFont = TextLine.getFontAtCurrentPos(text);
                int charsStart = text.getIndex() - text.getBeginIndex();
                LineMetrics lm = defaultFont.getLineMetrics(chars, charsStart, charsStart + 1, frc);
                CoreMetrics cm = CoreMetrics.get(lm);
                paragraphInit((byte)cm.baselineIndex, cm, paragraphAttrs, chars);
            } else {
                GraphicAttribute graphic = (GraphicAttribute)(GraphicAttribute)paragraphAttrs.get(TextAttribute.CHAR_REPLACEMENT);
                byte defaultBaseline = getBaselineFromGraphic(graphic);
                CoreMetrics cm = GraphicComponent.createCoreMetrics(graphic);
                paragraphInit(defaultBaseline, cm, paragraphAttrs, chars);
            }
        }
        textLine = TextLine.standardCreateTextLine(frc, text, chars, baselineOffsets);
    }
    
    private void ensureCache() {
        if (!cacheIsValid) {
            buildCache();
        }
    }
    
    private void buildCache() {
        if (textLine == null) {
            initTextLine();
        }
        lineMetrics = textLine.getMetrics();
        if (textLine.isDirectionLTR()) {
            int lastNonSpace = characterCount - 1;
            while (lastNonSpace != -1) {
                int logIndex = textLine.visualToLogical(lastNonSpace);
                if (!textLine.isCharSpace(logIndex)) {
                    break;
                } else {
                    --lastNonSpace;
                }
            }
            if (lastNonSpace == characterCount - 1) {
                visibleAdvance = lineMetrics.advance;
            } else if (lastNonSpace == -1) {
                visibleAdvance = 0;
            } else {
                int logIndex = textLine.visualToLogical(lastNonSpace);
                visibleAdvance = textLine.getCharLinePosition(logIndex) + textLine.getCharAdvance(logIndex);
            }
        } else {
            int leftmostNonSpace = 0;
            while (leftmostNonSpace != characterCount) {
                int logIndex = textLine.visualToLogical(leftmostNonSpace);
                if (!textLine.isCharSpace(logIndex)) {
                    break;
                } else {
                    ++leftmostNonSpace;
                }
            }
            if (leftmostNonSpace == characterCount) {
                visibleAdvance = 0;
            } else if (leftmostNonSpace == 0) {
                visibleAdvance = lineMetrics.advance;
            } else {
                int logIndex = textLine.visualToLogical(leftmostNonSpace);
                float pos = textLine.getCharLinePosition(logIndex);
                visibleAdvance = lineMetrics.advance - pos;
            }
        }
        naturalBounds = null;
        boundsRect = null;
        hashCodeCache = 0;
        cacheIsValid = true;
    }
    
    private Rectangle2D getNaturalBounds() {
        ensureCache();
        if (naturalBounds == null) {
            naturalBounds = textLine.getItalicBounds();
        }
        return naturalBounds;
    }
    
    protected Object clone() {
        try {
            return super.clone();
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }
    
    private void checkTextHit(TextHitInfo hit) {
        if (hit == null) {
            throw new IllegalArgumentException("TextHitInfo is null.");
        }
        if (hit.getInsertionIndex() < 0 || hit.getInsertionIndex() > characterCount) {
            throw new IllegalArgumentException("TextHitInfo is out of range");
        }
    }
    
    public TextLayout getJustifiedLayout(float justificationWidth) {
        if (justificationWidth <= 0) {
            throw new IllegalArgumentException("justificationWidth <= 0 passed to TextLayout.getJustifiedLayout()");
        }
        if (justifyRatio == ALREADY_JUSTIFIED) {
            throw new Error("Can\'t justify again.");
        }
        ensureCache();
        int limit = characterCount;
        while (limit > 0 && textLine.isCharWhitespace(limit - 1)) {
            --limit;
        }
        TextLine newLine = textLine.getJustifiedLine(justificationWidth, justifyRatio, 0, limit);
        if (newLine != null) {
            return new TextLayout(newLine, baseline, baselineOffsets, ALREADY_JUSTIFIED);
        }
        return this;
    }
    
    protected void handleJustify(float justificationWidth) {
    }
    
    public byte getBaseline() {
        return baseline;
    }
    
    public float[] getBaselineOffsets() {
        float[] offsets = new float[baselineOffsets.length];
        System.arraycopy(baselineOffsets, 0, offsets, 0, offsets.length);
        return offsets;
    }
    
    public float getAdvance() {
        if (optInfo != null) {
            try {
                return optInfo.getAdvance();
            } catch (Error e) {
            }
        }
        ensureCache();
        return lineMetrics.advance;
    }
    
    public float getVisibleAdvance() {
        ensureCache();
        return visibleAdvance;
    }
    
    public float getAscent() {
        if (optInfo != null) {
            return optInfo.getCoreMetrics().ascent;
        }
        ensureCache();
        return lineMetrics.ascent;
    }
    
    public float getDescent() {
        if (optInfo != null) {
            return optInfo.getCoreMetrics().descent;
        }
        ensureCache();
        return lineMetrics.descent;
    }
    
    public float getLeading() {
        if (optInfo != null) {
            return optInfo.getCoreMetrics().leading;
        }
        ensureCache();
        return lineMetrics.leading;
    }
    
    public Rectangle2D getBounds() {
        if (optInfo != null) {
            return optInfo.getVisualBounds();
        }
        ensureCache();
        if (boundsRect == null) {
            Rectangle2D lineBounds = textLine.getBounds();
            if (dx != 0 || dy != 0) {
                lineBounds.setRect(lineBounds.getX() - dx, lineBounds.getY() - dy, lineBounds.getWidth(), lineBounds.getHeight());
            }
            boundsRect = lineBounds;
        }
        Rectangle2D bounds = new Rectangle2D$Float();
        bounds.setRect(boundsRect);
        return bounds;
    }
    
    public boolean isLeftToRight() {
        return (optInfo != null) || textLine.isDirectionLTR();
    }
    
    public boolean isVertical() {
        return isVerticalLine;
    }
    
    public int getCharacterCount() {
        return characterCount;
    }
    
    private float[] getCaretInfo(int caret, Rectangle2D bounds, float[] info) {
        float top1X;
        float top2X;
        float bottom1X;
        float bottom2X;
        if (caret == 0 || caret == characterCount) {
            float pos;
            int logIndex;
            if (caret == characterCount) {
                logIndex = textLine.visualToLogical(characterCount - 1);
                pos = textLine.getCharLinePosition(logIndex) + textLine.getCharAdvance(logIndex);
            } else {
                logIndex = textLine.visualToLogical(caret);
                pos = textLine.getCharLinePosition(logIndex);
            }
            float angle = textLine.getCharAngle(logIndex);
            float shift = textLine.getCharShift(logIndex);
            pos += angle * shift;
            top1X = top2X = pos + angle * textLine.getCharAscent(logIndex);
            bottom1X = bottom2X = pos - angle * textLine.getCharDescent(logIndex);
        } else {
            {
                int logIndex = textLine.visualToLogical(caret - 1);
                float angle1 = textLine.getCharAngle(logIndex);
                float pos1 = textLine.getCharLinePosition(logIndex) + textLine.getCharAdvance(logIndex);
                if (angle1 != 0) {
                    pos1 += angle1 * textLine.getCharShift(logIndex);
                    top1X = pos1 + angle1 * textLine.getCharAscent(logIndex);
                    bottom1X = pos1 - angle1 * textLine.getCharDescent(logIndex);
                } else {
                    top1X = bottom1X = pos1;
                }
            }
            {
                int logIndex = textLine.visualToLogical(caret);
                float angle2 = textLine.getCharAngle(logIndex);
                float pos2 = textLine.getCharLinePosition(logIndex);
                if (angle2 != 0) {
                    pos2 += angle2 * textLine.getCharShift(logIndex);
                    top2X = pos2 + angle2 * textLine.getCharAscent(logIndex);
                    bottom2X = pos2 - angle2 * textLine.getCharDescent(logIndex);
                } else {
                    top2X = bottom2X = pos2;
                }
            }
        }
        float topX = (top1X + top2X) / 2;
        float bottomX = (bottom1X + bottom2X) / 2;
        if (info == null) {
            info = new float[2];
        }
        if (isVerticalLine) {
            info[1] = (float)((topX - bottomX) / bounds.getWidth());
            info[0] = (float)(topX + (info[1] * bounds.getX()));
        } else {
            info[1] = (float)((topX - bottomX) / bounds.getHeight());
            info[0] = (float)(bottomX + (info[1] * bounds.getMaxY()));
        }
        return info;
    }
    
    public float[] getCaretInfo(TextHitInfo hit, Rectangle2D bounds) {
        ensureCache();
        checkTextHit(hit);
        return getCaretInfoTestInternal(hit, bounds);
    }
    
    private float[] getCaretInfoTestInternal(TextHitInfo hit, Rectangle2D bounds) {
        ensureCache();
        checkTextHit(hit);
        float[] info = new float[6];
        getCaretInfo(hitToCaret(hit), bounds, info);
        double iangle;
        double ixbase;
        double p1x;
        double p1y;
        double p2x;
        double p2y;
        int charix = hit.getCharIndex();
        boolean lead = hit.isLeadingEdge();
        boolean ltr = textLine.isDirectionLTR();
        boolean horiz = !isVertical();
        if (charix == -1 || charix == characterCount) {
            TextLine$TextLineMetrics m = textLine.getMetrics();
            boolean low = ltr == (charix == -1);
            iangle = 0;
            if (horiz) {
                p1x = p2x = low ? 0 : m.advance;
                p1y = -m.ascent;
                p2y = m.descent;
            } else {
                p1y = p2y = low ? 0 : m.advance;
                p1x = m.descent;
                p2x = m.ascent;
            }
        } else {
            CoreMetrics thiscm = textLine.getCoreMetricsAt(charix);
            iangle = thiscm.italicAngle;
            ixbase = textLine.getCharLinePosition(charix, lead);
            if (thiscm.baselineIndex < 0) {
                TextLine$TextLineMetrics m = textLine.getMetrics();
                if (horiz) {
                    p1x = p2x = ixbase;
                    if (thiscm.baselineIndex == GraphicAttribute.TOP_ALIGNMENT) {
                        p1y = -m.ascent;
                        p2y = p1y + thiscm.height;
                    } else {
                        p2y = m.descent;
                        p1y = p2y - thiscm.height;
                    }
                } else {
                    p1y = p2y = ixbase;
                    p1x = m.descent;
                    p2x = m.ascent;
                }
            } else {
                float bo = baselineOffsets[thiscm.baselineIndex];
                if (horiz) {
                    ixbase += iangle * thiscm.ssOffset;
                    p1x = ixbase + iangle * thiscm.ascent;
                    p2x = ixbase - iangle * thiscm.descent;
                    p1y = bo - thiscm.ascent;
                    p2y = bo + thiscm.descent;
                } else {
                    ixbase -= iangle * thiscm.ssOffset;
                    p1y = ixbase + iangle * thiscm.ascent;
                    p2y = ixbase - iangle * thiscm.descent;
                    p1x = bo + thiscm.ascent;
                    p2x = bo + thiscm.descent;
                }
            }
        }
        info[2] = (float)p1x;
        info[3] = (float)p1y;
        info[4] = (float)p2x;
        info[5] = (float)p2y;
        return info;
    }
    
    public float[] getCaretInfo(TextHitInfo hit) {
        return getCaretInfo(hit, getNaturalBounds());
    }
    
    private int hitToCaret(TextHitInfo hit) {
        int hitIndex = hit.getCharIndex();
        if (hitIndex < 0) {
            return textLine.isDirectionLTR() ? 0 : characterCount;
        } else if (hitIndex >= characterCount) {
            return textLine.isDirectionLTR() ? characterCount : 0;
        }
        int visIndex = textLine.logicalToVisual(hitIndex);
        if (hit.isLeadingEdge() != textLine.isCharLTR(hitIndex)) {
            ++visIndex;
        }
        return visIndex;
    }
    
    private TextHitInfo caretToHit(int caret) {
        if (caret == 0 || caret == characterCount) {
            if ((caret == characterCount) == textLine.isDirectionLTR()) {
                return TextHitInfo.leading(characterCount);
            } else {
                return TextHitInfo.trailing(-1);
            }
        } else {
            int charIndex = textLine.visualToLogical(caret);
            boolean leading = textLine.isCharLTR(charIndex);
            return leading ? TextHitInfo.leading(charIndex) : TextHitInfo.trailing(charIndex);
        }
    }
    
    private boolean caretIsValid(int caret) {
        if (caret == characterCount || caret == 0) {
            return true;
        }
        int offset = textLine.visualToLogical(caret);
        if (!textLine.isCharLTR(offset)) {
            offset = textLine.visualToLogical(caret - 1);
            if (textLine.isCharLTR(offset)) {
                return true;
            }
        }
        return textLine.caretAtOffsetIsValid(offset);
    }
    
    public TextHitInfo getNextRightHit(TextHitInfo hit) {
        ensureCache();
        checkTextHit(hit);
        int caret = hitToCaret(hit);
        if (caret == characterCount) {
            return null;
        }
        do {
            ++caret;
        }         while (!caretIsValid(caret));
        return caretToHit(caret);
    }
    
    public TextHitInfo getNextRightHit(int offset, TextLayout$CaretPolicy policy) {
        if (offset < 0 || offset > characterCount) {
            throw new IllegalArgumentException("Offset out of bounds in TextLayout.getNextRightHit()");
        }
        if (policy == null) {
            throw new IllegalArgumentException("Null CaretPolicy passed to TextLayout.getNextRightHit()");
        }
        TextHitInfo hit1 = TextHitInfo.afterOffset(offset);
        TextHitInfo hit2 = hit1.getOtherHit();
        TextHitInfo nextHit = getNextRightHit(policy.getStrongCaret(hit1, hit2, this));
        if (nextHit != null) {
            TextHitInfo otherHit = getVisualOtherHit(nextHit);
            return policy.getStrongCaret(otherHit, nextHit, this);
        } else {
            return null;
        }
    }
    
    public TextHitInfo getNextRightHit(int offset) {
        return getNextRightHit(offset, DEFAULT_CARET_POLICY);
    }
    
    public TextHitInfo getNextLeftHit(TextHitInfo hit) {
        ensureCache();
        checkTextHit(hit);
        int caret = hitToCaret(hit);
        if (caret == 0) {
            return null;
        }
        do {
            --caret;
        }         while (!caretIsValid(caret));
        return caretToHit(caret);
    }
    
    public TextHitInfo getNextLeftHit(int offset, TextLayout$CaretPolicy policy) {
        if (policy == null) {
            throw new IllegalArgumentException("Null CaretPolicy passed to TextLayout.getNextLeftHit()");
        }
        if (offset < 0 || offset > characterCount) {
            throw new IllegalArgumentException("Offset out of bounds in TextLayout.getNextLeftHit()");
        }
        TextHitInfo hit1 = TextHitInfo.afterOffset(offset);
        TextHitInfo hit2 = hit1.getOtherHit();
        TextHitInfo nextHit = getNextLeftHit(policy.getStrongCaret(hit1, hit2, this));
        if (nextHit != null) {
            TextHitInfo otherHit = getVisualOtherHit(nextHit);
            return policy.getStrongCaret(otherHit, nextHit, this);
        } else {
            return null;
        }
    }
    
    public TextHitInfo getNextLeftHit(int offset) {
        return getNextLeftHit(offset, DEFAULT_CARET_POLICY);
    }
    
    public TextHitInfo getVisualOtherHit(TextHitInfo hit) {
        ensureCache();
        checkTextHit(hit);
        int hitCharIndex = hit.getCharIndex();
        int charIndex;
        boolean leading;
        if (hitCharIndex == -1 || hitCharIndex == characterCount) {
            int visIndex;
            if (textLine.isDirectionLTR() == (hitCharIndex == -1)) {
                visIndex = 0;
            } else {
                visIndex = characterCount - 1;
            }
            charIndex = textLine.visualToLogical(visIndex);
            if (textLine.isDirectionLTR() == (hitCharIndex == -1)) {
                leading = textLine.isCharLTR(charIndex);
            } else {
                leading = !textLine.isCharLTR(charIndex);
            }
        } else {
            int visIndex = textLine.logicalToVisual(hitCharIndex);
            boolean movedToRight;
            if (textLine.isCharLTR(hitCharIndex) == hit.isLeadingEdge()) {
                --visIndex;
                movedToRight = false;
            } else {
                ++visIndex;
                movedToRight = true;
            }
            if (visIndex > -1 && visIndex < characterCount) {
                charIndex = textLine.visualToLogical(visIndex);
                leading = movedToRight == textLine.isCharLTR(charIndex);
            } else {
                charIndex = (movedToRight == textLine.isDirectionLTR()) ? characterCount : -1;
                leading = charIndex == characterCount;
            }
        }
        return leading ? TextHitInfo.leading(charIndex) : TextHitInfo.trailing(charIndex);
    }
    
    private double[] getCaretPath(TextHitInfo hit, Rectangle2D bounds) {
        float[] info = getCaretInfo(hit, bounds);
        return new double[]{info[2], info[3], info[4], info[5]};
    }
    
    private double[] getCaretPath(int caret, Rectangle2D bounds, boolean clipToBounds) {
        float[] info = getCaretInfo(caret, bounds, null);
        double pos = info[0];
        double slope = info[1];
        double x0;
        double y0;
        double x1;
        double y1;
        double x2 = -3141.59;
        double y2 = -2.7;
        double left = bounds.getX();
        double right = left + bounds.getWidth();
        double top = bounds.getY();
        double bottom = top + bounds.getHeight();
        boolean threePoints = false;
        if (isVerticalLine) {
            if (slope >= 0) {
                x0 = left;
                x1 = right;
            } else {
                x1 = left;
                x0 = right;
            }
            y0 = pos + x0 * slope;
            y1 = pos + x1 * slope;
            if (clipToBounds) {
                if (y0 < top) {
                    if (slope <= 0 || y1 <= top) {
                        y0 = y1 = top;
                    } else {
                        threePoints = true;
                        y0 = top;
                        y2 = top;
                        x2 = x1 + (top - y1) / slope;
                        if (y1 > bottom) {
                            y1 = bottom;
                        }
                    }
                } else if (y1 > bottom) {
                    if (slope >= 0 || y0 >= bottom) {
                        y0 = y1 = bottom;
                    } else {
                        threePoints = true;
                        y1 = bottom;
                        y2 = bottom;
                        x2 = x0 + (bottom - x1) / slope;
                    }
                }
            }
        } else {
            if (slope >= 0) {
                y0 = bottom;
                y1 = top;
            } else {
                y1 = bottom;
                y0 = top;
            }
            x0 = pos - y0 * slope;
            x1 = pos - y1 * slope;
            if (clipToBounds) {
                if (x0 < left) {
                    if (slope <= 0 || x1 <= left) {
                        x0 = x1 = left;
                    } else {
                        threePoints = true;
                        x0 = left;
                        x2 = left;
                        y2 = y1 - (left - x1) / slope;
                        if (x1 > right) {
                            x1 = right;
                        }
                    }
                } else if (x1 > right) {
                    if (slope >= 0 || x0 >= right) {
                        x0 = x1 = right;
                    } else {
                        threePoints = true;
                        x1 = right;
                        x2 = right;
                        y2 = y0 - (right - x0) / slope;
                    }
                }
            }
        }
        return threePoints ? new double[]{x0, y0, x2, y2, x1, y1} : new double[]{x0, y0, x1, y1};
    }
    
    private static GeneralPath pathToShape(double[] path, boolean close) {
        GeneralPath result = new GeneralPath(GeneralPath.WIND_EVEN_ODD, path.length);
        result.moveTo((float)path[0], (float)path[1]);
        for (int i = 2; i < path.length; i += 2) {
            result.lineTo((float)path[i], (float)path[i + 1]);
        }
        if (close) {
            result.closePath();
        }
        return result;
    }
    
    public Shape getCaretShape(TextHitInfo hit, Rectangle2D bounds) {
        ensureCache();
        checkTextHit(hit);
        if (bounds == null) {
            throw new IllegalArgumentException("Null Rectangle2D passed to TextLayout.getCaret()");
        }
        return pathToShape(getCaretPath(hit, bounds), false);
    }
    
    public Shape getCaretShape(TextHitInfo hit) {
        return getCaretShape(hit, getNaturalBounds());
    }
    
    private final TextHitInfo getStrongHit(TextHitInfo hit1, TextHitInfo hit2) {
        byte hit1Level = getCharacterLevel(hit1.getCharIndex());
        byte hit2Level = getCharacterLevel(hit2.getCharIndex());
        if (hit1Level == hit2Level) {
            if (hit2.isLeadingEdge() && !hit1.isLeadingEdge()) {
                return hit2;
            } else {
                return hit1;
            }
        } else {
            return (hit1Level < hit2Level) ? hit1 : hit2;
        }
    }
    
    public byte getCharacterLevel(int index) {
        if (index < -1 || index > characterCount) {
            throw new IllegalArgumentException("Index is out of range in getCharacterLevel.");
        }
        if (optInfo != null) {
            return 0;
        }
        ensureCache();
        if (index == -1 || index == characterCount) {
            return (byte)(textLine.isDirectionLTR() ? 0 : 1);
        }
        return textLine.getCharLevel(index);
    }
    
    public Shape[] getCaretShapes(int offset, Rectangle2D bounds, TextLayout$CaretPolicy policy) {
        ensureCache();
        if (offset < 0 || offset > characterCount) {
            throw new IllegalArgumentException("Offset out of bounds in TextLayout.getCaretShapes()");
        }
        if (bounds == null) {
            throw new IllegalArgumentException("Null Rectangle2D passed to TextLayout.getCaretShapes()");
        }
        if (policy == null) {
            throw new IllegalArgumentException("Null CaretPolicy passed to TextLayout.getCaretShapes()");
        }
        Shape[] result = new Shape[2];
        TextHitInfo hit = TextHitInfo.afterOffset(offset);
        int hitCaret = hitToCaret(hit);
        Shape hitShape = pathToShape(getCaretPath(hit, bounds), false);
        TextHitInfo otherHit = hit.getOtherHit();
        int otherCaret = hitToCaret(otherHit);
        if (hitCaret == otherCaret) {
            result[0] = hitShape;
        } else {
            Shape otherShape = pathToShape(getCaretPath(otherHit, bounds), false);
            TextHitInfo strongHit = policy.getStrongCaret(hit, otherHit, this);
            boolean hitIsStrong = strongHit.equals(hit);
            if (hitIsStrong) {
                result[0] = hitShape;
                result[1] = otherShape;
            } else {
                result[0] = otherShape;
                result[1] = hitShape;
            }
        }
        return result;
    }
    
    public Shape[] getCaretShapes(int offset, Rectangle2D bounds) {
        return getCaretShapes(offset, bounds, DEFAULT_CARET_POLICY);
    }
    
    public Shape[] getCaretShapes(int offset) {
        return getCaretShapes(offset, getNaturalBounds(), DEFAULT_CARET_POLICY);
    }
    
    private GeneralPath boundingShape(double[] path0, double[] path1) {
        GeneralPath result = pathToShape(path0, false);
        boolean sameDirection;
        if (isVerticalLine) {
            sameDirection = (path0[1] > path0[path0.length - 1]) == (path1[1] > path1[path1.length - 1]);
        } else {
            sameDirection = (path0[0] > path0[path0.length - 2]) == (path1[0] > path1[path1.length - 2]);
        }
        int start;
        int limit;
        int increment;
        if (sameDirection) {
            start = path1.length - 2;
            limit = -2;
            increment = -2;
        } else {
            start = 0;
            limit = path1.length;
            increment = 2;
        }
        for (int i = start; i != limit; i += increment) {
            result.lineTo((float)path1[i], (float)path1[i + 1]);
        }
        result.closePath();
        return result;
    }
    
    private GeneralPath caretBoundingShape(int caret0, int caret1, Rectangle2D bounds) {
        if (caret0 > caret1) {
            int temp = caret0;
            caret0 = caret1;
            caret1 = temp;
        }
        return boundingShape(getCaretPath(caret0, bounds, true), getCaretPath(caret1, bounds, true));
    }
    
    private GeneralPath leftShape(Rectangle2D bounds) {
        double[] path0;
        if (isVerticalLine) {
            path0 = new double[]{bounds.getX(), bounds.getY(), bounds.getX() + bounds.getWidth(), bounds.getY()};
        } else {
            path0 = new double[]{bounds.getX(), bounds.getY() + bounds.getHeight(), bounds.getX(), bounds.getY()};
        }
        double[] path1 = getCaretPath(0, bounds, true);
        return boundingShape(path0, path1);
    }
    
    private GeneralPath rightShape(Rectangle2D bounds) {
        double[] path1;
        if (isVerticalLine) {
            path1 = new double[]{bounds.getX(), bounds.getY() + bounds.getHeight(), bounds.getX() + bounds.getWidth(), bounds.getY() + bounds.getHeight()};
        } else {
            path1 = new double[]{bounds.getX() + bounds.getWidth(), bounds.getY() + bounds.getHeight(), bounds.getX() + bounds.getWidth(), bounds.getY()};
        }
        double[] path0 = getCaretPath(characterCount, bounds, true);
        return boundingShape(path0, path1);
    }
    
    public int[] getLogicalRangesForVisualSelection(TextHitInfo firstEndpoint, TextHitInfo secondEndpoint) {
        ensureCache();
        checkTextHit(firstEndpoint);
        checkTextHit(secondEndpoint);
        boolean[] included = new boolean[characterCount];
        int startIndex = hitToCaret(firstEndpoint);
        int limitIndex = hitToCaret(secondEndpoint);
        if (startIndex > limitIndex) {
            int t = startIndex;
            startIndex = limitIndex;
            limitIndex = t;
        }
        if (startIndex < limitIndex) {
            int visIndex = startIndex;
            while (visIndex < limitIndex) {
                included[textLine.visualToLogical(visIndex)] = true;
                ++visIndex;
            }
        }
        int count = 0;
        boolean inrun = false;
        for (int i = 0; i < characterCount; i++) {
            if (included[i] != inrun) {
                inrun = !inrun;
                if (inrun) {
                    count++;
                }
            }
        }
        int[] ranges = new int[count * 2];
        count = 0;
        inrun = false;
        for (int i = 0; i < characterCount; i++) {
            if (included[i] != inrun) {
                ranges[count++] = i;
                inrun = !inrun;
            }
        }
        if (inrun) {
            ranges[count++] = characterCount;
        }
        return ranges;
    }
    
    public Shape getVisualHighlightShape(TextHitInfo firstEndpoint, TextHitInfo secondEndpoint, Rectangle2D bounds) {
        ensureCache();
        checkTextHit(firstEndpoint);
        checkTextHit(secondEndpoint);
        if (bounds == null) {
            throw new IllegalArgumentException("Null Rectangle2D passed to TextLayout.getVisualHighlightShape()");
        }
        GeneralPath result = new GeneralPath(GeneralPath.WIND_EVEN_ODD);
        int firstCaret = hitToCaret(firstEndpoint);
        int secondCaret = hitToCaret(secondEndpoint);
        result.append(caretBoundingShape(firstCaret, secondCaret, bounds), false);
        if (firstCaret == 0 || secondCaret == 0) {
            result.append(leftShape(bounds), false);
        }
        if (firstCaret == characterCount || secondCaret == characterCount) {
            result.append(rightShape(bounds), false);
        }
        return result;
    }
    
    public Shape getVisualHighlightShape(TextHitInfo firstEndpoint, TextHitInfo secondEndpoint) {
        return getVisualHighlightShape(firstEndpoint, secondEndpoint, getNaturalBounds());
    }
    
    public Shape getLogicalHighlightShape(int firstEndpoint, int secondEndpoint, Rectangle2D bounds) {
        if (bounds == null) {
            throw new IllegalArgumentException("Null Rectangle2D passed to TextLayout.getLogicalHighlightShape()");
        }
        ensureCache();
        if (firstEndpoint > secondEndpoint) {
            int t = firstEndpoint;
            firstEndpoint = secondEndpoint;
            secondEndpoint = t;
        }
        if (firstEndpoint < 0 || secondEndpoint > characterCount) {
            throw new IllegalArgumentException("Range is invalid in TextLayout.getLogicalHighlightShape()");
        }
        GeneralPath result = new GeneralPath(GeneralPath.WIND_EVEN_ODD);
        int[] carets = new int[10];
        int count = 0;
        if (firstEndpoint < secondEndpoint) {
            int logIndex = firstEndpoint;
            do {
                carets[count++] = hitToCaret(TextHitInfo.leading(logIndex));
                boolean ltr = textLine.isCharLTR(logIndex);
                do {
                    logIndex++;
                }                 while (logIndex < secondEndpoint && textLine.isCharLTR(logIndex) == ltr);
                int hitCh = logIndex;
                carets[count++] = hitToCaret(TextHitInfo.trailing(hitCh - 1));
                if (count == carets.length) {
                    int[] temp = new int[carets.length + 10];
                    System.arraycopy(carets, 0, temp, 0, count);
                    carets = temp;
                }
            }             while (logIndex < secondEndpoint);
        } else {
            count = 2;
            carets[0] = carets[1] = hitToCaret(TextHitInfo.leading(firstEndpoint));
        }
        for (int i = 0; i < count; i += 2) {
            result.append(caretBoundingShape(carets[i], carets[i + 1], bounds), false);
        }
        if (firstEndpoint != secondEndpoint) {
            if ((textLine.isDirectionLTR() && firstEndpoint == 0) || (!textLine.isDirectionLTR() && secondEndpoint == characterCount)) {
                result.append(leftShape(bounds), false);
            }
            if ((textLine.isDirectionLTR() && secondEndpoint == characterCount) || (!textLine.isDirectionLTR() && firstEndpoint == 0)) {
                result.append(rightShape(bounds), false);
            }
        }
        return result;
    }
    
    public Shape getLogicalHighlightShape(int firstEndpoint, int secondEndpoint) {
        return getLogicalHighlightShape(firstEndpoint, secondEndpoint, getNaturalBounds());
    }
    
    public Shape getBlackBoxBounds(int firstEndpoint, int secondEndpoint) {
        ensureCache();
        if (firstEndpoint > secondEndpoint) {
            int t = firstEndpoint;
            firstEndpoint = secondEndpoint;
            secondEndpoint = t;
        }
        if (firstEndpoint < 0 || secondEndpoint > characterCount) {
            throw new IllegalArgumentException("Invalid range passed to TextLayout.getBlackBoxBounds()");
        }
        GeneralPath result = new GeneralPath(GeneralPath.WIND_NON_ZERO);
        if (firstEndpoint < characterCount) {
            for (int logIndex = firstEndpoint; logIndex < secondEndpoint; logIndex++) {
                Rectangle2D r = textLine.getCharBounds(logIndex);
                if (!r.isEmpty()) {
                    result.append(r, false);
                }
            }
        }
        if (dx != 0 || dy != 0) {
            AffineTransform translate = new AffineTransform();
            translate.setToTranslation(dx, dy);
            result = (GeneralPath)(GeneralPath)result.createTransformedShape(translate);
        }
        return result;
    }
    
    private float caretToPointDistance(float[] caretInfo, float x, float y) {
        float lineDistance = isVerticalLine ? y : x;
        float distanceOffBaseline = isVerticalLine ? -x : y;
        return lineDistance - caretInfo[0] + (distanceOffBaseline * caretInfo[1]);
    }
    
    public TextHitInfo hitTestChar(float x, float y, Rectangle2D bounds) {
        if (isVertical()) {
            if (y < bounds.getMinY()) {
                return TextHitInfo.leading(0);
            } else if (y >= bounds.getMaxY()) {
                return TextHitInfo.trailing(characterCount - 1);
            }
        } else {
            if (x < bounds.getMinX()) {
                return isLeftToRight() ? TextHitInfo.leading(0) : TextHitInfo.trailing(characterCount - 1);
            } else if (x >= bounds.getMaxX()) {
                return isLeftToRight() ? TextHitInfo.trailing(characterCount - 1) : TextHitInfo.leading(0);
            }
        }
        double distance = Double.MAX_VALUE;
        int index = 0;
        int trail = -1;
        CoreMetrics lcm = null;
        float icx = 0;
        float icy = 0;
        float ia = 0;
        float cy = 0;
        float dya = 0;
        float ydsq = 0;
        for (int i = 0; i < characterCount; ++i) {
            if (!textLine.caretAtOffsetIsValid(i)) {
                continue;
            }
            if (trail == -1) {
                trail = i;
            }
            CoreMetrics cm = textLine.getCoreMetricsAt(i);
            if (cm != lcm) {
                lcm = cm;
                if (cm.baselineIndex == GraphicAttribute.TOP_ALIGNMENT) {
                    cy = -(textLine.getMetrics().ascent - cm.ascent) + cm.ssOffset;
                } else if (cm.baselineIndex == GraphicAttribute.BOTTOM_ALIGNMENT) {
                    cy = textLine.getMetrics().descent - cm.descent + cm.ssOffset;
                } else {
                    cy = cm.effectiveBaselineOffset(baselineOffsets) + cm.ssOffset;
                }
                float dy = (cm.descent - cm.ascent) / 2 - cy;
                dya = dy * cm.italicAngle;
                cy += dy;
                ydsq = (cy - y) * (cy - y);
            }
            float cx = textLine.getCharXPosition(i);
            float ca = textLine.getCharAdvance(i);
            float dx = ca / 2;
            cx += dx - dya;
            double nd = Math.sqrt(4 * (cx - x) * (cx - x) + ydsq);
            if (nd < distance) {
                distance = nd;
                index = i;
                trail = -1;
                icx = cx;
                icy = cy;
                ia = cm.italicAngle;
            }
        }
        boolean left = x < icx - (y - icy) * ia;
        boolean leading = textLine.isCharLTR(index) == left;
        if (trail == -1) {
            trail = characterCount;
        }
        TextHitInfo result = leading ? TextHitInfo.leading(index) : TextHitInfo.trailing(trail - 1);
        return result;
    }
    
    public TextHitInfo hitTestChar(float x, float y) {
        return hitTestChar(x, y, getNaturalBounds());
    }
    
    public int hashCode() {
        if (hashCodeCache == 0) {
            ensureCache();
            hashCodeCache = textLine.hashCode();
        }
        return hashCodeCache;
    }
    
    public boolean equals(Object obj) {
        return (obj instanceof TextLayout) && equals((TextLayout)(TextLayout)obj);
    }
    
    public boolean equals(TextLayout rhs) {
        if (rhs == null) {
            return false;
        }
        if (rhs == this) {
            return true;
        }
        ensureCache();
        return textLine.equals(rhs.textLine);
    }
    
    public String toString() {
        ensureCache();
        return textLine.toString();
    }
    
    public void draw(Graphics2D g2, float x, float y) {
        if (g2 == null) {
            throw new IllegalArgumentException("Null Graphics2D passed to TextLayout.draw()");
        }
        if (optInfo != null) {
            if (optInfo.draw(g2, x, y)) {
                return;
            }
            initTextLine();
        }
        textLine.draw(g2, x - dx, y - dy);
    }
    
    TextLine getTextLineForTesting() {
        return textLine;
    }
    
    private static int sameBaselineUpTo(Font font, char[] text, int start, int limit) {
        return limit;
    }
    
    static byte getBaselineFromGraphic(GraphicAttribute graphic) {
        byte alignment = (byte)graphic.getAlignment();
        if (alignment == GraphicAttribute.BOTTOM_ALIGNMENT || alignment == GraphicAttribute.TOP_ALIGNMENT) {
            return (byte)GraphicAttribute.ROMAN_BASELINE;
        } else {
            return alignment;
        }
    }
    
    public Shape getOutline(AffineTransform tx) {
        ensureCache();
        return textLine.getOutline(tx);
    }
}
