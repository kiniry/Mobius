package java.awt.font;

import java.awt.Font;
import java.awt.Graphics2D;
import java.awt.Shape;
import java.awt.geom.Rectangle2D;
import java.awt.geom.AffineTransform;
import java.awt.geom.GeneralPath;
import java.text.AttributedCharacterIterator;
import java.text.Bidi;
import java.util.Map;
import sun.font.BidiUtils;
import sun.font.CoreMetrics;
import sun.font.Decoration;
import sun.font.FontResolver;
import sun.font.GraphicComponent;
import sun.font.TextLabelFactory;
import sun.font.TextLineComponent;
import sun.text.CodePointIterator;

final class TextLine {
    
    /*synthetic*/ static float access$400(TextLine x0, int x1) {
        return x0.getComponentShift(x1);
    }
    
    /*synthetic*/ static float[] access$300(TextLine x0) {
        return x0.locs;
    }
    
    /*synthetic*/ static int[] access$200(TextLine x0) {
        return x0.fComponentVisualOrder;
    }
    
    /*synthetic*/ static TextLineComponent[] access$100(TextLine x0) {
        return x0.fComponents;
    }
    {
    }
    private TextLineComponent[] fComponents;
    private float[] fBaselineOffsets;
    private int[] fComponentVisualOrder;
    private float[] locs;
    private char[] fChars;
    private int fCharsStart;
    private int fCharsLimit;
    private int[] fCharVisualOrder;
    private int[] fCharLogicalOrder;
    private byte[] fCharLevels;
    private boolean fIsDirectionLTR;
    private TextLine$TextLineMetrics fMetrics = null;
    
    public TextLine(TextLineComponent[] components, float[] baselineOffsets, char[] chars, int charsStart, int charsLimit, int[] charLogicalOrder, byte[] charLevels, boolean isDirectionLTR) {
        
        int[] componentVisualOrder = computeComponentOrder(components, charLogicalOrder);
        fComponents = components;
        fBaselineOffsets = baselineOffsets;
        fComponentVisualOrder = componentVisualOrder;
        fChars = chars;
        fCharsStart = charsStart;
        fCharsLimit = charsLimit;
        fCharLogicalOrder = charLogicalOrder;
        fCharLevels = charLevels;
        fIsDirectionLTR = isDirectionLTR;
        checkCtorArgs();
        init();
    }
    
    private void checkCtorArgs() {
        int checkCharCount = 0;
        for (int i = 0; i < fComponents.length; i++) {
            checkCharCount += fComponents[i].getNumCharacters();
        }
        if (checkCharCount != this.characterCount()) {
            throw new IllegalArgumentException("Invalid TextLine!  char count is different from sum of char counts of components.");
        }
    }
    
    private void init() {
        float ascent = 0;
        float descent = 0;
        float leading = 0;
        float advance = 0;
        float maxGraphicHeight = 0;
        float maxGraphicHeightWithLeading = 0;
        TextLineComponent tlc;
        boolean fitTopAndBottomGraphics = false;
        for (int i = 0; i < fComponents.length; i++) {
            tlc = fComponents[i];
            CoreMetrics cm = tlc.getCoreMetrics();
            byte baseline = (byte)cm.baselineIndex;
            if (baseline >= 0) {
                float baselineOffset = fBaselineOffsets[baseline];
                ascent = Math.max(ascent, -baselineOffset + cm.ascent);
                float gd = baselineOffset + cm.descent;
                descent = Math.max(descent, gd);
                leading = Math.max(leading, gd + cm.leading);
            } else {
                fitTopAndBottomGraphics = true;
                float graphicHeight = cm.ascent + cm.descent;
                float graphicHeightWithLeading = graphicHeight + cm.leading;
                maxGraphicHeight = Math.max(maxGraphicHeight, graphicHeight);
                maxGraphicHeightWithLeading = Math.max(maxGraphicHeightWithLeading, graphicHeightWithLeading);
            }
        }
        if (fitTopAndBottomGraphics) {
            if (maxGraphicHeight > ascent + descent) {
                descent = maxGraphicHeight - ascent;
            }
            if (maxGraphicHeightWithLeading > ascent + leading) {
                leading = maxGraphicHeightWithLeading - ascent;
            }
        }
        leading -= descent;
        if (fitTopAndBottomGraphics) {
            fBaselineOffsets = new float[]{fBaselineOffsets[0], fBaselineOffsets[1], fBaselineOffsets[2], descent, -ascent};
        }
        float x = 0;
        float y = 0;
        CoreMetrics pcm = null;
        locs = new float[fComponents.length * 2 + 2];
        for (int i = 0, n = 0; i < fComponents.length; ++i, n += 2) {
            int vi = fComponentVisualOrder == null ? i : fComponentVisualOrder[i];
            tlc = fComponents[vi];
            CoreMetrics cm = tlc.getCoreMetrics();
            if ((pcm != null) && (pcm.italicAngle != 0 || cm.italicAngle != 0) && (pcm.italicAngle != cm.italicAngle || pcm.baselineIndex != cm.baselineIndex || pcm.ssOffset != cm.ssOffset)) {
                float pb = pcm.effectiveBaselineOffset(fBaselineOffsets);
                float pa = pb - pcm.ascent;
                float pd = pb + pcm.descent;
                pb += pcm.ssOffset;
                float cb = cm.effectiveBaselineOffset(fBaselineOffsets);
                float ca = cb - cm.ascent;
                float cd = cb + cm.descent;
                cb += cm.ssOffset;
                float a = Math.max(pa, ca);
                float d = Math.min(pd, cd);
                float pax = pcm.italicAngle * (pb - a);
                float pdx = pcm.italicAngle * (pb - d);
                float cax = cm.italicAngle * (cb - a);
                float cdx = cm.italicAngle * (cb - d);
                float dax = pax - cax;
                float ddx = pdx - cdx;
                float dx = Math.max(dax, ddx);
                x += dx;
                y = cb;
            } else {
                y = cm.effectiveBaselineOffset(fBaselineOffsets) + cm.ssOffset;
            }
            locs[n] = x;
            locs[n + 1] = y;
            x += tlc.getAdvance();
            pcm = cm;
        }
        if (pcm.italicAngle != 0) {
            float pb = pcm.effectiveBaselineOffset(fBaselineOffsets);
            float pa = pb - pcm.ascent;
            float pd = pb + pcm.descent;
            pb += pcm.ssOffset;
            float d;
            if (pcm.italicAngle > 0) {
                d = pb + pcm.ascent;
            } else {
                d = pb - pcm.descent;
            }
            d *= pcm.italicAngle;
            x += d;
        }
        locs[locs.length - 2] = x;
        advance = x;
        fMetrics = new TextLine$TextLineMetrics(ascent, descent, leading, advance);
    }
    {
    }
    private static TextLine$Function fgPosAdvF = new TextLine$1();
    private static TextLine$Function fgAdvanceF = new TextLine$2();
    private static TextLine$Function fgXPositionF = new TextLine$3();
    private static TextLine$Function fgYPositionF = new TextLine$4();
    
    public int characterCount() {
        return fCharsLimit - fCharsStart;
    }
    
    public boolean isDirectionLTR() {
        return fIsDirectionLTR;
    }
    
    public TextLine$TextLineMetrics getMetrics() {
        return fMetrics;
    }
    
    public int visualToLogical(int visualIndex) {
        if (fCharLogicalOrder == null) {
            return visualIndex;
        }
        if (fCharVisualOrder == null) {
            fCharVisualOrder = BidiUtils.createInverseMap(fCharLogicalOrder);
        }
        return fCharVisualOrder[visualIndex];
    }
    
    public int logicalToVisual(int logicalIndex) {
        return (fCharLogicalOrder == null) ? logicalIndex : fCharLogicalOrder[logicalIndex];
    }
    
    public byte getCharLevel(int logicalIndex) {
        return fCharLevels == null ? 0 : fCharLevels[logicalIndex];
    }
    
    public boolean isCharLTR(int logicalIndex) {
        return (getCharLevel(logicalIndex) & 1) == 0;
    }
    
    public int getCharType(int logicalIndex) {
        return Character.getType(fChars[logicalIndex + fCharsStart]);
    }
    
    public boolean isCharSpace(int logicalIndex) {
        return Character.isSpaceChar(fChars[logicalIndex + fCharsStart]);
    }
    
    public boolean isCharWhitespace(int logicalIndex) {
        return Character.isWhitespace(fChars[logicalIndex + fCharsStart]);
    }
    
    public float getCharAngle(int logicalIndex) {
        return getCoreMetricsAt(logicalIndex).italicAngle;
    }
    
    public CoreMetrics getCoreMetricsAt(int logicalIndex) {
        if (logicalIndex < 0) {
            throw new IllegalArgumentException("Negative logicalIndex.");
        }
        if (logicalIndex > fCharsLimit - fCharsStart) {
            throw new IllegalArgumentException("logicalIndex too large.");
        }
        int currentTlc = 0;
        int tlcStart = 0;
        int tlcLimit = 0;
        do {
            tlcLimit += fComponents[currentTlc].getNumCharacters();
            if (tlcLimit > logicalIndex) {
                break;
            }
            ++currentTlc;
            tlcStart = tlcLimit;
        }         while (currentTlc < fComponents.length);
        return fComponents[currentTlc].getCoreMetrics();
    }
    
    public float getCharAscent(int logicalIndex) {
        return getCoreMetricsAt(logicalIndex).ascent;
    }
    
    public float getCharDescent(int logicalIndex) {
        return getCoreMetricsAt(logicalIndex).descent;
    }
    
    public float getCharShift(int logicalIndex) {
        return getCoreMetricsAt(logicalIndex).ssOffset;
    }
    
    private float applyFunctionAtIndex(int logicalIndex, TextLine$Function f) {
        if (logicalIndex < 0) {
            throw new IllegalArgumentException("Negative logicalIndex.");
        }
        int tlcStart = 0;
        for (int i = 0; i < fComponents.length; i++) {
            int tlcLimit = tlcStart + fComponents[i].getNumCharacters();
            if (tlcLimit > logicalIndex) {
                return f.computeFunction(this, i, logicalIndex - tlcStart);
            } else {
                tlcStart = tlcLimit;
            }
        }
        throw new IllegalArgumentException("logicalIndex too large.");
    }
    
    public float getCharAdvance(int logicalIndex) {
        return applyFunctionAtIndex(logicalIndex, fgAdvanceF);
    }
    
    public float getCharXPosition(int logicalIndex) {
        return applyFunctionAtIndex(logicalIndex, fgXPositionF);
    }
    
    public float getCharYPosition(int logicalIndex) {
        return applyFunctionAtIndex(logicalIndex, fgYPositionF);
    }
    
    public float getCharLinePosition(int logicalIndex) {
        return getCharXPosition(logicalIndex);
    }
    
    public float getCharLinePosition(int logicalIndex, boolean leading) {
        TextLine$Function f = isCharLTR(logicalIndex) == leading ? fgXPositionF : fgPosAdvF;
        return applyFunctionAtIndex(logicalIndex, f);
    }
    
    public boolean caretAtOffsetIsValid(int offset) {
        if (offset < 0) {
            throw new IllegalArgumentException("Negative offset.");
        }
        int tlcStart = 0;
        for (int i = 0; i < fComponents.length; i++) {
            int tlcLimit = tlcStart + fComponents[i].getNumCharacters();
            if (tlcLimit > offset) {
                return fComponents[i].caretAtOffsetIsValid(offset - tlcStart);
            } else {
                tlcStart = tlcLimit;
            }
        }
        throw new IllegalArgumentException("logicalIndex too large.");
    }
    
    public Rectangle2D getCharBounds(int logicalIndex) {
        if (logicalIndex < 0) {
            throw new IllegalArgumentException("Negative logicalIndex.");
        }
        int tlcStart = 0;
        for (int i = 0; i < fComponents.length; i++) {
            int tlcLimit = tlcStart + fComponents[i].getNumCharacters();
            if (tlcLimit > logicalIndex) {
                TextLineComponent tlc = fComponents[i];
                int indexInTlc = logicalIndex - tlcStart;
                Rectangle2D chBounds = tlc.getCharVisualBounds(indexInTlc);
                int vi = fComponentVisualOrder == null ? i : fComponentVisualOrder[i];
                chBounds.setRect(chBounds.getX() + locs[vi * 2], chBounds.getY() + locs[vi * 2 + 1], chBounds.getWidth(), chBounds.getHeight());
                return chBounds;
            } else {
                tlcStart = tlcLimit;
            }
        }
        throw new IllegalArgumentException("logicalIndex too large.");
    }
    
    private float getComponentShift(int index) {
        CoreMetrics cm = fComponents[index].getCoreMetrics();
        return cm.effectiveBaselineOffset(fBaselineOffsets);
    }
    
    public void draw(Graphics2D g2, float x, float y) {
        for (int i = 0, n = 0; i < fComponents.length; i++, n += 2) {
            int vi = fComponentVisualOrder == null ? i : fComponentVisualOrder[i];
            TextLineComponent tlc = fComponents[vi];
            tlc.draw(g2, locs[n] + x, locs[n + 1] + y);
        }
    }
    
    public Rectangle2D getBounds() {
        float left = Float.MAX_VALUE;
        float right = -Float.MAX_VALUE;
        float top = Float.MAX_VALUE;
        float bottom = -Float.MAX_VALUE;
        for (int i = 0, n = 0; i < fComponents.length; i++, n += 2) {
            int vi = fComponentVisualOrder == null ? i : fComponentVisualOrder[i];
            TextLineComponent tlc = fComponents[vi];
            Rectangle2D tlcBounds = tlc.getVisualBounds();
            float x = locs[n];
            float y = locs[n + 1];
            left = Math.min(left, x + (float)tlcBounds.getX());
            right = Math.max(right, x + (float)tlcBounds.getMaxX());
            top = Math.min(top, y + (float)tlcBounds.getY());
            bottom = Math.max(bottom, y + (float)tlcBounds.getMaxY());
        }
        return new Rectangle2D$Float(left, top, right - left, bottom - top);
    }
    
    public Rectangle2D getItalicBounds() {
        float left = Float.MAX_VALUE;
        float right = -Float.MAX_VALUE;
        float top = Float.MAX_VALUE;
        float bottom = -Float.MAX_VALUE;
        for (int i = 0, n = 0; i < fComponents.length; i++, n += 2) {
            int vi = fComponentVisualOrder == null ? i : fComponentVisualOrder[i];
            TextLineComponent tlc = fComponents[vi];
            Rectangle2D tlcBounds = tlc.getItalicBounds();
            float x = locs[n];
            float y = locs[n + 1];
            left = Math.min(left, x + (float)tlcBounds.getX());
            right = Math.max(right, x + (float)tlcBounds.getMaxX());
            top = Math.min(top, y + (float)tlcBounds.getY());
            bottom = Math.max(bottom, y + (float)tlcBounds.getMaxY());
        }
        return new Rectangle2D$Float(left, top, right - left, bottom - top);
    }
    
    public Shape getOutline(AffineTransform tx) {
        GeneralPath dstShape = new GeneralPath(GeneralPath.WIND_NON_ZERO);
        for (int i = 0, n = 0; i < fComponents.length; i++, n += 2) {
            int vi = fComponentVisualOrder == null ? i : fComponentVisualOrder[i];
            TextLineComponent tlc = fComponents[vi];
            dstShape.append(tlc.getOutline(locs[n], locs[n + 1]), false);
        }
        if (tx != null) {
            dstShape.transform(tx);
        }
        return dstShape;
    }
    
    public int hashCode() {
        return (fComponents.length << 16) ^ (fComponents[0].hashCode() << 3) ^ (fCharsLimit - fCharsStart);
    }
    
    public String toString() {
        StringBuffer buf = new StringBuffer();
        for (int i = 0; i < fComponents.length; i++) {
            buf.append(fComponents[i]);
        }
        return buf.toString();
    }
    
    public static TextLine fastCreateTextLine(FontRenderContext frc, char[] chars, Font font, CoreMetrics lm, Map attributes) {
        boolean isDirectionLTR = true;
        byte[] levels = null;
        int[] charsLtoV = null;
        Bidi bidi = null;
        int characterCount = chars.length;
        boolean requiresBidi = false;
        boolean directionKnown = false;
        byte[] embs = null;
        if (attributes != null) {
            try {
                Boolean runDirection = (Boolean)(Boolean)attributes.get(TextAttribute.RUN_DIRECTION);
                if (runDirection != null) {
                    directionKnown = true;
                    isDirectionLTR = TextAttribute.RUN_DIRECTION_LTR.equals(runDirection);
                    requiresBidi = !isDirectionLTR;
                }
            } catch (ClassCastException e) {
            }
            try {
                Integer embeddingLevel = (Integer)(Integer)attributes.get(TextAttribute.BIDI_EMBEDDING);
                if (embeddingLevel != null) {
                    int intLevel = embeddingLevel.intValue();
                    if (intLevel >= -61 && intLevel < 62) {
                        byte level = (byte)intLevel;
                        requiresBidi = true;
                        embs = new byte[characterCount];
                        for (int i = 0; i < embs.length; ++i) {
                            embs[i] = level;
                        }
                    }
                }
            } catch (ClassCastException e) {
            }
        }
        if (!requiresBidi) {
            requiresBidi = Bidi.requiresBidi(chars, 0, chars.length);
        }
        if (requiresBidi) {
            int bidiflags = Bidi.DIRECTION_DEFAULT_LEFT_TO_RIGHT;
            if (directionKnown) {
                if (isDirectionLTR) {
                    bidiflags = Bidi.DIRECTION_LEFT_TO_RIGHT;
                } else {
                    bidiflags = Bidi.DIRECTION_RIGHT_TO_LEFT;
                }
            }
            bidi = new Bidi(chars, 0, embs, 0, chars.length, bidiflags);
            if (!bidi.isLeftToRight()) {
                levels = BidiUtils.getLevels(bidi);
                int[] charsVtoL = BidiUtils.createVisualToLogicalMap(levels);
                charsLtoV = BidiUtils.createInverseMap(charsVtoL);
                isDirectionLTR = bidi.baseIsLeftToRight();
            }
        }
        Decoration decorator;
        if (attributes != null) {
            decorator = Decoration.getDecoration(StyledParagraph.addInputMethodAttrs(attributes));
        } else {
            decorator = Decoration.getPlainDecoration();
        }
        int layoutFlags = 0;
        TextLabelFactory factory = new TextLabelFactory(frc, chars, bidi, layoutFlags);
        TextLineComponent[] components = new TextLineComponent[1];
        components = createComponentsOnRun(0, chars.length, chars, charsLtoV, levels, factory, font, lm, frc, decorator, components, 0);
        int numComponents = components.length;
        while (components[numComponents - 1] == null) {
            numComponents -= 1;
        }
        if (numComponents != components.length) {
            TextLineComponent[] temp = new TextLineComponent[numComponents];
            System.arraycopy(components, 0, temp, 0, numComponents);
            components = temp;
        }
        return new TextLine(components, lm.baselineOffsets, chars, 0, chars.length, charsLtoV, levels, isDirectionLTR);
    }
    
    private static TextLineComponent[] expandArray(TextLineComponent[] orig) {
        TextLineComponent[] newComponents = new TextLineComponent[orig.length + 8];
        System.arraycopy(orig, 0, newComponents, 0, orig.length);
        return newComponents;
    }
    
    public static TextLineComponent[] createComponentsOnRun(int runStart, int runLimit, char[] chars, int[] charsLtoV, byte[] levels, TextLabelFactory factory, Font font, CoreMetrics cm, FontRenderContext frc, Decoration decorator, TextLineComponent[] components, int numComponents) {
        int pos = runStart;
        do {
            int chunkLimit = firstVisualChunk(charsLtoV, levels, pos, runLimit);
            do {
                int startPos = pos;
                int lmCount;
                if (cm == null) {
                    LineMetrics lineMetrics = font.getLineMetrics(chars, startPos, chunkLimit, frc);
                    cm = CoreMetrics.get(lineMetrics);
                    lmCount = lineMetrics.getNumChars();
                } else {
                    lmCount = (chunkLimit - startPos);
                }
                TextLineComponent nextComponent = factory.createExtended(font, cm, decorator, startPos, startPos + lmCount);
                ++numComponents;
                if (numComponents >= components.length) {
                    components = expandArray(components);
                }
                components[numComponents - 1] = nextComponent;
                pos += lmCount;
            }             while (pos < chunkLimit);
        }         while (pos < runLimit);
        return components;
    }
    
    public static TextLineComponent[] getComponents(StyledParagraph styledParagraph, char[] chars, int textStart, int textLimit, int[] charsLtoV, byte[] levels, TextLabelFactory factory) {
        FontRenderContext frc = factory.getFontRenderContext();
        int numComponents = 0;
        TextLineComponent[] tempComponents = new TextLineComponent[1];
        int pos = textStart;
        do {
            int runLimit = Math.min(styledParagraph.getRunLimit(pos), textLimit);
            Decoration decorator = styledParagraph.getDecorationAt(pos);
            Object graphicOrFont = styledParagraph.getFontOrGraphicAt(pos);
            if (graphicOrFont instanceof GraphicAttribute) {
                GraphicAttribute graphicAttribute = (GraphicAttribute)(GraphicAttribute)graphicOrFont;
                do {
                    int chunkLimit = firstVisualChunk(charsLtoV, levels, pos, runLimit);
                    GraphicComponent nextGraphic = new GraphicComponent(graphicAttribute, decorator, charsLtoV, levels, pos, chunkLimit);
                    pos = chunkLimit;
                    ++numComponents;
                    if (numComponents >= tempComponents.length) {
                        tempComponents = expandArray(tempComponents);
                    }
                    tempComponents[numComponents - 1] = nextGraphic;
                }                 while (pos < runLimit);
            } else {
                Font font = (Font)(Font)graphicOrFont;
                tempComponents = createComponentsOnRun(pos, runLimit, chars, charsLtoV, levels, factory, font, null, frc, decorator, tempComponents, numComponents);
                pos = runLimit;
                numComponents = tempComponents.length;
                while (tempComponents[numComponents - 1] == null) {
                    numComponents -= 1;
                }
            }
        }         while (pos < textLimit);
        TextLineComponent[] components;
        if (tempComponents.length == numComponents) {
            components = tempComponents;
        } else {
            components = new TextLineComponent[numComponents];
            System.arraycopy(tempComponents, 0, components, 0, numComponents);
        }
        return components;
    }
    
    public static TextLine createLineFromText(char[] chars, StyledParagraph styledParagraph, TextLabelFactory factory, boolean isDirectionLTR, float[] baselineOffsets) {
        factory.setLineContext(0, chars.length);
        Bidi lineBidi = factory.getLineBidi();
        int[] charsLtoV = null;
        byte[] levels = null;
        if (lineBidi != null) {
            levels = BidiUtils.getLevels(lineBidi);
            int[] charsVtoL = BidiUtils.createVisualToLogicalMap(levels);
            charsLtoV = BidiUtils.createInverseMap(charsVtoL);
        }
        TextLineComponent[] components = getComponents(styledParagraph, chars, 0, chars.length, charsLtoV, levels, factory);
        return new TextLine(components, baselineOffsets, chars, 0, chars.length, charsLtoV, levels, isDirectionLTR);
    }
    
    private static int[] computeComponentOrder(TextLineComponent[] components, int[] charsLtoV) {
        int[] componentOrder = null;
        if (charsLtoV != null && components.length > 1) {
            componentOrder = new int[components.length];
            int gStart = 0;
            for (int i = 0; i < components.length; i++) {
                componentOrder[i] = charsLtoV[gStart];
                gStart += components[i].getNumCharacters();
            }
            componentOrder = BidiUtils.createContiguousOrder(componentOrder);
            componentOrder = BidiUtils.createInverseMap(componentOrder);
        }
        return componentOrder;
    }
    
    public static TextLine standardCreateTextLine(FontRenderContext frc, AttributedCharacterIterator text, char[] chars, float[] baselineOffsets) {
        StyledParagraph styledParagraph = new StyledParagraph(text, chars);
        Bidi bidi = new Bidi(text);
        if (bidi.isLeftToRight()) {
            bidi = null;
        }
        int layoutFlags = 0;
        TextLabelFactory factory = new TextLabelFactory(frc, chars, bidi, layoutFlags);
        boolean isDirectionLTR = true;
        if (bidi != null) {
            isDirectionLTR = bidi.baseIsLeftToRight();
        }
        return createLineFromText(chars, styledParagraph, factory, isDirectionLTR, baselineOffsets);
    }
    
    static boolean advanceToFirstFont(AttributedCharacterIterator aci) {
        for (char ch = aci.first(); ch != aci.DONE; ch = aci.setIndex(aci.getRunLimit())) {
            if (aci.getAttribute(TextAttribute.CHAR_REPLACEMENT) == null) {
                return true;
            }
        }
        return false;
    }
    
    static float[] getNormalizedOffsets(float[] baselineOffsets, byte baseline) {
        if (baselineOffsets[baseline] != 0) {
            float base = baselineOffsets[baseline];
            float[] temp = new float[baselineOffsets.length];
            for (int i = 0; i < temp.length; i++) temp[i] = baselineOffsets[i] - base;
            baselineOffsets = temp;
        }
        return baselineOffsets;
    }
    
    static Font getFontAtCurrentPos(AttributedCharacterIterator aci) {
        Object value = aci.getAttribute(TextAttribute.FONT);
        if (value != null) {
            return (Font)(Font)value;
        }
        if (aci.getAttribute(TextAttribute.FAMILY) != null) {
            return Font.getFont(aci.getAttributes());
        }
        int ch = CodePointIterator.create(aci).next();
        if (ch != CodePointIterator.DONE) {
            FontResolver resolver = FontResolver.getInstance();
            return resolver.getFont(resolver.getFontIndex(ch), aci.getAttributes());
        }
        return null;
    }
    
    static float getJustifyRatio(Map attributes) {
        Object value = attributes.get(TextAttribute.JUSTIFICATION);
        if (value == null) {
            return 1;
        }
        float justifyRatio = ((Float)(Float)value).floatValue();
        if (justifyRatio < 0) {
            justifyRatio = 0;
        } else if (justifyRatio > 1) {
            justifyRatio = 1;
        }
        return justifyRatio;
    }
    
    private static int firstVisualChunk(int[] order, byte[] direction, int start, int limit) {
        if (order != null && direction != null) {
            byte dir = direction[start];
            while (++start < limit && direction[start] == dir) {
            }
            return start;
        }
        return limit;
    }
    
    public TextLine getJustifiedLine(float justificationWidth, float justifyRatio, int justStart, int justLimit) {
        TextLineComponent[] newComponents = new TextLineComponent[fComponents.length];
        System.arraycopy(fComponents, 0, newComponents, 0, fComponents.length);
        float leftHang = 0;
        float adv = 0;
        float justifyDelta = 0;
        boolean rejustify = false;
        do {
            adv = getAdvanceBetween(newComponents, 0, characterCount());
            float justifyAdvance = getAdvanceBetween(newComponents, justStart, justLimit);
            justifyDelta = (justificationWidth - justifyAdvance) * justifyRatio;
            int[] infoPositions = new int[newComponents.length];
            int infoCount = 0;
            for (int visIndex = 0; visIndex < newComponents.length; visIndex++) {
                int logIndex = fComponentVisualOrder == null ? visIndex : fComponentVisualOrder[visIndex];
                infoPositions[logIndex] = infoCount;
                infoCount += newComponents[logIndex].getNumJustificationInfos();
            }
            GlyphJustificationInfo[] infos = new GlyphJustificationInfo[infoCount];
            int compStart = 0;
            for (int i = 0; i < newComponents.length; i++) {
                TextLineComponent comp = newComponents[i];
                int compLength = comp.getNumCharacters();
                int compLimit = compStart + compLength;
                if (compLimit > justStart) {
                    int rangeMin = Math.max(0, justStart - compStart);
                    int rangeMax = Math.min(compLength, justLimit - compStart);
                    comp.getJustificationInfos(infos, infoPositions[i], rangeMin, rangeMax);
                    if (compLimit >= justLimit) {
                        break;
                    }
                }
            }
            int infoStart = 0;
            int infoLimit = infoCount;
            while (infoStart < infoLimit && infos[infoStart] == null) {
                ++infoStart;
            }
            while (infoLimit > infoStart && infos[infoLimit - 1] == null) {
                --infoLimit;
            }
            TextJustifier justifier = new TextJustifier(infos, infoStart, infoLimit);
            float[] deltas = justifier.justify(justifyDelta);
            boolean canRejustify = rejustify == false;
            boolean wantRejustify = false;
            boolean[] flags = new boolean[1];
            compStart = 0;
            for (int i = 0; i < newComponents.length; i++) {
                TextLineComponent comp = newComponents[i];
                int compLength = comp.getNumCharacters();
                int compLimit = compStart + compLength;
                if (compLimit > justStart) {
                    int rangeMin = Math.max(0, justStart - compStart);
                    int rangeMax = Math.min(compLength, justLimit - compStart);
                    newComponents[i] = comp.applyJustificationDeltas(deltas, infoPositions[i] * 2, flags);
                    wantRejustify |= flags[0];
                    if (compLimit >= justLimit) {
                        break;
                    }
                }
            }
            rejustify = wantRejustify && !rejustify;
        }         while (rejustify);
        return new TextLine(newComponents, fBaselineOffsets, fChars, fCharsStart, fCharsLimit, fCharLogicalOrder, fCharLevels, fIsDirectionLTR);
    }
    
    public static float getAdvanceBetween(TextLineComponent[] components, int start, int limit) {
        float advance = 0;
        int tlcStart = 0;
        for (int i = 0; i < components.length; i++) {
            TextLineComponent comp = components[i];
            int tlcLength = comp.getNumCharacters();
            int tlcLimit = tlcStart + tlcLength;
            if (tlcLimit > start) {
                int measureStart = Math.max(0, start - tlcStart);
                int measureLimit = Math.min(tlcLength, limit - tlcStart);
                advance += comp.getAdvanceBetween(measureStart, measureLimit);
                if (tlcLimit >= limit) {
                    break;
                }
            }
            tlcStart = tlcLimit;
        }
        return advance;
    }
}
