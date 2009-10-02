package java.awt.font;

import java.awt.Font;
import java.text.AttributedCharacterIterator;
import java.text.Bidi;
import java.text.BreakIterator;
import java.awt.font.FontRenderContext;
import java.util.Hashtable;
import java.util.Map;
import sun.font.BidiUtils;
import sun.font.TextLineComponent;
import sun.font.TextLabelFactory;

public final class TextMeasurer implements Cloneable {
    private static float EST_LINES = (float)2.1;
    private FontRenderContext fFrc;
    private int fStart;
    private char[] fChars;
    private Bidi fBidi;
    private byte[] fLevels;
    private TextLineComponent[] fComponents;
    private int fComponentStart;
    private int fComponentLimit;
    private boolean haveLayoutWindow;
    private BreakIterator fLineBreak = null;
    private CharArrayIterator charIter = null;
    int layoutCount = 0;
    int layoutCharCount = 0;
    private StyledParagraph fParagraph;
    private boolean fIsDirectionLTR;
    private byte fBaseline;
    private float[] fBaselineOffsets;
    private float fJustifyRatio = 1;
    
    public TextMeasurer(AttributedCharacterIterator text, FontRenderContext frc) {
        
        fFrc = frc;
        initAll(text);
    }
    
    protected Object clone() {
        TextMeasurer other;
        try {
            other = (TextMeasurer)(TextMeasurer)super.clone();
        } catch (CloneNotSupportedException e) {
            throw new Error();
        }
        if (fComponents != null) {
            other.fComponents = (TextLineComponent[])(TextLineComponent[])fComponents.clone();
        }
        return other;
    }
    
    private void invalidateComponents() {
        fComponentStart = fComponentLimit = fChars.length;
        fComponents = null;
        haveLayoutWindow = false;
    }
    
    private void initAll(AttributedCharacterIterator text) {
        fStart = text.getBeginIndex();
        fChars = new char[text.getEndIndex() - fStart];
        int n = 0;
        for (char c = text.first(); c != text.DONE; c = text.next()) {
            fChars[n++] = c;
        }
        text.first();
        fBidi = new Bidi(text);
        if (fBidi.isLeftToRight()) {
            fBidi = null;
        }
        text.first();
        Map paragraphAttrs = text.getAttributes();
        if (paragraphAttrs != null) {
            try {
                NumericShaper shaper = (NumericShaper)(NumericShaper)paragraphAttrs.get(TextAttribute.NUMERIC_SHAPING);
                if (shaper != null) {
                    shaper.shape(fChars, 0, fChars.length);
                }
            } catch (ClassCastException e) {
            }
        }
        fParagraph = new StyledParagraph(text, fChars);
        {
            fJustifyRatio = TextLine.getJustifyRatio(paragraphAttrs);
            boolean haveFont = TextLine.advanceToFirstFont(text);
            if (haveFont) {
                Font defaultFont = TextLine.getFontAtCurrentPos(text);
                int charsStart = text.getIndex() - text.getBeginIndex();
                LineMetrics lm = defaultFont.getLineMetrics(fChars, charsStart, charsStart + 1, fFrc);
                fBaseline = (byte)lm.getBaselineIndex();
                fBaselineOffsets = lm.getBaselineOffsets();
            } else {
                GraphicAttribute graphic = (GraphicAttribute)(GraphicAttribute)paragraphAttrs.get(TextAttribute.CHAR_REPLACEMENT);
                fBaseline = TextLayout.getBaselineFromGraphic(graphic);
                Font dummyFont = new Font(new Hashtable(5, (float)0.9));
                LineMetrics lm = dummyFont.getLineMetrics(" ", 0, 1, fFrc);
                fBaselineOffsets = lm.getBaselineOffsets();
            }
            fBaselineOffsets = TextLine.getNormalizedOffsets(fBaselineOffsets, fBaseline);
        }
        invalidateComponents();
    }
    
    private void generateComponents(int startingAt, int endingAt) {
        if (collectStats) {
            formattedChars += (endingAt - startingAt);
        }
        int layoutFlags = 0;
        TextLabelFactory factory = new TextLabelFactory(fFrc, fChars, fBidi, layoutFlags);
        int[] charsLtoV = null;
        if (fBidi != null) {
            fLevels = BidiUtils.getLevels(fBidi);
            int[] charsVtoL = BidiUtils.createVisualToLogicalMap(fLevels);
            charsLtoV = BidiUtils.createInverseMap(charsVtoL);
            fIsDirectionLTR = fBidi.baseIsLeftToRight();
        } else {
            fLevels = null;
            fIsDirectionLTR = true;
        }
        try {
            fComponents = TextLine.getComponents(fParagraph, fChars, startingAt, endingAt, charsLtoV, fLevels, factory);
        } catch (IllegalArgumentException e) {
            System.out.println("startingAt=" + startingAt + "; endingAt=" + endingAt);
            System.out.println("fComponentLimit=" + fComponentLimit);
            throw e;
        }
        fComponentStart = startingAt;
        fComponentLimit = endingAt;
    }
    
    private int calcLineBreak(final int pos, final float maxAdvance) {
        int startPos = pos;
        float width = maxAdvance;
        int tlcIndex;
        int tlcStart = fComponentStart;
        for (tlcIndex = 0; tlcIndex < fComponents.length; tlcIndex++) {
            int gaLimit = tlcStart + fComponents[tlcIndex].getNumCharacters();
            if (gaLimit > startPos) {
                break;
            } else {
                tlcStart = gaLimit;
            }
        }
        for (; tlcIndex < fComponents.length; tlcIndex++) {
            TextLineComponent tlc = fComponents[tlcIndex];
            int numCharsInGa = tlc.getNumCharacters();
            int lineBreak = tlc.getLineBreakIndex(startPos - tlcStart, width);
            if (lineBreak == numCharsInGa && tlcIndex < fComponents.length) {
                width -= tlc.getAdvanceBetween(startPos - tlcStart, lineBreak);
                tlcStart += numCharsInGa;
                startPos = tlcStart;
            } else {
                return tlcStart + lineBreak;
            }
        }
        if (fComponentLimit < fChars.length) {
            generateComponents(pos, fChars.length);
            return calcLineBreak(pos, maxAdvance);
        }
        return fChars.length;
    }
    
    private int trailingCdWhitespaceStart(int startPos, int limitPos) {
        if (fLevels != null) {
            final byte baseLevel = (byte)(fIsDirectionLTR ? 0 : 1);
            for (int cdWsStart = limitPos; --cdWsStart >= startPos; ) {
                if ((fLevels[cdWsStart] % 2) == baseLevel || Character.getDirectionality(fChars[cdWsStart]) != Character.DIRECTIONALITY_WHITESPACE) {
                    return ++cdWsStart;
                }
            }
        }
        return startPos;
    }
    
    private TextLineComponent[] makeComponentsOnRange(int startPos, int limitPos) {
        final int cdWsStart = trailingCdWhitespaceStart(startPos, limitPos);
        int tlcIndex;
        int tlcStart = fComponentStart;
        for (tlcIndex = 0; tlcIndex < fComponents.length; tlcIndex++) {
            int gaLimit = tlcStart + fComponents[tlcIndex].getNumCharacters();
            if (gaLimit > startPos) {
                break;
            } else {
                tlcStart = gaLimit;
            }
        }
        int componentCount;
        {
            boolean split = false;
            int compStart = tlcStart;
            int lim = tlcIndex;
            for (boolean cont = true; cont; lim++) {
                int gaLimit = compStart + fComponents[lim].getNumCharacters();
                if (cdWsStart > Math.max(compStart, startPos) && cdWsStart < Math.min(gaLimit, limitPos)) {
                    split = true;
                }
                if (gaLimit >= limitPos) {
                    cont = false;
                } else {
                    compStart = gaLimit;
                }
            }
            componentCount = lim - tlcIndex;
            if (split) {
                componentCount++;
            }
        }
        TextLineComponent[] components = new TextLineComponent[componentCount];
        int newCompIndex = 0;
        int linePos = startPos;
        int breakPt = cdWsStart;
        int subsetFlag;
        if (breakPt == startPos) {
            subsetFlag = fIsDirectionLTR ? TextLineComponent.LEFT_TO_RIGHT : TextLineComponent.RIGHT_TO_LEFT;
            breakPt = limitPos;
        } else {
            subsetFlag = TextLineComponent.UNCHANGED;
        }
        while (linePos < limitPos) {
            int compLength = fComponents[tlcIndex].getNumCharacters();
            int tlcLimit = tlcStart + compLength;
            int start = Math.max(linePos, tlcStart);
            int limit = Math.min(breakPt, tlcLimit);
            components[newCompIndex++] = fComponents[tlcIndex].getSubset(start - tlcStart, limit - tlcStart, subsetFlag);
            linePos += (limit - start);
            if (linePos == breakPt) {
                breakPt = limitPos;
                subsetFlag = fIsDirectionLTR ? TextLineComponent.LEFT_TO_RIGHT : TextLineComponent.RIGHT_TO_LEFT;
            }
            if (linePos == tlcLimit) {
                tlcIndex++;
                tlcStart = tlcLimit;
            }
        }
        return components;
    }
    
    private TextLine makeTextLineOnRange(int startPos, int limitPos) {
        int[] charsLtoV = null;
        byte[] charLevels = null;
        if (fBidi != null) {
            Bidi lineBidi = fBidi.createLineBidi(startPos, limitPos);
            charLevels = BidiUtils.getLevels(lineBidi);
            int[] charsVtoL = BidiUtils.createVisualToLogicalMap(charLevels);
            charsLtoV = BidiUtils.createInverseMap(charsVtoL);
        }
        TextLineComponent[] components = makeComponentsOnRange(startPos, limitPos);
        return new TextLine(components, fBaselineOffsets, fChars, startPos, limitPos, charsLtoV, charLevels, fIsDirectionLTR);
    }
    
    private void ensureComponents(int start, int limit) {
        if (start < fComponentStart || limit > fComponentLimit) {
            generateComponents(start, limit);
        }
    }
    
    private void makeLayoutWindow(int localStart) {
        int compStart = localStart;
        int compLimit = fChars.length;
        if (layoutCount > 0 && !haveLayoutWindow) {
            float avgLineLength = Math.max(layoutCharCount / layoutCount, 1);
            compLimit = Math.min(localStart + (int)(avgLineLength * EST_LINES), fChars.length);
        }
        if (localStart > 0 || compLimit < fChars.length) {
            if (charIter == null) {
                charIter = new CharArrayIterator(fChars);
            } else {
                charIter.reset(fChars);
            }
            if (fLineBreak == null) {
                fLineBreak = BreakIterator.getLineInstance();
            }
            fLineBreak.setText(charIter);
            if (localStart > 0) {
                if (!fLineBreak.isBoundary(localStart)) {
                    compStart = fLineBreak.preceding(localStart);
                }
            }
            if (compLimit < fChars.length) {
                if (!fLineBreak.isBoundary(compLimit)) {
                    compLimit = fLineBreak.following(compLimit);
                }
            }
        }
        ensureComponents(compStart, compLimit);
        haveLayoutWindow = true;
    }
    
    public int getLineBreakIndex(int start, float maxAdvance) {
        int localStart = start - fStart;
        if (!haveLayoutWindow || localStart < fComponentStart || localStart >= fComponentLimit) {
            makeLayoutWindow(localStart);
        }
        return calcLineBreak(localStart, maxAdvance) + fStart;
    }
    
    public float getAdvanceBetween(int start, int limit) {
        int localStart = start - fStart;
        int localLimit = limit - fStart;
        ensureComponents(localStart, localLimit);
        TextLine line = makeTextLineOnRange(localStart, localLimit);
        return line.getMetrics().advance;
    }
    
    public TextLayout getLayout(int start, int limit) {
        int localStart = start - fStart;
        int localLimit = limit - fStart;
        ensureComponents(localStart, localLimit);
        TextLine textLine = makeTextLineOnRange(localStart, localLimit);
        if (localLimit < fChars.length) {
            layoutCharCount += limit - start;
            layoutCount++;
        }
        return new TextLayout(textLine, fBaseline, fBaselineOffsets, fJustifyRatio);
    }
    private int formattedChars = 0;
    private static boolean wantStats = false;
    private boolean collectStats = false;
    
    private void printStats() {
        System.out.println("formattedChars: " + formattedChars);
        collectStats = false;
    }
    
    public void insertChar(AttributedCharacterIterator newParagraph, int insertPos) {
        if (collectStats) {
            printStats();
        }
        if (wantStats) {
            collectStats = true;
        }
        fStart = newParagraph.getBeginIndex();
        int end = newParagraph.getEndIndex();
        if (end - fStart != fChars.length + 1) {
            initAll(newParagraph);
        }
        char[] newChars = new char[end - fStart];
        int newCharIndex = insertPos - fStart;
        System.arraycopy(fChars, 0, newChars, 0, newCharIndex);
        char newChar = newParagraph.setIndex(insertPos);
        newChars[newCharIndex] = newChar;
        System.arraycopy(fChars, newCharIndex, newChars, newCharIndex + 1, end - insertPos - 1);
        fChars = newChars;
        if (fBidi != null || Bidi.requiresBidi(newChars, newCharIndex, newCharIndex + 1) || newParagraph.getAttribute(TextAttribute.BIDI_EMBEDDING) != null) {
            fBidi = new Bidi(newParagraph);
            if (fBidi.isLeftToRight()) {
                fBidi = null;
            }
        }
        fParagraph = StyledParagraph.insertChar(newParagraph, fChars, insertPos, fParagraph);
        invalidateComponents();
    }
    
    public void deleteChar(AttributedCharacterIterator newParagraph, int deletePos) {
        fStart = newParagraph.getBeginIndex();
        int end = newParagraph.getEndIndex();
        if (end - fStart != fChars.length - 1) {
            initAll(newParagraph);
        }
        char[] newChars = new char[end - fStart];
        int changedIndex = deletePos - fStart;
        System.arraycopy(fChars, 0, newChars, 0, deletePos - fStart);
        System.arraycopy(fChars, changedIndex + 1, newChars, changedIndex, end - deletePos);
        fChars = newChars;
        if (fBidi != null) {
            fBidi = new Bidi(newParagraph);
            if (fBidi.isLeftToRight()) {
                fBidi = null;
            }
        }
        fParagraph = StyledParagraph.deleteChar(newParagraph, fChars, deletePos, fParagraph);
        invalidateComponents();
    }
    
    char[] getChars() {
        return fChars;
    }
}
