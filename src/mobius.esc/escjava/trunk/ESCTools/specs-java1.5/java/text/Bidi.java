package java.text;

import java.awt.font.TextAttribute;
import java.awt.font.NumericShaper;
import sun.text.CodePointIterator;

public final class Bidi {
    byte dir;
    byte baselevel;
    int length;
    int[] runs;
    int[] cws;
    static {
        java.security.AccessController.doPrivileged(new sun.security.action.LoadLibraryAction("awt"));
        java.security.AccessController.doPrivileged(new sun.security.action.LoadLibraryAction("fontmanager"));
    }
    public static final int DIRECTION_LEFT_TO_RIGHT = 0;
    public static final int DIRECTION_RIGHT_TO_LEFT = 1;
    public static final int DIRECTION_DEFAULT_LEFT_TO_RIGHT = -2;
    public static final int DIRECTION_DEFAULT_RIGHT_TO_LEFT = -1;
    private static final int DIR_MIXED = 2;
    
    public Bidi(String paragraph, int flags) {
        
        if (paragraph == null) {
            throw new IllegalArgumentException("paragraph is null");
        }
        nativeBidiChars(this, paragraph.toCharArray(), 0, null, 0, paragraph.length(), flags);
    }
    
    public Bidi(AttributedCharacterIterator paragraph) {
        
        if (paragraph == null) {
            throw new IllegalArgumentException("paragraph is null");
        }
        int flags = DIRECTION_DEFAULT_LEFT_TO_RIGHT;
        byte[] embeddings = null;
        int start = paragraph.getBeginIndex();
        int limit = paragraph.getEndIndex();
        int length = limit - start;
        int n = 0;
        char[] text = new char[length];
        for (char c = paragraph.first(); c != paragraph.DONE; c = paragraph.next()) {
            text[n++] = c;
        }
        paragraph.first();
        try {
            Boolean runDirection = (Boolean)(Boolean)paragraph.getAttribute(TextAttribute.RUN_DIRECTION);
            if (runDirection != null) {
                if (TextAttribute.RUN_DIRECTION_LTR.equals(runDirection)) {
                    flags = DIRECTION_LEFT_TO_RIGHT;
                } else {
                    flags = DIRECTION_RIGHT_TO_LEFT;
                }
            }
        } catch (ClassCastException e) {
        }
        try {
            NumericShaper shaper = (NumericShaper)(NumericShaper)paragraph.getAttribute(TextAttribute.NUMERIC_SHAPING);
            if (shaper != null) {
                shaper.shape(text, 0, text.length);
            }
        } catch (ClassCastException e) {
        }
        int pos = start;
        do {
            paragraph.setIndex(pos);
            Object embeddingLevel = paragraph.getAttribute(TextAttribute.BIDI_EMBEDDING);
            int newpos = paragraph.getRunLimit(TextAttribute.BIDI_EMBEDDING);
            if (embeddingLevel != null) {
                try {
                    int intLevel = ((Integer)(Integer)embeddingLevel).intValue();
                    if (intLevel >= -61 && intLevel < 61) {
                        byte level = (byte)(intLevel < 0 ? (-intLevel | 128) : intLevel);
                        if (embeddings == null) {
                            embeddings = new byte[length];
                        }
                        for (int i = pos - start; i < newpos - start; ++i) {
                            embeddings[i] = level;
                        }
                    }
                } catch (ClassCastException e) {
                }
            }
            pos = newpos;
        }         while (pos < limit);
        nativeBidiChars(this, text, 0, embeddings, 0, text.length, flags);
    }
    
    public Bidi(char[] text, int textStart, byte[] embeddings, int embStart, int paragraphLength, int flags) {
        
        if (text == null) {
            throw new IllegalArgumentException("text is null");
        }
        if (paragraphLength < 0) {
            throw new IllegalArgumentException("bad length: " + paragraphLength);
        }
        if (textStart < 0 || paragraphLength > text.length - textStart) {
            throw new IllegalArgumentException("bad range: " + textStart + " length: " + paragraphLength + " for text of length: " + text.length);
        }
        if (embeddings != null && (embStart < 0 || paragraphLength > embeddings.length - embStart)) {
            throw new IllegalArgumentException("bad range: " + embStart + " length: " + paragraphLength + " for embeddings of length: " + text.length);
        }
        if (embeddings != null) {
            for (int i = embStart, embLimit = embStart + paragraphLength; i < embLimit; ++i) {
                if (embeddings[i] < 0) {
                    byte[] temp = new byte[paragraphLength];
                    System.arraycopy(embeddings, embStart, temp, 0, paragraphLength);
                    for (i -= embStart; i < paragraphLength; ++i) {
                        if (temp[i] < 0) {
                            temp[i] = (byte)(-temp[i] | 128);
                        }
                    }
                    embeddings = temp;
                    embStart = 0;
                    break;
                }
            }
        }
        nativeBidiChars(this, text, textStart, embeddings, embStart, paragraphLength, flags);
    }
    
    private Bidi(int dir, int baseLevel, int length, int[] data, int[] cws) {
        
        reset(dir, baseLevel, length, data, cws);
    }
    
    private void reset(int dir, int baselevel, int length, int[] data, int[] cws) {
        this.dir = (byte)dir;
        this.baselevel = (byte)baselevel;
        this.length = length;
        this.runs = data;
        this.cws = cws;
    }
    
    public Bidi createLineBidi(int lineStart, int lineLimit) {
        if (lineStart == 0 && lineLimit == length) {
            return this;
        }
        int lineLength = lineLimit - lineStart;
        if (lineStart < 0 || lineLimit < lineStart || lineLimit > length) {
            throw new IllegalArgumentException("range " + lineStart + " to " + lineLimit + " is invalid for paragraph of length " + length);
        }
        if (runs == null) {
            return new Bidi(dir, baselevel, lineLength, null, null);
        } else {
            int cwspos = -1;
            int[] ncws = null;
            if (cws != null) {
                int cwss = 0;
                int cwsl = cws.length;
                while (cwss < cwsl) {
                    if (cws[cwss] >= lineStart) {
                        cwsl = cwss;
                        while (cwsl < cws.length && cws[cwsl] < lineLimit) {
                            cwsl++;
                        }
                        int ll = lineLimit - 1;
                        while (cwsl > cwss && cws[cwsl - 1] == ll) {
                            cwspos = ll;
                            --cwsl;
                            --ll;
                        }
                        if (cwspos == lineStart) {
                            return new Bidi(dir, baselevel, lineLength, null, null);
                        }
                        int ncwslen = cwsl - cwss;
                        if (ncwslen > 0) {
                            ncws = new int[ncwslen];
                            for (int i = 0; i < ncwslen; ++i) {
                                ncws[i] = cws[cwss + i] - lineStart;
                            }
                        }
                        break;
                    }
                    ++cwss;
                }
            }
            int[] nruns = null;
            int nlevel = baselevel;
            int limit = cwspos == -1 ? lineLimit : cwspos;
            int rs = 0;
            int rl = runs.length;
            int ndir = dir;
            for (; rs < runs.length; rs += 2) {
                if (runs[rs] > lineStart) {
                    rl = rs;
                    while (rl < runs.length && runs[rl] < limit) {
                        rl += 2;
                    }
                    if ((rl > rs) || (runs[rs + 1] != baselevel)) {
                        rl += 2;
                        if (cwspos != -1 && rl > rs && runs[rl - 1] != baselevel) {
                            nruns = new int[rl - rs + 2];
                            nruns[rl - rs] = lineLength;
                            nruns[rl - rs + 1] = baselevel;
                        } else {
                            limit = lineLimit;
                            nruns = new int[rl - rs];
                        }
                        int n = 0;
                        for (int i = rs; i < rl; i += 2) {
                            nruns[n++] = runs[i] - lineStart;
                            nruns[n++] = runs[i + 1];
                        }
                        nruns[n - 2] = limit - lineStart;
                    } else {
                        ndir = (runs[rs + 1] & 1) == 0 ? DIRECTION_LEFT_TO_RIGHT : DIRECTION_RIGHT_TO_LEFT;
                    }
                    break;
                }
            }
            return new Bidi(ndir, baselevel, lineLength, nruns, ncws);
        }
    }
    
    public boolean isMixed() {
        return dir == DIR_MIXED;
    }
    
    public boolean isLeftToRight() {
        return dir == DIRECTION_LEFT_TO_RIGHT;
    }
    
    public boolean isRightToLeft() {
        return dir == DIRECTION_RIGHT_TO_LEFT;
    }
    
    public int getLength() {
        return length;
    }
    
    public boolean baseIsLeftToRight() {
        return (baselevel & 1) == 0;
    }
    
    public int getBaseLevel() {
        return baselevel;
    }
    
    public int getLevelAt(int offset) {
        if (runs == null || offset < 0 || offset >= length) {
            return baselevel;
        } else {
            int i = 0;
            do {
                if (offset < runs[i]) {
                    return runs[i + 1];
                }
                i += 2;
            }             while (true);
        }
    }
    
    public int getRunCount() {
        return runs == null ? 1 : runs.length / 2;
    }
    
    public int getRunLevel(int run) {
        return runs == null ? baselevel : runs[run * 2 + 1];
    }
    
    public int getRunStart(int run) {
        return (runs == null || run == 0) ? 0 : runs[run * 2 - 2];
    }
    
    public int getRunLimit(int run) {
        return runs == null ? length : runs[run * 2];
    }
    
    public static boolean requiresBidi(char[] text, int start, int limit) {
        CodePointIterator cpi = CodePointIterator.create(text, start, limit);
        for (int cp = cpi.next(); cp != CodePointIterator.DONE; cp = cpi.next()) {
            if (cp > 1424) {
                int dc = nativeGetDirectionCode(cp);
                if ((RMASK & (1 << dc)) != 0) {
                    return true;
                }
            }
        }
        return false;
    }
    
    public static void reorderVisually(byte[] levels, int levelStart, Object[] objects, int objectStart, int count) {
        if (count < 0) {
            throw new IllegalArgumentException("count " + count + " must be >= 0");
        }
        if (levelStart < 0 || levelStart + count > levels.length) {
            throw new IllegalArgumentException("levelStart " + levelStart + " and count " + count + " out of range [0, " + levels.length + "]");
        }
        if (objectStart < 0 || objectStart + count > objects.length) {
            throw new IllegalArgumentException("objectStart " + objectStart + " and count " + count + " out of range [0, " + objects.length + "]");
        }
        byte lowestOddLevel = (byte)(NUMLEVELS + 1);
        byte highestLevel = 0;
        int levelLimit = levelStart + count;
        for (int i = levelStart; i < levelLimit; i++) {
            byte level = levels[i];
            if (level > highestLevel) {
                highestLevel = level;
            }
            if ((level & 1) != 0 && level < lowestOddLevel) {
                lowestOddLevel = level;
            }
        }
        int delta = objectStart - levelStart;
        while (highestLevel >= lowestOddLevel) {
            int i = levelStart;
            for (; ; ) {
                while (i < levelLimit && levels[i] < highestLevel) {
                    i++;
                }
                int begin = i++;
                if (begin == levelLimit) {
                    break;
                }
                while (i < levelLimit && levels[i] >= highestLevel) {
                    i++;
                }
                int end = i - 1;
                begin += delta;
                end += delta;
                while (begin < end) {
                    Object temp = objects[begin];
                    objects[begin] = objects[end];
                    objects[end] = temp;
                    ++begin;
                    --end;
                }
            }
            --highestLevel;
        }
    }
    private static final char NUMLEVELS = 62;
    private static final int RMASK = (1 << 1) | (1 << 5) | (1 << 13) | (1 << 14) | (1 << 15);
    
    private static native int nativeGetDirectionCode(int cp);
    
    private static synchronized native void nativeBidiChars(Bidi bidi, char[] text, int textStart, byte[] embeddings, int embeddingStart, int length, int flags);
    
    public String toString() {
        StringBuffer buf = new StringBuffer(super.toString());
        buf.append("[dir: " + dir);
        buf.append(" baselevel: " + baselevel);
        buf.append(" length: " + length);
        if (runs == null) {
            buf.append(" runs: null");
        } else {
            buf.append(" runs: [");
            for (int i = 0; i < runs.length; i += 2) {
                if (i != 0) {
                    buf.append(' ');
                }
                buf.append(runs[i]);
                buf.append('/');
                buf.append(runs[i + 1]);
            }
            buf.append(']');
        }
        if (cws == null) {
            buf.append(" cws: null");
        } else {
            buf.append(" cws: [");
            for (int i = 0; i < cws.length; ++i) {
                if (i != 0) {
                    buf.append(' ');
                }
                buf.append(Integer.toHexString(cws[i]));
            }
            buf.append(']');
        }
        buf.append(']');
        return buf.toString();
    }
}
