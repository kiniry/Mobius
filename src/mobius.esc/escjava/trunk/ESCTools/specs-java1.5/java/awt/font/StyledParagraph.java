package java.awt.font;

import java.awt.Font;
import java.awt.Toolkit;
import java.awt.im.InputMethodHighlight;
import java.text.Annotation;
import java.text.AttributedCharacterIterator;
import java.util.Vector;
import java.util.Hashtable;
import java.util.Map;
import sun.font.Decoration;
import sun.font.FontResolver;
import sun.text.CodePointIterator;

final class StyledParagraph {
    private int length;
    private Decoration decoration;
    private Object font;
    private Vector decorations;
    int[] decorationStarts;
    private Vector fonts;
    int[] fontStarts;
    private static int INITIAL_SIZE = 8;
    
    public StyledParagraph(AttributedCharacterIterator aci, char[] chars) {
        
        int start = aci.getBeginIndex();
        int end = aci.getEndIndex();
        length = end - start;
        int index = start;
        aci.first();
        do {
            final int nextRunStart = aci.getRunLimit();
            final int localIndex = index - start;
            Map attributes = aci.getAttributes();
            attributes = addInputMethodAttrs(attributes);
            Decoration d = Decoration.getDecoration(attributes);
            addDecoration(d, localIndex);
            Object f = getGraphicOrFont(attributes);
            if (f == null) {
                addFonts(chars, attributes, localIndex, nextRunStart - start);
            } else {
                addFont(f, localIndex);
            }
            aci.setIndex(nextRunStart);
            index = nextRunStart;
        }         while (index < end);
        if (decorations != null) {
            decorationStarts = addToVector(this, length, decorations, decorationStarts);
        }
        if (fonts != null) {
            fontStarts = addToVector(this, length, fonts, fontStarts);
        }
    }
    
    private static void insertInto(int pos, int[] starts, int numStarts) {
        while (starts[--numStarts] > pos) {
            starts[numStarts] += 1;
        }
    }
    
    public static StyledParagraph insertChar(AttributedCharacterIterator aci, char[] chars, int insertPos, StyledParagraph oldParagraph) {
        char ch = aci.setIndex(insertPos);
        int relativePos = Math.max(insertPos - aci.getBeginIndex() - 1, 0);
        Map attributes = addInputMethodAttrs(aci.getAttributes());
        Decoration d = Decoration.getDecoration(attributes);
        if (!oldParagraph.getDecorationAt(relativePos).equals(d)) {
            return new StyledParagraph(aci, chars);
        }
        Object f = getGraphicOrFont(attributes);
        if (f == null) {
            FontResolver resolver = FontResolver.getInstance();
            int fontIndex = resolver.getFontIndex(ch);
            f = resolver.getFont(fontIndex, attributes);
        }
        if (!oldParagraph.getFontOrGraphicAt(relativePos).equals(f)) {
            return new StyledParagraph(aci, chars);
        }
        oldParagraph.length += 1;
        if (oldParagraph.decorations != null) {
            insertInto(relativePos, oldParagraph.decorationStarts, oldParagraph.decorations.size());
        }
        if (oldParagraph.fonts != null) {
            insertInto(relativePos, oldParagraph.fontStarts, oldParagraph.fonts.size());
        }
        return oldParagraph;
    }
    
    private static void deleteFrom(int deleteAt, int[] starts, int numStarts) {
        while (starts[--numStarts] > deleteAt) {
            starts[numStarts] -= 1;
        }
    }
    
    public static StyledParagraph deleteChar(AttributedCharacterIterator aci, char[] chars, int deletePos, StyledParagraph oldParagraph) {
        deletePos -= aci.getBeginIndex();
        if (oldParagraph.decorations == null && oldParagraph.fonts == null) {
            oldParagraph.length -= 1;
            return oldParagraph;
        }
        if (oldParagraph.getRunLimit(deletePos) == deletePos + 1) {
            if (deletePos == 0 || oldParagraph.getRunLimit(deletePos - 1) == deletePos) {
                return new StyledParagraph(aci, chars);
            }
        }
        oldParagraph.length -= 1;
        if (oldParagraph.decorations != null) {
            deleteFrom(deletePos, oldParagraph.decorationStarts, oldParagraph.decorations.size());
        }
        if (oldParagraph.fonts != null) {
            deleteFrom(deletePos, oldParagraph.fontStarts, oldParagraph.fonts.size());
        }
        return oldParagraph;
    }
    
    public int getRunLimit(int index) {
        if (index < 0 || index >= length) {
            throw new IllegalArgumentException("index out of range");
        }
        int limit1 = length;
        if (decorations != null) {
            int run = findRunContaining(index, decorationStarts);
            limit1 = decorationStarts[run + 1];
        }
        int limit2 = length;
        if (fonts != null) {
            int run = findRunContaining(index, fontStarts);
            limit2 = fontStarts[run + 1];
        }
        return Math.min(limit1, limit2);
    }
    
    public Decoration getDecorationAt(int index) {
        if (index < 0 || index >= length) {
            throw new IllegalArgumentException("index out of range");
        }
        if (decorations == null) {
            return decoration;
        }
        int run = findRunContaining(index, decorationStarts);
        return (Decoration)(Decoration)decorations.elementAt(run);
    }
    
    public Object getFontOrGraphicAt(int index) {
        if (index < 0 || index >= length) {
            throw new IllegalArgumentException("index out of range");
        }
        if (fonts == null) {
            return font;
        }
        int run = findRunContaining(index, fontStarts);
        return fonts.elementAt(run);
    }
    
    private static int findRunContaining(int index, int[] starts) {
        for (int i = 1; true; i++) {
            if (starts[i] > index) {
                return i - 1;
            }
        }
    }
    
    private static int[] addToVector(Object obj, int index, Vector v, int[] starts) {
        if (!v.lastElement().equals(obj)) {
            v.addElement(obj);
            int count = v.size();
            if (starts.length == count) {
                int[] temp = new int[starts.length * 2];
                System.arraycopy(starts, 0, temp, 0, starts.length);
                starts = temp;
            }
            starts[count - 1] = index;
        }
        return starts;
    }
    
    private void addDecoration(Decoration d, int index) {
        if (decorations != null) {
            decorationStarts = addToVector(d, index, decorations, decorationStarts);
        } else if (decoration == null) {
            decoration = d;
        } else {
            if (!decoration.equals(d)) {
                decorations = new Vector(INITIAL_SIZE);
                decorations.addElement(decoration);
                decorations.addElement(d);
                decorationStarts = new int[INITIAL_SIZE];
                decorationStarts[0] = 0;
                decorationStarts[1] = index;
            }
        }
    }
    
    private void addFont(Object f, int index) {
        if (fonts != null) {
            fontStarts = addToVector(f, index, fonts, fontStarts);
        } else if (font == null) {
            font = f;
        } else {
            if (!font.equals(f)) {
                fonts = new Vector(INITIAL_SIZE);
                fonts.addElement(font);
                fonts.addElement(f);
                fontStarts = new int[INITIAL_SIZE];
                fontStarts[0] = 0;
                fontStarts[1] = index;
            }
        }
    }
    
    private void addFonts(char[] chars, Map attributes, int start, int limit) {
        FontResolver resolver = FontResolver.getInstance();
        CodePointIterator iter = CodePointIterator.create(chars, start, limit);
        for (int runStart = iter.charIndex(); runStart < limit; runStart = iter.charIndex()) {
            int fontIndex = resolver.nextFontRunIndex(iter);
            addFont(resolver.getFont(fontIndex, attributes), runStart);
        }
    }
    
    static Map addInputMethodAttrs(Map oldStyles) {
        Object value = oldStyles.get(TextAttribute.INPUT_METHOD_HIGHLIGHT);
        try {
            if (value != null) {
                if (value instanceof Annotation) {
                    value = ((Annotation)(Annotation)value).getValue();
                }
                InputMethodHighlight hl;
                hl = (InputMethodHighlight)(InputMethodHighlight)value;
                Map imStyles = null;
                try {
                    imStyles = hl.getStyle();
                } catch (NoSuchMethodError e) {
                }
                if (imStyles == null) {
                    Toolkit tk = Toolkit.getDefaultToolkit();
                    imStyles = tk.mapInputMethodHighlight(hl);
                }
                if (imStyles != null) {
                    Hashtable newStyles = new Hashtable(5, (float)0.9);
                    newStyles.putAll(oldStyles);
                    newStyles.putAll(imStyles);
                    return newStyles;
                }
            }
        } catch (ClassCastException e) {
        }
        return oldStyles;
    }
    
    private static Object getGraphicOrFont(Map attributes) {
        Object value = attributes.get(TextAttribute.CHAR_REPLACEMENT);
        if (value != null) {
            return value;
        }
        value = attributes.get(TextAttribute.FONT);
        if (value != null) {
            return value;
        }
        if (attributes.get(TextAttribute.FAMILY) != null) {
            return Font.getFont(attributes);
        } else {
            return null;
        }
    }
}
