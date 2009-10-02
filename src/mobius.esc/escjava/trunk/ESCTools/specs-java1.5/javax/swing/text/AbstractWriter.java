package javax.swing.text;

import java.io.Writer;
import java.io.IOException;
import java.util.Enumeration;

public abstract class AbstractWriter {
    private ElementIterator it;
    private Writer out;
    private int indentLevel = 0;
    private int indentSpace = 2;
    private Document doc = null;
    private int maxLineLength = 100;
    private int currLength = 0;
    private int startOffset = 0;
    private int endOffset = 0;
    private int offsetIndent = 0;
    private String lineSeparator;
    private boolean canWrapLines;
    private boolean isLineEmpty;
    private char[] indentChars;
    private char[] tempChars;
    private char[] newlineChars;
    private Segment segment;
    protected static final char NEWLINE = '\n';
    
    protected AbstractWriter(Writer w, Document doc) {
        this(w, doc, 0, doc.getLength());
    }
    
    protected AbstractWriter(Writer w, Document doc, int pos, int len) {
        
        this.doc = doc;
        it = new ElementIterator(doc.getDefaultRootElement());
        out = w;
        startOffset = pos;
        endOffset = pos + len;
        Object docNewline = doc.getProperty(DefaultEditorKit.EndOfLineStringProperty);
        if (docNewline instanceof String) {
            setLineSeparator((String)(String)docNewline);
        } else {
            String newline = null;
            try {
                newline = System.getProperty("line.separator");
            } catch (SecurityException se) {
            }
            if (newline == null) {
                newline = "\n";
            }
            setLineSeparator(newline);
        }
        canWrapLines = true;
    }
    
    protected AbstractWriter(Writer w, Element root) {
        this(w, root, 0, root.getEndOffset());
    }
    
    protected AbstractWriter(Writer w, Element root, int pos, int len) {
        
        this.doc = root.getDocument();
        it = new ElementIterator(root);
        out = w;
        startOffset = pos;
        endOffset = pos + len;
        canWrapLines = true;
    }
    
    public int getStartOffset() {
        return startOffset;
    }
    
    public int getEndOffset() {
        return endOffset;
    }
    
    protected ElementIterator getElementIterator() {
        return it;
    }
    
    protected Writer getWriter() {
        return out;
    }
    
    protected Document getDocument() {
        return doc;
    }
    
    protected boolean inRange(Element next) {
        int startOffset = getStartOffset();
        int endOffset = getEndOffset();
        if ((next.getStartOffset() >= startOffset && next.getStartOffset() < endOffset) || (startOffset >= next.getStartOffset() && startOffset < next.getEndOffset())) {
            return true;
        }
        return false;
    }
    
    protected abstract void write() throws IOException, BadLocationException;
    
    protected String getText(Element elem) throws BadLocationException {
        return doc.getText(elem.getStartOffset(), elem.getEndOffset() - elem.getStartOffset());
    }
    
    protected void text(Element elem) throws BadLocationException, IOException {
        int start = Math.max(getStartOffset(), elem.getStartOffset());
        int end = Math.min(getEndOffset(), elem.getEndOffset());
        if (start < end) {
            if (segment == null) {
                segment = new Segment();
            }
            getDocument().getText(start, end - start, segment);
            if (segment.count > 0) {
                write(segment.array, segment.offset, segment.count);
            }
        }
    }
    
    protected void setLineLength(int l) {
        maxLineLength = l;
    }
    
    protected int getLineLength() {
        return maxLineLength;
    }
    
    protected void setCurrentLineLength(int length) {
        currLength = length;
        isLineEmpty = (currLength == 0);
    }
    
    protected int getCurrentLineLength() {
        return currLength;
    }
    
    protected boolean isLineEmpty() {
        return isLineEmpty;
    }
    
    protected void setCanWrapLines(boolean newValue) {
        canWrapLines = newValue;
    }
    
    protected boolean getCanWrapLines() {
        return canWrapLines;
    }
    
    protected void setIndentSpace(int space) {
        indentSpace = space;
    }
    
    protected int getIndentSpace() {
        return indentSpace;
    }
    
    public void setLineSeparator(String value) {
        lineSeparator = value;
    }
    
    public String getLineSeparator() {
        return lineSeparator;
    }
    
    protected void incrIndent() {
        if (offsetIndent > 0) {
            offsetIndent++;
        } else {
            if (++indentLevel * getIndentSpace() >= getLineLength()) {
                offsetIndent++;
                --indentLevel;
            }
        }
    }
    
    protected void decrIndent() {
        if (offsetIndent > 0) {
            --offsetIndent;
        } else {
            indentLevel--;
        }
    }
    
    protected int getIndentLevel() {
        return indentLevel;
    }
    
    protected void indent() throws IOException {
        int max = getIndentLevel() * getIndentSpace();
        if (indentChars == null || max > indentChars.length) {
            indentChars = new char[max];
            for (int counter = 0; counter < max; counter++) {
                indentChars[counter] = ' ';
            }
        }
        int length = getCurrentLineLength();
        boolean wasEmpty = isLineEmpty();
        output(indentChars, 0, max);
        if (wasEmpty && length == 0) {
            isLineEmpty = true;
        }
    }
    
    protected void write(char ch) throws IOException {
        if (tempChars == null) {
            tempChars = new char[128];
        }
        tempChars[0] = ch;
        write(tempChars, 0, 1);
    }
    
    protected void write(String content) throws IOException {
        if (content == null) {
            return;
        }
        int size = content.length();
        if (tempChars == null || tempChars.length < size) {
            tempChars = new char[size];
        }
        content.getChars(0, size, tempChars, 0);
        write(tempChars, 0, size);
    }
    
    protected void writeLineSeparator() throws IOException {
        String newline = getLineSeparator();
        int length = newline.length();
        if (newlineChars == null || newlineChars.length < length) {
            newlineChars = new char[length];
        }
        newline.getChars(0, length, newlineChars, 0);
        output(newlineChars, 0, length);
        setCurrentLineLength(0);
    }
    
    protected void write(char[] chars, int startIndex, int length) throws IOException {
        if (!getCanWrapLines()) {
            int lastIndex = startIndex;
            int endIndex = startIndex + length;
            int newlineIndex = indexOf(chars, NEWLINE, startIndex, endIndex);
            while (newlineIndex != -1) {
                if (newlineIndex > lastIndex) {
                    output(chars, lastIndex, newlineIndex - lastIndex);
                }
                writeLineSeparator();
                lastIndex = newlineIndex + 1;
                newlineIndex = indexOf(chars, '\n', lastIndex, endIndex);
            }
            if (lastIndex < endIndex) {
                output(chars, lastIndex, endIndex - lastIndex);
            }
        } else {
            int lastIndex = startIndex;
            int endIndex = startIndex + length;
            int lineLength = getCurrentLineLength();
            int maxLength = getLineLength();
            while (lastIndex < endIndex) {
                int newlineIndex = indexOf(chars, NEWLINE, lastIndex, endIndex);
                boolean needsNewline = false;
                boolean forceNewLine = false;
                lineLength = getCurrentLineLength();
                if (newlineIndex != -1 && (lineLength + (newlineIndex - lastIndex)) < maxLength) {
                    if (newlineIndex > lastIndex) {
                        output(chars, lastIndex, newlineIndex - lastIndex);
                    }
                    lastIndex = newlineIndex + 1;
                    forceNewLine = true;
                } else if (newlineIndex == -1 && (lineLength + (endIndex - lastIndex)) < maxLength) {
                    if (endIndex > lastIndex) {
                        output(chars, lastIndex, endIndex - lastIndex);
                    }
                    lastIndex = endIndex;
                } else {
                    int breakPoint = -1;
                    int maxBreak = Math.min(endIndex - lastIndex, maxLength - lineLength - 1);
                    int counter = 0;
                    while (counter < maxBreak) {
                        if (Character.isWhitespace(chars[counter + lastIndex])) {
                            breakPoint = counter;
                        }
                        counter++;
                    }
                    if (breakPoint != -1) {
                        breakPoint += lastIndex + 1;
                        output(chars, lastIndex, breakPoint - lastIndex);
                        lastIndex = breakPoint;
                        needsNewline = true;
                    } else {
                        counter = Math.max(0, maxBreak);
                        maxBreak = endIndex - lastIndex;
                        while (counter < maxBreak) {
                            if (Character.isWhitespace(chars[counter + lastIndex])) {
                                breakPoint = counter;
                                break;
                            }
                            counter++;
                        }
                        if (breakPoint == -1) {
                            output(chars, lastIndex, endIndex - lastIndex);
                            breakPoint = endIndex;
                        } else {
                            breakPoint += lastIndex;
                            if (chars[breakPoint] == NEWLINE) {
                                output(chars, lastIndex, breakPoint++ - lastIndex);
                                forceNewLine = true;
                            } else {
                                output(chars, lastIndex, ++breakPoint - lastIndex);
                                needsNewline = true;
                            }
                        }
                        lastIndex = breakPoint;
                    }
                }
                if (forceNewLine || needsNewline || lastIndex < endIndex) {
                    writeLineSeparator();
                    if (lastIndex < endIndex || !forceNewLine) {
                        indent();
                    }
                }
            }
        }
    }
    
    protected void writeAttributes(AttributeSet attr) throws IOException {
        Enumeration names = attr.getAttributeNames();
        while (names.hasMoreElements()) {
            Object name = names.nextElement();
            write(" " + name + "=" + attr.getAttribute(name));
        }
    }
    
    protected void output(char[] content, int start, int length) throws IOException {
        getWriter().write(content, start, length);
        setCurrentLineLength(getCurrentLineLength() + length);
    }
    
    private int indexOf(char[] chars, char sChar, int startIndex, int endIndex) {
        while (startIndex < endIndex) {
            if (chars[startIndex] == sChar) {
                return startIndex;
            }
            startIndex++;
        }
        return -1;
    }
}
