package javax.swing.text;

import java.awt.Color;
import java.awt.Font;
import java.awt.font.TextAttribute;
import java.util.Enumeration;
import java.util.Vector;
import java.io.IOException;
import java.io.ObjectInputStream;
import javax.swing.event.*;
import javax.swing.undo.UndoableEdit;
import javax.swing.SwingUtilities;

public class DefaultStyledDocument extends AbstractDocument implements StyledDocument {
    
    public DefaultStyledDocument(AbstractDocument$Content c, StyleContext styles) {
        super(c, styles);
        listeningStyles = new Vector();
        buffer = new DefaultStyledDocument$ElementBuffer(this, createDefaultRoot());
        Style defaultStyle = styles.getStyle(StyleContext.DEFAULT_STYLE);
        setLogicalStyle(0, defaultStyle);
    }
    
    public DefaultStyledDocument(StyleContext styles) {
        this(new GapContent(BUFFER_SIZE_DEFAULT), styles);
    }
    
    public DefaultStyledDocument() {
        this(new GapContent(BUFFER_SIZE_DEFAULT), new StyleContext());
    }
    
    public Element getDefaultRootElement() {
        return buffer.getRootElement();
    }
    
    protected void create(DefaultStyledDocument$ElementSpec[] data) {
        try {
            if (getLength() != 0) {
                remove(0, getLength());
            }
            writeLock();
            AbstractDocument$Content c = getContent();
            int n = data.length;
            StringBuffer sb = new StringBuffer();
            for (int i = 0; i < n; i++) {
                DefaultStyledDocument$ElementSpec es = data[i];
                if (es.getLength() > 0) {
                    sb.append(es.getArray(), es.getOffset(), es.getLength());
                }
            }
            UndoableEdit cEdit = c.insertString(0, sb.toString());
            int length = sb.length();
            AbstractDocument$DefaultDocumentEvent evnt = new AbstractDocument$DefaultDocumentEvent(this, 0, length, DocumentEvent$EventType.INSERT);
            evnt.addEdit(cEdit);
            buffer.create(length, data, evnt);
            super.insertUpdate(evnt, null);
            evnt.end();
            fireInsertUpdate(evnt);
            fireUndoableEditUpdate(new UndoableEditEvent(this, evnt));
        } catch (BadLocationException ble) {
            throw new StateInvariantError("problem initializing");
        } finally {
            writeUnlock();
        }
    }
    
    protected void insert(int offset, DefaultStyledDocument$ElementSpec[] data) throws BadLocationException {
        if (data == null || data.length == 0) {
            return;
        }
        try {
            writeLock();
            AbstractDocument$Content c = getContent();
            int n = data.length;
            StringBuffer sb = new StringBuffer();
            for (int i = 0; i < n; i++) {
                DefaultStyledDocument$ElementSpec es = data[i];
                if (es.getLength() > 0) {
                    sb.append(es.getArray(), es.getOffset(), es.getLength());
                }
            }
            if (sb.length() == 0) {
                return;
            }
            UndoableEdit cEdit = c.insertString(offset, sb.toString());
            int length = sb.length();
            AbstractDocument$DefaultDocumentEvent evnt = new AbstractDocument$DefaultDocumentEvent(this, offset, length, DocumentEvent$EventType.INSERT);
            evnt.addEdit(cEdit);
            buffer.insert(offset, length, data, evnt);
            super.insertUpdate(evnt, null);
            evnt.end();
            fireInsertUpdate(evnt);
            fireUndoableEditUpdate(new UndoableEditEvent(this, evnt));
        } finally {
            writeUnlock();
        }
    }
    
    public Style addStyle(String nm, Style parent) {
        StyleContext styles = (StyleContext)(StyleContext)getAttributeContext();
        return styles.addStyle(nm, parent);
    }
    
    public void removeStyle(String nm) {
        StyleContext styles = (StyleContext)(StyleContext)getAttributeContext();
        styles.removeStyle(nm);
    }
    
    public Style getStyle(String nm) {
        StyleContext styles = (StyleContext)(StyleContext)getAttributeContext();
        return styles.getStyle(nm);
    }
    
    public Enumeration getStyleNames() {
        return ((StyleContext)(StyleContext)getAttributeContext()).getStyleNames();
    }
    
    public void setLogicalStyle(int pos, Style s) {
        Element paragraph = getParagraphElement(pos);
        if ((paragraph != null) && (paragraph instanceof AbstractDocument$AbstractElement)) {
            try {
                writeLock();
                DefaultStyledDocument$StyleChangeUndoableEdit edit = new DefaultStyledDocument$StyleChangeUndoableEdit((AbstractDocument$AbstractElement)(AbstractDocument$AbstractElement)paragraph, s);
                ((AbstractDocument$AbstractElement)(AbstractDocument$AbstractElement)paragraph).setResolveParent(s);
                int p0 = paragraph.getStartOffset();
                int p1 = paragraph.getEndOffset();
                AbstractDocument$DefaultDocumentEvent e = new AbstractDocument$DefaultDocumentEvent(this, p0, p1 - p0, DocumentEvent$EventType.CHANGE);
                e.addEdit(edit);
                e.end();
                fireChangedUpdate(e);
                fireUndoableEditUpdate(new UndoableEditEvent(this, e));
            } finally {
                writeUnlock();
            }
        }
    }
    
    public Style getLogicalStyle(int p) {
        Style s = null;
        Element paragraph = getParagraphElement(p);
        if (paragraph != null) {
            AttributeSet a = paragraph.getAttributes();
            AttributeSet parent = a.getResolveParent();
            if (parent instanceof Style) {
                s = (Style)(Style)parent;
            }
        }
        return s;
    }
    
    public void setCharacterAttributes(int offset, int length, AttributeSet s, boolean replace) {
        if (length == 0) {
            return;
        }
        try {
            writeLock();
            AbstractDocument$DefaultDocumentEvent changes = new AbstractDocument$DefaultDocumentEvent(this, offset, length, DocumentEvent$EventType.CHANGE);
            buffer.change(offset, length, changes);
            AttributeSet sCopy = s.copyAttributes();
            int lastEnd = Integer.MAX_VALUE;
            for (int pos = offset; pos < (offset + length); pos = lastEnd) {
                Element run = getCharacterElement(pos);
                lastEnd = run.getEndOffset();
                if (pos == lastEnd) {
                    break;
                }
                MutableAttributeSet attr = (MutableAttributeSet)(MutableAttributeSet)run.getAttributes();
                changes.addEdit(new DefaultStyledDocument$AttributeUndoableEdit(run, sCopy, replace));
                if (replace) {
                    attr.removeAttributes(attr);
                }
                attr.addAttributes(s);
            }
            changes.end();
            fireChangedUpdate(changes);
            fireUndoableEditUpdate(new UndoableEditEvent(this, changes));
        } finally {
            writeUnlock();
        }
    }
    
    public void setParagraphAttributes(int offset, int length, AttributeSet s, boolean replace) {
        try {
            writeLock();
            AbstractDocument$DefaultDocumentEvent changes = new AbstractDocument$DefaultDocumentEvent(this, offset, length, DocumentEvent$EventType.CHANGE);
            AttributeSet sCopy = s.copyAttributes();
            Element section = getDefaultRootElement();
            int index0 = section.getElementIndex(offset);
            int index1 = section.getElementIndex(offset + ((length > 0) ? length - 1 : 0));
            boolean isI18N = Boolean.TRUE.equals(getProperty(I18NProperty));
            boolean hasRuns = false;
            for (int i = index0; i <= index1; i++) {
                Element paragraph = section.getElement(i);
                MutableAttributeSet attr = (MutableAttributeSet)(MutableAttributeSet)paragraph.getAttributes();
                changes.addEdit(new DefaultStyledDocument$AttributeUndoableEdit(paragraph, sCopy, replace));
                if (replace) {
                    attr.removeAttributes(attr);
                }
                attr.addAttributes(s);
                if (isI18N && !hasRuns) {
                    hasRuns = (attr.getAttribute(TextAttribute.RUN_DIRECTION) != null);
                }
            }
            if (hasRuns) {
                updateBidi(changes);
            }
            changes.end();
            fireChangedUpdate(changes);
            fireUndoableEditUpdate(new UndoableEditEvent(this, changes));
        } finally {
            writeUnlock();
        }
    }
    
    public Element getParagraphElement(int pos) {
        Element e = null;
        for (e = getDefaultRootElement(); !e.isLeaf(); ) {
            int index = e.getElementIndex(pos);
            e = e.getElement(index);
        }
        if (e != null) return e.getParentElement();
        return e;
    }
    
    public Element getCharacterElement(int pos) {
        Element e = null;
        for (e = getDefaultRootElement(); !e.isLeaf(); ) {
            int index = e.getElementIndex(pos);
            e = e.getElement(index);
        }
        return e;
    }
    
    protected void insertUpdate(AbstractDocument$DefaultDocumentEvent chng, AttributeSet attr) {
        int offset = chng.getOffset();
        int length = chng.getLength();
        if (attr == null) {
            attr = SimpleAttributeSet.EMPTY;
        }
        Element paragraph = getParagraphElement(offset + length);
        AttributeSet pattr = paragraph.getAttributes();
        Element pParagraph = getParagraphElement(offset);
        Element run = pParagraph.getElement(pParagraph.getElementIndex(offset));
        int endOffset = offset + length;
        boolean insertingAtBoundry = (run.getEndOffset() == endOffset);
        AttributeSet cattr = run.getAttributes();
        try {
            Segment s = new Segment();
            Vector parseBuffer = new Vector();
            DefaultStyledDocument$ElementSpec lastStartSpec = null;
            boolean insertingAfterNewline = false;
            short lastStartDirection = DefaultStyledDocument$ElementSpec.OriginateDirection;
            if (offset > 0) {
                getText(offset - 1, 1, s);
                if (s.array[s.offset] == '\n') {
                    insertingAfterNewline = true;
                    lastStartDirection = createSpecsForInsertAfterNewline(paragraph, pParagraph, pattr, parseBuffer, offset, endOffset);
                    for (int counter = parseBuffer.size() - 1; counter >= 0; counter--) {
                        DefaultStyledDocument$ElementSpec spec = (DefaultStyledDocument$ElementSpec)(DefaultStyledDocument$ElementSpec)parseBuffer.elementAt(counter);
                        if (spec.getType() == DefaultStyledDocument$ElementSpec.StartTagType) {
                            lastStartSpec = spec;
                            break;
                        }
                    }
                }
            }
            if (!insertingAfterNewline) pattr = pParagraph.getAttributes();
            getText(offset, length, s);
            char[] txt = s.array;
            int n = s.offset + s.count;
            int lastOffset = s.offset;
            for (int i = s.offset; i < n; i++) {
                if (txt[i] == '\n') {
                    int breakOffset = i + 1;
                    parseBuffer.addElement(new DefaultStyledDocument$ElementSpec(attr, DefaultStyledDocument$ElementSpec.ContentType, breakOffset - lastOffset));
                    parseBuffer.addElement(new DefaultStyledDocument$ElementSpec(null, DefaultStyledDocument$ElementSpec.EndTagType));
                    lastStartSpec = new DefaultStyledDocument$ElementSpec(pattr, DefaultStyledDocument$ElementSpec.StartTagType);
                    parseBuffer.addElement(lastStartSpec);
                    lastOffset = breakOffset;
                }
            }
            if (lastOffset < n) {
                parseBuffer.addElement(new DefaultStyledDocument$ElementSpec(attr, DefaultStyledDocument$ElementSpec.ContentType, n - lastOffset));
            }
            DefaultStyledDocument$ElementSpec first = (DefaultStyledDocument$ElementSpec)(DefaultStyledDocument$ElementSpec)parseBuffer.firstElement();
            int docLength = getLength();
            if (first.getType() == DefaultStyledDocument$ElementSpec.ContentType && cattr.isEqual(attr)) {
                first.setDirection(DefaultStyledDocument$ElementSpec.JoinPreviousDirection);
            }
            if (lastStartSpec != null) {
                if (insertingAfterNewline) {
                    lastStartSpec.setDirection(lastStartDirection);
                } else if (pParagraph.getEndOffset() != endOffset) {
                    lastStartSpec.setDirection(DefaultStyledDocument$ElementSpec.JoinFractureDirection);
                } else {
                    Element parent = pParagraph.getParentElement();
                    int pParagraphIndex = parent.getElementIndex(offset);
                    if ((pParagraphIndex + 1) < parent.getElementCount() && !parent.getElement(pParagraphIndex + 1).isLeaf()) {
                        lastStartSpec.setDirection(DefaultStyledDocument$ElementSpec.JoinNextDirection);
                    }
                }
            }
            if (insertingAtBoundry && endOffset < docLength) {
                DefaultStyledDocument$ElementSpec last = (DefaultStyledDocument$ElementSpec)(DefaultStyledDocument$ElementSpec)parseBuffer.lastElement();
                if (last.getType() == DefaultStyledDocument$ElementSpec.ContentType && last.getDirection() != DefaultStyledDocument$ElementSpec.JoinPreviousDirection && ((lastStartSpec == null && (paragraph == pParagraph || insertingAfterNewline)) || (lastStartSpec != null && lastStartSpec.getDirection() != DefaultStyledDocument$ElementSpec.OriginateDirection))) {
                    Element nextRun = paragraph.getElement(paragraph.getElementIndex(endOffset));
                    if (nextRun.isLeaf() && attr.isEqual(nextRun.getAttributes())) {
                        last.setDirection(DefaultStyledDocument$ElementSpec.JoinNextDirection);
                    }
                }
            } else if (!insertingAtBoundry && lastStartSpec != null && lastStartSpec.getDirection() == DefaultStyledDocument$ElementSpec.JoinFractureDirection) {
                DefaultStyledDocument$ElementSpec last = (DefaultStyledDocument$ElementSpec)(DefaultStyledDocument$ElementSpec)parseBuffer.lastElement();
                if (last.getType() == DefaultStyledDocument$ElementSpec.ContentType && last.getDirection() != DefaultStyledDocument$ElementSpec.JoinPreviousDirection && attr.isEqual(cattr)) {
                    last.setDirection(DefaultStyledDocument$ElementSpec.JoinNextDirection);
                }
            }
            if (Utilities.isComposedTextAttributeDefined(attr)) {
                ((MutableAttributeSet)(MutableAttributeSet)attr).addAttributes(cattr);
                ((MutableAttributeSet)(MutableAttributeSet)attr).addAttribute(AbstractDocument.ElementNameAttribute, AbstractDocument.ContentElementName);
            }
            DefaultStyledDocument$ElementSpec[] spec = new DefaultStyledDocument$ElementSpec[parseBuffer.size()];
            parseBuffer.copyInto(spec);
            buffer.insert(offset, length, spec, chng);
        } catch (BadLocationException bl) {
        }
        super.insertUpdate(chng, attr);
    }
    
    short createSpecsForInsertAfterNewline(Element paragraph, Element pParagraph, AttributeSet pattr, Vector parseBuffer, int offset, int endOffset) {
        if (paragraph.getParentElement() == pParagraph.getParentElement()) {
            DefaultStyledDocument$ElementSpec spec = new DefaultStyledDocument$ElementSpec(pattr, DefaultStyledDocument$ElementSpec.EndTagType);
            parseBuffer.addElement(spec);
            spec = new DefaultStyledDocument$ElementSpec(pattr, DefaultStyledDocument$ElementSpec.StartTagType);
            parseBuffer.addElement(spec);
            if (pParagraph.getEndOffset() != endOffset) return DefaultStyledDocument$ElementSpec.JoinFractureDirection;
            Element parent = pParagraph.getParentElement();
            if ((parent.getElementIndex(offset) + 1) < parent.getElementCount()) return DefaultStyledDocument$ElementSpec.JoinNextDirection;
        } else {
            Vector leftParents = new Vector();
            Vector rightParents = new Vector();
            Element e = pParagraph;
            while (e != null) {
                leftParents.addElement(e);
                e = e.getParentElement();
            }
            e = paragraph;
            int leftIndex = -1;
            while (e != null && (leftIndex = leftParents.indexOf(e)) == -1) {
                rightParents.addElement(e);
                e = e.getParentElement();
            }
            if (e != null) {
                for (int counter = 0; counter < leftIndex; counter++) {
                    parseBuffer.addElement(new DefaultStyledDocument$ElementSpec(null, DefaultStyledDocument$ElementSpec.EndTagType));
                }
                DefaultStyledDocument$ElementSpec spec = null;
                for (int counter = rightParents.size() - 1; counter >= 0; counter--) {
                    spec = new DefaultStyledDocument$ElementSpec(((Element)(Element)rightParents.elementAt(counter)).getAttributes(), DefaultStyledDocument$ElementSpec.StartTagType);
                    if (counter > 0) spec.setDirection(DefaultStyledDocument$ElementSpec.JoinNextDirection);
                    parseBuffer.addElement(spec);
                }
                if (rightParents.size() > 0) return DefaultStyledDocument$ElementSpec.JoinNextDirection;
                return DefaultStyledDocument$ElementSpec.JoinFractureDirection;
            }
        }
        return DefaultStyledDocument$ElementSpec.OriginateDirection;
    }
    
    protected void removeUpdate(AbstractDocument$DefaultDocumentEvent chng) {
        super.removeUpdate(chng);
        buffer.remove(chng.getOffset(), chng.getLength(), chng);
    }
    
    protected AbstractDocument$AbstractElement createDefaultRoot() {
        writeLock();
        AbstractDocument$BranchElement section = new DefaultStyledDocument$SectionElement(this);
        AbstractDocument$BranchElement paragraph = new AbstractDocument$BranchElement(this, section, null);
        AbstractDocument$LeafElement brk = new AbstractDocument$LeafElement(this, paragraph, null, 0, 1);
        Element[] buff = new Element[1];
        buff[0] = brk;
        paragraph.replace(0, 0, buff);
        buff[0] = paragraph;
        section.replace(0, 0, buff);
        writeUnlock();
        return section;
    }
    
    public Color getForeground(AttributeSet attr) {
        StyleContext styles = (StyleContext)(StyleContext)getAttributeContext();
        return styles.getForeground(attr);
    }
    
    public Color getBackground(AttributeSet attr) {
        StyleContext styles = (StyleContext)(StyleContext)getAttributeContext();
        return styles.getBackground(attr);
    }
    
    public Font getFont(AttributeSet attr) {
        StyleContext styles = (StyleContext)(StyleContext)getAttributeContext();
        return styles.getFont(attr);
    }
    
    protected void styleChanged(Style style) {
        if (getLength() != 0) {
            if (updateRunnable == null) {
                updateRunnable = new DefaultStyledDocument$ChangeUpdateRunnable(this);
            }
            synchronized (updateRunnable) {
                if (!updateRunnable.isPending) {
                    SwingUtilities.invokeLater(updateRunnable);
                    updateRunnable.isPending = true;
                }
            }
        }
    }
    
    public void addDocumentListener(DocumentListener listener) {
        synchronized (listeningStyles) {
            int oldDLCount = listenerList.getListenerCount(DocumentListener.class);
            super.addDocumentListener(listener);
            if (oldDLCount == 0) {
                if (styleContextChangeListener == null) {
                    styleContextChangeListener = createStyleContextChangeListener();
                }
                if (styleContextChangeListener != null) {
                    StyleContext styles = (StyleContext)(StyleContext)getAttributeContext();
                    styles.addChangeListener(styleContextChangeListener);
                }
                updateStylesListeningTo();
            }
        }
    }
    
    public void removeDocumentListener(DocumentListener listener) {
        synchronized (listeningStyles) {
            super.removeDocumentListener(listener);
            if (listenerList.getListenerCount(DocumentListener.class) == 0) {
                for (int counter = listeningStyles.size() - 1; counter >= 0; counter--) {
                    ((Style)(Style)listeningStyles.elementAt(counter)).removeChangeListener(styleChangeListener);
                }
                listeningStyles.removeAllElements();
                if (styleContextChangeListener != null) {
                    StyleContext styles = (StyleContext)(StyleContext)getAttributeContext();
                    styles.removeChangeListener(styleContextChangeListener);
                }
            }
        }
    }
    
    ChangeListener createStyleChangeListener() {
        return new DefaultStyledDocument$StyleChangeHandler(this);
    }
    
    ChangeListener createStyleContextChangeListener() {
        return new DefaultStyledDocument$StyleContextChangeHandler(this);
    }
    
    void updateStylesListeningTo() {
        synchronized (listeningStyles) {
            StyleContext styles = (StyleContext)(StyleContext)getAttributeContext();
            if (styleChangeListener == null) {
                styleChangeListener = createStyleChangeListener();
            }
            if (styleChangeListener != null && styles != null) {
                Enumeration styleNames = styles.getStyleNames();
                Vector v = (Vector)(Vector)listeningStyles.clone();
                listeningStyles.removeAllElements();
                while (styleNames.hasMoreElements()) {
                    String name = (String)(String)styleNames.nextElement();
                    Style aStyle = styles.getStyle(name);
                    int index = v.indexOf(aStyle);
                    listeningStyles.addElement(aStyle);
                    if (index == -1) {
                        aStyle.addChangeListener(styleChangeListener);
                    } else {
                        v.removeElementAt(index);
                    }
                }
                for (int counter = v.size() - 1; counter >= 0; counter--) {
                    Style aStyle = (Style)(Style)v.elementAt(counter);
                    aStyle.removeChangeListener(styleChangeListener);
                }
                if (listeningStyles.size() == 0) {
                    styleChangeListener = null;
                }
            }
        }
    }
    
    private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException {
        listeningStyles = new Vector();
        s.defaultReadObject();
        if (styleContextChangeListener == null && listenerList.getListenerCount(DocumentListener.class) > 0) {
            styleContextChangeListener = createStyleContextChangeListener();
            if (styleContextChangeListener != null) {
                StyleContext styles = (StyleContext)(StyleContext)getAttributeContext();
                styles.addChangeListener(styleContextChangeListener);
            }
            updateStylesListeningTo();
        }
    }
    public static final int BUFFER_SIZE_DEFAULT = 4096;
    protected DefaultStyledDocument$ElementBuffer buffer;
    private transient Vector listeningStyles;
    private transient ChangeListener styleChangeListener;
    private transient ChangeListener styleContextChangeListener;
    private transient DefaultStyledDocument$ChangeUpdateRunnable updateRunnable;
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
}
