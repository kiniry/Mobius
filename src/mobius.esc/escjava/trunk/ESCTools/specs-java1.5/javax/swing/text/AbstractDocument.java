package javax.swing.text;

import java.util.*;
import java.io.*;
import java.awt.font.TextAttribute;
import java.text.Bidi;
import javax.swing.undo.*;
import javax.swing.event.*;
import sun.font.BidiUtils;

public abstract class AbstractDocument implements Document, Serializable {
    
    protected AbstractDocument(AbstractDocument$Content data) {
        this(data, StyleContext.getDefaultStyleContext());
    }
    
    protected AbstractDocument(AbstractDocument$Content data, AbstractDocument$AttributeContext context) {
        
        this.data = data;
        this.context = context;
        bidiRoot = new AbstractDocument$BidiRootElement(this);
        if (defaultI18NProperty == null) {
            Object o = java.security.AccessController.doPrivileged(new AbstractDocument$1(this));
            if (o != null) {
                defaultI18NProperty = Boolean.valueOf((String)(String)o);
            } else {
                defaultI18NProperty = Boolean.FALSE;
            }
        }
        putProperty(I18NProperty, defaultI18NProperty);
        writeLock();
        try {
            Element[] p = new Element[1];
            p[0] = new AbstractDocument$BidiElement(this, bidiRoot, 0, 1, 0);
            bidiRoot.replace(0, 0, p);
        } finally {
            writeUnlock();
        }
    }
    
    public Dictionary getDocumentProperties() {
        if (documentProperties == null) {
            documentProperties = new Hashtable(2);
        }
        return documentProperties;
    }
    
    public void setDocumentProperties(Dictionary x) {
        documentProperties = x;
    }
    
    protected void fireInsertUpdate(DocumentEvent e) {
        notifyingListeners = true;
        try {
            Object[] listeners = listenerList.getListenerList();
            for (int i = listeners.length - 2; i >= 0; i -= 2) {
                if (listeners[i] == DocumentListener.class) {
                    ((DocumentListener)(DocumentListener)listeners[i + 1]).insertUpdate(e);
                }
            }
        } finally {
            notifyingListeners = false;
        }
    }
    
    protected void fireChangedUpdate(DocumentEvent e) {
        notifyingListeners = true;
        try {
            Object[] listeners = listenerList.getListenerList();
            for (int i = listeners.length - 2; i >= 0; i -= 2) {
                if (listeners[i] == DocumentListener.class) {
                    ((DocumentListener)(DocumentListener)listeners[i + 1]).changedUpdate(e);
                }
            }
        } finally {
            notifyingListeners = false;
        }
    }
    
    protected void fireRemoveUpdate(DocumentEvent e) {
        notifyingListeners = true;
        try {
            Object[] listeners = listenerList.getListenerList();
            for (int i = listeners.length - 2; i >= 0; i -= 2) {
                if (listeners[i] == DocumentListener.class) {
                    ((DocumentListener)(DocumentListener)listeners[i + 1]).removeUpdate(e);
                }
            }
        } finally {
            notifyingListeners = false;
        }
    }
    
    protected void fireUndoableEditUpdate(UndoableEditEvent e) {
        Object[] listeners = listenerList.getListenerList();
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == UndoableEditListener.class) {
                ((UndoableEditListener)(UndoableEditListener)listeners[i + 1]).undoableEditHappened(e);
            }
        }
    }
    
    public EventListener[] getListeners(Class listenerType) {
        return listenerList.getListeners(listenerType);
    }
    
    public int getAsynchronousLoadPriority() {
        Integer loadPriority = (Integer)(Integer)getProperty(AbstractDocument.AsyncLoadPriority);
        if (loadPriority != null) {
            return loadPriority.intValue();
        }
        return -1;
    }
    
    public void setAsynchronousLoadPriority(int p) {
        Integer loadPriority = (p >= 0) ? new Integer(p) : null;
        putProperty(AbstractDocument.AsyncLoadPriority, loadPriority);
    }
    
    public void setDocumentFilter(DocumentFilter filter) {
        documentFilter = filter;
    }
    
    public DocumentFilter getDocumentFilter() {
        return documentFilter;
    }
    
    public void render(Runnable r) {
        readLock();
        try {
            r.run();
        } finally {
            readUnlock();
        }
    }
    
    public int getLength() {
        return data.length() - 1;
    }
    
    public void addDocumentListener(DocumentListener listener) {
        listenerList.add(DocumentListener.class, listener);
    }
    
    public void removeDocumentListener(DocumentListener listener) {
        listenerList.remove(DocumentListener.class, listener);
    }
    
    public DocumentListener[] getDocumentListeners() {
        return (DocumentListener[])(DocumentListener[])listenerList.getListeners(DocumentListener.class);
    }
    
    public void addUndoableEditListener(UndoableEditListener listener) {
        listenerList.add(UndoableEditListener.class, listener);
    }
    
    public void removeUndoableEditListener(UndoableEditListener listener) {
        listenerList.remove(UndoableEditListener.class, listener);
    }
    
    public UndoableEditListener[] getUndoableEditListeners() {
        return (UndoableEditListener[])(UndoableEditListener[])listenerList.getListeners(UndoableEditListener.class);
    }
    
    public final Object getProperty(Object key) {
        return getDocumentProperties().get(key);
    }
    
    public final void putProperty(Object key, Object value) {
        if (value != null) {
            getDocumentProperties().put(key, value);
        } else {
            getDocumentProperties().remove(key);
        }
        if (key == TextAttribute.RUN_DIRECTION && Boolean.TRUE.equals(getProperty(I18NProperty))) {
            writeLock();
            try {
                AbstractDocument$DefaultDocumentEvent e = new AbstractDocument$DefaultDocumentEvent(this, 0, getLength(), DocumentEvent$EventType.INSERT);
                updateBidi(e);
            } finally {
                writeUnlock();
            }
        }
    }
    
    public void remove(int offs, int len) throws BadLocationException {
        DocumentFilter filter = getDocumentFilter();
        writeLock();
        try {
            if (filter != null) {
                filter.remove(getFilterBypass(), offs, len);
            } else {
                handleRemove(offs, len);
            }
        } finally {
            writeUnlock();
        }
    }
    
    void handleRemove(int offs, int len) throws BadLocationException {
        if (len > 0) {
            if (offs < 0 || (offs + len) > getLength()) {
                throw new BadLocationException("Invalid remove", getLength() + 1);
            }
            AbstractDocument$DefaultDocumentEvent chng = new AbstractDocument$DefaultDocumentEvent(this, offs, len, DocumentEvent$EventType.REMOVE);
            boolean isComposedTextElement = false;
            isComposedTextElement = Utilities.isComposedTextElement(this, offs);
            removeUpdate(chng);
            UndoableEdit u = data.remove(offs, len);
            if (u != null) {
                chng.addEdit(u);
            }
            postRemoveUpdate(chng);
            chng.end();
            fireRemoveUpdate(chng);
            if ((u != null) && !isComposedTextElement) {
                fireUndoableEditUpdate(new UndoableEditEvent(this, chng));
            }
        }
    }
    
    private static final boolean isComplex(char ch) {
        return (ch >= '\u0900' && ch <= '\u0d7f') || (ch >= '\u0e00' && ch <= '\u0e7f') || (ch >= '\ud800' && ch <= '\udfff');
    }
    
    private static final boolean isComplex(char[] text, int start, int limit) {
        for (int i = start; i < limit; ++i) {
            if (isComplex(text[i])) {
                return true;
            }
        }
        return false;
    }
    
    public void replace(int offset, int length, String text, AttributeSet attrs) throws BadLocationException {
        if (length == 0 && (text == null || text.length() == 0)) {
            return;
        }
        DocumentFilter filter = getDocumentFilter();
        writeLock();
        try {
            if (filter != null) {
                filter.replace(getFilterBypass(), offset, length, text, attrs);
            } else {
                if (length > 0) {
                    remove(offset, length);
                }
                if (text != null && text.length() > 0) {
                    insertString(offset, text, attrs);
                }
            }
        } finally {
            writeUnlock();
        }
    }
    
    public void insertString(int offs, String str, AttributeSet a) throws BadLocationException {
        if ((str == null) || (str.length() == 0)) {
            return;
        }
        DocumentFilter filter = getDocumentFilter();
        writeLock();
        try {
            if (filter != null) {
                filter.insertString(getFilterBypass(), offs, str, a);
            } else {
                handleInsertString(offs, str, a);
            }
        } finally {
            writeUnlock();
        }
    }
    
    void handleInsertString(int offs, String str, AttributeSet a) throws BadLocationException {
        if ((str == null) || (str.length() == 0)) {
            return;
        }
        UndoableEdit u = data.insertString(offs, str);
        AbstractDocument$DefaultDocumentEvent e = new AbstractDocument$DefaultDocumentEvent(this, offs, str.length(), DocumentEvent$EventType.INSERT);
        if (u != null) {
            e.addEdit(u);
        }
        if (getProperty(I18NProperty).equals(Boolean.FALSE)) {
            Object d = getProperty(TextAttribute.RUN_DIRECTION);
            if ((d != null) && (d.equals(TextAttribute.RUN_DIRECTION_RTL))) {
                putProperty(I18NProperty, Boolean.TRUE);
            } else {
                char[] chars = str.toCharArray();
                if (Bidi.requiresBidi(chars, 0, chars.length) || isComplex(chars, 0, chars.length)) {
                    putProperty(I18NProperty, Boolean.TRUE);
                }
            }
        }
        insertUpdate(e, a);
        e.end();
        fireInsertUpdate(e);
        if (u != null && (a == null || !a.isDefined(StyleConstants.ComposedTextAttribute))) {
            fireUndoableEditUpdate(new UndoableEditEvent(this, e));
        }
    }
    
    public String getText(int offset, int length) throws BadLocationException {
        if (length < 0) {
            throw new BadLocationException("Length must be positive", length);
        }
        String str = data.getString(offset, length);
        return str;
    }
    
    public void getText(int offset, int length, Segment txt) throws BadLocationException {
        if (length < 0) {
            throw new BadLocationException("Length must be positive", length);
        }
        data.getChars(offset, length, txt);
    }
    
    public synchronized Position createPosition(int offs) throws BadLocationException {
        return data.createPosition(offs);
    }
    
    public final Position getStartPosition() {
        Position p;
        try {
            p = createPosition(0);
        } catch (BadLocationException bl) {
            p = null;
        }
        return p;
    }
    
    public final Position getEndPosition() {
        Position p;
        try {
            p = createPosition(data.length());
        } catch (BadLocationException bl) {
            p = null;
        }
        return p;
    }
    
    public Element[] getRootElements() {
        Element[] elems = new Element[2];
        elems[0] = getDefaultRootElement();
        elems[1] = getBidiRootElement();
        return elems;
    }
    
    public abstract Element getDefaultRootElement();
    
    private DocumentFilter$FilterBypass getFilterBypass() {
        if (filterBypass == null) {
            filterBypass = new AbstractDocument$DefaultFilterBypass(this, null);
        }
        return filterBypass;
    }
    
    public Element getBidiRootElement() {
        return bidiRoot;
    }
    
    boolean isLeftToRight(int p0, int p1) {
        if (!getProperty(I18NProperty).equals(Boolean.TRUE)) {
            return true;
        }
        Element bidiRoot = getBidiRootElement();
        int index = bidiRoot.getElementIndex(p0);
        Element bidiElem = bidiRoot.getElement(index);
        if (bidiElem.getEndOffset() >= p1) {
            AttributeSet bidiAttrs = bidiElem.getAttributes();
            return ((StyleConstants.getBidiLevel(bidiAttrs) % 2) == 0);
        }
        return true;
    }
    
    public abstract Element getParagraphElement(int pos);
    
    protected final AbstractDocument$AttributeContext getAttributeContext() {
        return context;
    }
    
    protected void insertUpdate(AbstractDocument$DefaultDocumentEvent chng, AttributeSet attr) {
        if (getProperty(I18NProperty).equals(Boolean.TRUE)) updateBidi(chng);
        if (AbstractDocument.DefaultDocumentEvent.access$100(chng) == DocumentEvent$EventType.INSERT && chng.getLength() > 0 && !Boolean.TRUE.equals(getProperty(MultiByteProperty))) {
            Segment segment = SegmentCache.getSharedSegment();
            try {
                getText(chng.getOffset(), chng.getLength(), segment);
                segment.first();
                do {
                    if ((int)segment.current() > 255) {
                        putProperty(MultiByteProperty, Boolean.TRUE);
                        break;
                    }
                }                 while (segment.next() != Segment.DONE);
            } catch (BadLocationException ble) {
            }
            SegmentCache.releaseSharedSegment(segment);
        }
    }
    
    protected void removeUpdate(AbstractDocument$DefaultDocumentEvent chng) {
    }
    
    protected void postRemoveUpdate(AbstractDocument$DefaultDocumentEvent chng) {
        if (getProperty(I18NProperty).equals(Boolean.TRUE)) updateBidi(chng);
    }
    
    void updateBidi(AbstractDocument$DefaultDocumentEvent chng) {
        int firstPStart;
        int lastPEnd;
        if (AbstractDocument.DefaultDocumentEvent.access$100(chng) == DocumentEvent$EventType.INSERT || AbstractDocument.DefaultDocumentEvent.access$100(chng) == DocumentEvent$EventType.CHANGE) {
            int chngStart = chng.getOffset();
            int chngEnd = chngStart + chng.getLength();
            firstPStart = getParagraphElement(chngStart).getStartOffset();
            lastPEnd = getParagraphElement(chngEnd).getEndOffset();
        } else if (AbstractDocument.DefaultDocumentEvent.access$100(chng) == DocumentEvent$EventType.REMOVE) {
            Element paragraph = getParagraphElement(chng.getOffset());
            firstPStart = paragraph.getStartOffset();
            lastPEnd = paragraph.getEndOffset();
        } else {
            throw new Error("Internal error: unknown event type.");
        }
        byte[] levels = calculateBidiLevels(firstPStart, lastPEnd);
        Vector newElements = new Vector();
        int firstSpanStart = firstPStart;
        int removeFromIndex = 0;
        if (firstSpanStart > 0) {
            int prevElemIndex = bidiRoot.getElementIndex(firstPStart - 1);
            removeFromIndex = prevElemIndex;
            Element prevElem = bidiRoot.getElement(prevElemIndex);
            int prevLevel = StyleConstants.getBidiLevel(prevElem.getAttributes());
            if (prevLevel == levels[0]) {
                firstSpanStart = prevElem.getStartOffset();
            } else if (prevElem.getEndOffset() > firstPStart) {
                newElements.addElement(new AbstractDocument$BidiElement(this, bidiRoot, prevElem.getStartOffset(), firstPStart, prevLevel));
            } else {
                removeFromIndex++;
            }
        }
        int firstSpanEnd = 0;
        while ((firstSpanEnd < levels.length) && (levels[firstSpanEnd] == levels[0])) firstSpanEnd++;
        int lastSpanEnd = lastPEnd;
        Element newNextElem = null;
        int removeToIndex = bidiRoot.getElementCount() - 1;
        if (lastSpanEnd <= getLength()) {
            int nextElemIndex = bidiRoot.getElementIndex(lastPEnd);
            removeToIndex = nextElemIndex;
            Element nextElem = bidiRoot.getElement(nextElemIndex);
            int nextLevel = StyleConstants.getBidiLevel(nextElem.getAttributes());
            if (nextLevel == levels[levels.length - 1]) {
                lastSpanEnd = nextElem.getEndOffset();
            } else if (nextElem.getStartOffset() < lastPEnd) {
                newNextElem = new AbstractDocument$BidiElement(this, bidiRoot, lastPEnd, nextElem.getEndOffset(), nextLevel);
            } else {
                removeToIndex--;
            }
        }
        int lastSpanStart = levels.length;
        while ((lastSpanStart > firstSpanEnd) && (levels[lastSpanStart - 1] == levels[levels.length - 1])) lastSpanStart--;
        if ((firstSpanEnd == lastSpanStart) && (levels[0] == levels[levels.length - 1])) {
            newElements.addElement(new AbstractDocument$BidiElement(this, bidiRoot, firstSpanStart, lastSpanEnd, levels[0]));
        } else {
            newElements.addElement(new AbstractDocument$BidiElement(this, bidiRoot, firstSpanStart, firstSpanEnd + firstPStart, levels[0]));
            for (int i = firstSpanEnd; i < lastSpanStart; ) {
                int j;
                for (j = i; (j < levels.length) && (levels[j] == levels[i]); j++) ;
                newElements.addElement(new AbstractDocument$BidiElement(this, bidiRoot, firstPStart + i, firstPStart + j, (int)levels[i]));
                i = j;
            }
            newElements.addElement(new AbstractDocument$BidiElement(this, bidiRoot, lastSpanStart + firstPStart, lastSpanEnd, levels[levels.length - 1]));
        }
        if (newNextElem != null) newElements.addElement(newNextElem);
        int removedElemCount = 0;
        if (bidiRoot.getElementCount() > 0) {
            removedElemCount = removeToIndex - removeFromIndex + 1;
        }
        Element[] removedElems = new Element[removedElemCount];
        for (int i = 0; i < removedElemCount; i++) {
            removedElems[i] = bidiRoot.getElement(removeFromIndex + i);
        }
        Element[] addedElems = new Element[newElements.size()];
        newElements.copyInto(addedElems);
        AbstractDocument$ElementEdit ee = new AbstractDocument$ElementEdit(bidiRoot, removeFromIndex, removedElems, addedElems);
        chng.addEdit(ee);
        bidiRoot.replace(removeFromIndex, removedElems.length, addedElems);
    }
    
    private byte[] calculateBidiLevels(int firstPStart, int lastPEnd) {
        byte[] levels = new byte[lastPEnd - firstPStart];
        int levelsEnd = 0;
        Boolean defaultDirection = null;
        Object d = getProperty(TextAttribute.RUN_DIRECTION);
        if (d instanceof Boolean) {
            defaultDirection = (Boolean)(Boolean)d;
        }
        for (int o = firstPStart; o < lastPEnd; ) {
            Element p = getParagraphElement(o);
            int pStart = p.getStartOffset();
            int pEnd = p.getEndOffset();
            Boolean direction = defaultDirection;
            d = p.getAttributes().getAttribute(TextAttribute.RUN_DIRECTION);
            if (d instanceof Boolean) {
                direction = (Boolean)(Boolean)d;
            }
            Segment seg = SegmentCache.getSharedSegment();
            try {
                getText(pStart, pEnd - pStart, seg);
            } catch (BadLocationException e) {
                throw new Error("Internal error: " + e.toString());
            }
            Bidi bidiAnalyzer;
            int bidiflag = Bidi.DIRECTION_DEFAULT_LEFT_TO_RIGHT;
            if (direction != null) {
                if (TextAttribute.RUN_DIRECTION_LTR.equals(direction)) {
                    bidiflag = Bidi.DIRECTION_LEFT_TO_RIGHT;
                } else {
                    bidiflag = Bidi.DIRECTION_RIGHT_TO_LEFT;
                }
            }
            bidiAnalyzer = new Bidi(seg.array, seg.offset, null, 0, seg.count, bidiflag);
            BidiUtils.getLevels(bidiAnalyzer, levels, levelsEnd);
            levelsEnd += bidiAnalyzer.getLength();
            o = p.getEndOffset();
            SegmentCache.releaseSharedSegment(seg);
        }
        if (levelsEnd != levels.length) throw new Error("levelsEnd assertion failed.");
        return levels;
    }
    
    public void dump(PrintStream out) {
        Element root = getDefaultRootElement();
        if (root instanceof AbstractDocument$AbstractElement) {
            ((AbstractDocument$AbstractElement)(AbstractDocument$AbstractElement)root).dump(out, 0);
        }
        bidiRoot.dump(out, 0);
    }
    
    protected final AbstractDocument$Content getContent() {
        return data;
    }
    
    protected Element createLeafElement(Element parent, AttributeSet a, int p0, int p1) {
        return new AbstractDocument$LeafElement(this, parent, a, p0, p1);
    }
    
    protected Element createBranchElement(Element parent, AttributeSet a) {
        return new AbstractDocument$BranchElement(this, parent, a);
    }
    
    protected final synchronized Thread getCurrentWriter() {
        return currWriter;
    }
    
    protected final synchronized void writeLock() {
        try {
            while ((numReaders > 0) || (currWriter != null)) {
                if (Thread.currentThread() == currWriter) {
                    if (notifyingListeners) {
                        throw new IllegalStateException("Attempt to mutate in notification");
                    }
                    numWriters++;
                    return;
                }
                wait();
            }
            currWriter = Thread.currentThread();
            numWriters = 1;
        } catch (InterruptedException e) {
            throw new Error("Interrupted attempt to aquire write lock");
        }
    }
    
    protected final synchronized void writeUnlock() {
        if (--numWriters <= 0) {
            numWriters = 0;
            currWriter = null;
            notifyAll();
        }
    }
    
    public final synchronized void readLock() {
        try {
            while (currWriter != null) {
                if (currWriter == Thread.currentThread()) {
                    return;
                }
                wait();
            }
            numReaders += 1;
        } catch (InterruptedException e) {
            throw new Error("Interrupted attempt to aquire read lock");
        }
    }
    
    public final synchronized void readUnlock() {
        if (currWriter == Thread.currentThread()) {
            return;
        }
        if (numReaders <= 0) {
            throw new StateInvariantError(BAD_LOCK_STATE);
        }
        numReaders -= 1;
        notify();
    }
    
    private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException {
        s.defaultReadObject();
        listenerList = new EventListenerList();
        bidiRoot = new AbstractDocument$BidiRootElement(this);
        try {
            writeLock();
            Element[] p = new Element[1];
            p[0] = new AbstractDocument$BidiElement(this, bidiRoot, 0, 1, 0);
            bidiRoot.replace(0, 0, p);
        } finally {
            writeUnlock();
        }
        s.registerValidation(new AbstractDocument$2(this), 0);
    }
    private transient int numReaders;
    private transient Thread currWriter;
    private transient int numWriters;
    private transient boolean notifyingListeners;
    private static Boolean defaultI18NProperty;
    private Dictionary documentProperties = null;
    protected EventListenerList listenerList = new EventListenerList();
    private AbstractDocument$Content data;
    private AbstractDocument$AttributeContext context;
    private transient AbstractDocument$BranchElement bidiRoot;
    private DocumentFilter documentFilter;
    private transient DocumentFilter$FilterBypass filterBypass;
    private static final String BAD_LOCK_STATE = "document lock failure";
    protected static final String BAD_LOCATION = "document location failure";
    public static final String ParagraphElementName = "paragraph";
    public static final String ContentElementName = "content";
    public static final String SectionElementName = "section";
    public static final String BidiElementName = "bidi level";
    public static final String ElementNameAttribute = "$ename";
    static final String I18NProperty = "i18n";
    static final Object MultiByteProperty = "multiByte";
    static final String AsyncLoadPriority = "load priority";
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
    {
    }
    {
    }
    {
    }
}
