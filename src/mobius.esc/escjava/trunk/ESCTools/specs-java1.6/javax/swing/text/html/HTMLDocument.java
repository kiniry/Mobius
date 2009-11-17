package javax.swing.text.html;

import java.util.*;
import java.net.URL;
import java.io.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.swing.undo.*;

public class HTMLDocument extends DefaultStyledDocument {
    
    /*synthetic*/ static String access$1002(HTMLDocument x0, String x1) {
        return x0.baseTarget = x1;
    }
    
    /*synthetic*/ static HashMap access$702(HTMLDocument x0, HashMap x1) {
        return x0.radioButtonGroupsMap = x1;
    }
    
    /*synthetic*/ static HashMap access$700(HTMLDocument x0) {
        return x0.radioButtonGroupsMap;
    }
    
    /*synthetic*/ static boolean access$600(char[] x0, int x1, int x2) {
        return isComplex(x0, x1, x2);
    }
    
    /*synthetic*/ static void access$500(HTMLDocument x0, DocumentEvent x1) {
        x0.fireRemoveUpdate(x1);
    }
    
    /*synthetic*/ static void access$400(HTMLDocument x0, AbstractDocument$DefaultDocumentEvent x1) {
        x0.postRemoveUpdate(x1);
    }
    
    /*synthetic*/ static AbstractDocument$Content access$300(HTMLDocument x0) {
        return x0.getContent();
    }
    
    /*synthetic*/ static void access$200(HTMLDocument x0, AbstractDocument$DefaultDocumentEvent x1) {
        x0.removeUpdate(x1);
    }
    
    /*synthetic*/ static char[] access$100() {
        return NEWLINE;
    }
    {
    }
    
    public HTMLDocument() {
        this(new GapContent(BUFFER_SIZE_DEFAULT), new StyleSheet());
    }
    
    public HTMLDocument(StyleSheet styles) {
        this(new GapContent(BUFFER_SIZE_DEFAULT), styles);
    }
    
    public HTMLDocument(AbstractDocument$Content c, StyleSheet styles) {
        super(c, styles);
    }
    
    public HTMLEditorKit$ParserCallback getReader(int pos) {
        Object desc = getProperty(Document.StreamDescriptionProperty);
        if (desc instanceof URL) {
            setBase((URL)(URL)desc);
        }
        HTMLDocument$HTMLReader reader = new HTMLDocument$HTMLReader(this, pos);
        return reader;
    }
    
    public HTMLEditorKit$ParserCallback getReader(int pos, int popDepth, int pushDepth, HTML$Tag insertTag) {
        return getReader(pos, popDepth, pushDepth, insertTag, true);
    }
    
    HTMLEditorKit$ParserCallback getReader(int pos, int popDepth, int pushDepth, HTML$Tag insertTag, boolean insertInsertTag) {
        Object desc = getProperty(Document.StreamDescriptionProperty);
        if (desc instanceof URL) {
            setBase((URL)(URL)desc);
        }
        HTMLDocument$HTMLReader reader = new HTMLDocument$HTMLReader(this, pos, popDepth, pushDepth, insertTag, insertInsertTag, false, true);
        return reader;
    }
    
    public URL getBase() {
        return base;
    }
    
    public void setBase(URL u) {
        base = u;
        getStyleSheet().setBase(u);
    }
    
    protected void insert(int offset, DefaultStyledDocument$ElementSpec[] data) throws BadLocationException {
        super.insert(offset, data);
    }
    
    protected void insertUpdate(AbstractDocument$DefaultDocumentEvent chng, AttributeSet attr) {
        if (attr == null) {
            attr = contentAttributeSet;
        } else if (attr.isDefined(StyleConstants.ComposedTextAttribute)) {
            ((MutableAttributeSet)(MutableAttributeSet)attr).addAttributes(contentAttributeSet);
        }
        if (attr.isDefined(IMPLIED_CR)) {
            ((MutableAttributeSet)(MutableAttributeSet)attr).removeAttribute(IMPLIED_CR);
        }
        super.insertUpdate(chng, attr);
    }
    
    protected void create(DefaultStyledDocument$ElementSpec[] data) {
        super.create(data);
    }
    
    public void setParagraphAttributes(int offset, int length, AttributeSet s, boolean replace) {
        try {
            writeLock();
            int end = Math.min(offset + length, getLength());
            Element e = getParagraphElement(offset);
            offset = e.getStartOffset();
            e = getParagraphElement(end);
            length = Math.max(0, e.getEndOffset() - offset);
            AbstractDocument$DefaultDocumentEvent changes = new AbstractDocument$DefaultDocumentEvent(this, offset, length, DocumentEvent$EventType.CHANGE);
            AttributeSet sCopy = s.copyAttributes();
            int lastEnd = Integer.MAX_VALUE;
            for (int pos = offset; pos <= end; pos = lastEnd) {
                Element paragraph = getParagraphElement(pos);
                if (lastEnd == paragraph.getEndOffset()) {
                    lastEnd++;
                } else {
                    lastEnd = paragraph.getEndOffset();
                }
                MutableAttributeSet attr = (MutableAttributeSet)(MutableAttributeSet)paragraph.getAttributes();
                changes.addEdit(new DefaultStyledDocument$AttributeUndoableEdit(paragraph, sCopy, replace));
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
    
    public StyleSheet getStyleSheet() {
        return (StyleSheet)(StyleSheet)getAttributeContext();
    }
    
    public HTMLDocument$Iterator getIterator(HTML$Tag t) {
        if (t.isBlock()) {
            return null;
        }
        return new HTMLDocument$LeafIterator(t, this);
    }
    
    protected Element createLeafElement(Element parent, AttributeSet a, int p0, int p1) {
        return new HTMLDocument$RunElement(this, parent, a, p0, p1);
    }
    
    protected Element createBranchElement(Element parent, AttributeSet a) {
        return new HTMLDocument$BlockElement(this, parent, a);
    }
    
    protected AbstractDocument$AbstractElement createDefaultRoot() {
        writeLock();
        MutableAttributeSet a = new SimpleAttributeSet();
        a.addAttribute(StyleConstants.NameAttribute, HTML$Tag.HTML);
        HTMLDocument$BlockElement html = new HTMLDocument$BlockElement(this, null, a.copyAttributes());
        a.removeAttributes(a);
        a.addAttribute(StyleConstants.NameAttribute, HTML$Tag.BODY);
        HTMLDocument$BlockElement body = new HTMLDocument$BlockElement(this, html, a.copyAttributes());
        a.removeAttributes(a);
        a.addAttribute(StyleConstants.NameAttribute, HTML$Tag.P);
        getStyleSheet().addCSSAttributeFromHTML(a, CSS$Attribute.MARGIN_TOP, "0");
        HTMLDocument$BlockElement paragraph = new HTMLDocument$BlockElement(this, body, a.copyAttributes());
        a.removeAttributes(a);
        a.addAttribute(StyleConstants.NameAttribute, HTML$Tag.CONTENT);
        HTMLDocument$RunElement brk = new HTMLDocument$RunElement(this, paragraph, a, 0, 1);
        Element[] buff = new Element[1];
        buff[0] = brk;
        paragraph.replace(0, 0, buff);
        buff[0] = paragraph;
        body.replace(0, 0, buff);
        buff[0] = body;
        html.replace(0, 0, buff);
        writeUnlock();
        return html;
    }
    
    public void setTokenThreshold(int n) {
        putProperty(TokenThreshold, new Integer(n));
    }
    
    public int getTokenThreshold() {
        Integer i = (Integer)(Integer)getProperty(TokenThreshold);
        if (i != null) {
            return i.intValue();
        }
        return Integer.MAX_VALUE;
    }
    
    public void setPreservesUnknownTags(boolean preservesTags) {
        preservesUnknownTags = preservesTags;
    }
    
    public boolean getPreservesUnknownTags() {
        return preservesUnknownTags;
    }
    
    public void processHTMLFrameHyperlinkEvent(HTMLFrameHyperlinkEvent e) {
        String frameName = e.getTarget();
        Element element = e.getSourceElement();
        String urlStr = e.getURL().toString();
        if (frameName.equals("_self")) {
            updateFrame(element, urlStr);
        } else if (frameName.equals("_parent")) {
            updateFrameSet(element.getParentElement(), urlStr);
        } else {
            Element targetElement = findFrame(frameName);
            if (targetElement != null) {
                updateFrame(targetElement, urlStr);
            }
        }
    }
    
    private Element findFrame(String frameName) {
        ElementIterator it = new ElementIterator(this);
        Element next = null;
        while ((next = it.next()) != null) {
            AttributeSet attr = next.getAttributes();
            if (matchNameAttribute(attr, HTML$Tag.FRAME)) {
                String frameTarget = (String)(String)attr.getAttribute(HTML$Attribute.NAME);
                if (frameTarget != null && frameTarget.equals(frameName)) {
                    break;
                }
            }
        }
        return next;
    }
    
    static boolean matchNameAttribute(AttributeSet attr, HTML$Tag tag) {
        Object o = attr.getAttribute(StyleConstants.NameAttribute);
        if (o instanceof HTML$Tag) {
            HTML$Tag name = (HTML$Tag)(HTML$Tag)o;
            if (name == tag) {
                return true;
            }
        }
        return false;
    }
    
    private void updateFrameSet(Element element, String url) {
        try {
            int startOffset = element.getStartOffset();
            int endOffset = Math.min(getLength(), element.getEndOffset());
            String html = "<frame";
            if (url != null) {
                html += " src=\"" + url + "\"";
            }
            html += ">";
            installParserIfNecessary();
            setOuterHTML(element, html);
        } catch (BadLocationException e1) {
        } catch (IOException ioe) {
        }
    }
    
    private void updateFrame(Element element, String url) {
        try {
            writeLock();
            AbstractDocument$DefaultDocumentEvent changes = new AbstractDocument$DefaultDocumentEvent(this, element.getStartOffset(), 1, DocumentEvent$EventType.CHANGE);
            AttributeSet sCopy = element.getAttributes().copyAttributes();
            MutableAttributeSet attr = (MutableAttributeSet)(MutableAttributeSet)element.getAttributes();
            changes.addEdit(new DefaultStyledDocument$AttributeUndoableEdit(element, sCopy, false));
            attr.removeAttribute(HTML$Attribute.SRC);
            attr.addAttribute(HTML$Attribute.SRC, url);
            changes.end();
            fireChangedUpdate(changes);
            fireUndoableEditUpdate(new UndoableEditEvent(this, changes));
        } finally {
            writeUnlock();
        }
    }
    
    boolean isFrameDocument() {
        return frameDocument;
    }
    
    void setFrameDocumentState(boolean frameDoc) {
        this.frameDocument = frameDoc;
    }
    
    void addMap(Map map) {
        String name = map.getName();
        if (name != null) {
            Object maps = getProperty(MAP_PROPERTY);
            if (maps == null) {
                maps = new Hashtable(11);
                putProperty(MAP_PROPERTY, maps);
            }
            if (maps instanceof Hashtable) {
                ((Hashtable)(Hashtable)maps).put("#" + name, map);
            }
        }
    }
    
    void removeMap(Map map) {
        String name = map.getName();
        if (name != null) {
            Object maps = getProperty(MAP_PROPERTY);
            if (maps instanceof Hashtable) {
                ((Hashtable)(Hashtable)maps).remove("#" + name);
            }
        }
    }
    
    Map getMap(String name) {
        if (name != null) {
            Object maps = getProperty(MAP_PROPERTY);
            if (maps != null && (maps instanceof Hashtable)) {
                return (Map)(Map)((Hashtable)(Hashtable)maps).get(name);
            }
        }
        return null;
    }
    
    Enumeration getMaps() {
        Object maps = getProperty(MAP_PROPERTY);
        if (maps instanceof Hashtable) {
            return ((Hashtable)(Hashtable)maps).elements();
        }
        return null;
    }
    
    void setDefaultStyleSheetType(String contentType) {
        putProperty(StyleType, contentType);
    }
    
    String getDefaultStyleSheetType() {
        String retValue = (String)(String)getProperty(StyleType);
        if (retValue == null) {
            return "text/css";
        }
        return retValue;
    }
    
    public void setParser(HTMLEditorKit$Parser parser) {
        this.parser = parser;
        putProperty("__PARSER__", null);
    }
    
    public HTMLEditorKit$Parser getParser() {
        Object p = getProperty("__PARSER__");
        if (p instanceof HTMLEditorKit$Parser) {
            return (HTMLEditorKit$Parser)(HTMLEditorKit$Parser)p;
        }
        return parser;
    }
    
    public void setInnerHTML(Element elem, String htmlText) throws BadLocationException, IOException {
        verifyParser();
        if (elem != null && elem.isLeaf()) {
            throw new IllegalArgumentException("Can not set inner HTML of a leaf");
        }
        if (elem != null && htmlText != null) {
            int oldCount = elem.getElementCount();
            int insertPosition = elem.getStartOffset();
            insertHTML(elem, elem.getStartOffset(), htmlText, true);
            if (elem.getElementCount() > oldCount) {
                removeElements(elem, elem.getElementCount() - oldCount, oldCount);
            }
        }
    }
    
    public void setOuterHTML(Element elem, String htmlText) throws BadLocationException, IOException {
        verifyParser();
        if (elem != null && elem.getParentElement() != null && htmlText != null) {
            int start = elem.getStartOffset();
            int end = elem.getEndOffset();
            int startLength = getLength();
            boolean wantsNewline = !elem.isLeaf();
            if (!wantsNewline && (end > startLength || getText(end - 1, 1).charAt(0) == NEWLINE[0])) {
                wantsNewline = true;
            }
            Element parent = elem.getParentElement();
            int oldCount = parent.getElementCount();
            insertHTML(parent, start, htmlText, wantsNewline);
            int newLength = getLength();
            if (oldCount != parent.getElementCount()) {
                int removeIndex = parent.getElementIndex(start + newLength - startLength);
                removeElements(parent, removeIndex, 1);
            }
        }
    }
    
    public void insertAfterStart(Element elem, String htmlText) throws BadLocationException, IOException {
        verifyParser();
        if (elem != null && elem.isLeaf()) {
            throw new IllegalArgumentException("Can not insert HTML after start of a leaf");
        }
        insertHTML(elem, elem.getStartOffset(), htmlText, false);
    }
    
    public void insertBeforeEnd(Element elem, String htmlText) throws BadLocationException, IOException {
        verifyParser();
        if (elem != null && elem.isLeaf()) {
            throw new IllegalArgumentException("Can not set inner HTML before end of leaf");
        }
        int offset = elem.getEndOffset();
        if (elem.getElement(elem.getElementIndex(offset - 1)).isLeaf() && getText(offset - 1, 1).charAt(0) == NEWLINE[0]) {
            offset--;
        }
        insertHTML(elem, offset, htmlText, false);
    }
    
    public void insertBeforeStart(Element elem, String htmlText) throws BadLocationException, IOException {
        verifyParser();
        if (elem != null) {
            Element parent = elem.getParentElement();
            if (parent != null) {
                insertHTML(parent, elem.getStartOffset(), htmlText, false);
            }
        }
    }
    
    public void insertAfterEnd(Element elem, String htmlText) throws BadLocationException, IOException {
        verifyParser();
        if (elem != null) {
            Element parent = elem.getParentElement();
            if (parent != null) {
                int offset = elem.getEndOffset();
                if (offset > getLength()) {
                    offset--;
                } else if (elem.isLeaf() && getText(offset - 1, 1).charAt(0) == NEWLINE[0]) {
                    offset--;
                }
                insertHTML(parent, offset, htmlText, false);
            }
        }
    }
    
    public Element getElement(String id) {
        if (id == null) {
            return null;
        }
        return getElement(getDefaultRootElement(), HTML$Attribute.ID, id, true);
    }
    
    public Element getElement(Element e, Object attribute, Object value) {
        return getElement(e, attribute, value, true);
    }
    
    private Element getElement(Element e, Object attribute, Object value, boolean searchLeafAttributes) {
        AttributeSet attr = e.getAttributes();
        if (attr != null && attr.isDefined(attribute)) {
            if (value.equals(attr.getAttribute(attribute))) {
                return e;
            }
        }
        if (!e.isLeaf()) {
            for (int counter = 0, maxCounter = e.getElementCount(); counter < maxCounter; counter++) {
                Element retValue = getElement(e.getElement(counter), attribute, value, searchLeafAttributes);
                if (retValue != null) {
                    return retValue;
                }
            }
        } else if (searchLeafAttributes && attr != null) {
            Enumeration names = attr.getAttributeNames();
            if (names != null) {
                while (names.hasMoreElements()) {
                    Object name = names.nextElement();
                    if ((name instanceof HTML$Tag) && (attr.getAttribute(name) instanceof AttributeSet)) {
                        AttributeSet check = (AttributeSet)(AttributeSet)attr.getAttribute(name);
                        if (check.isDefined(attribute) && value.equals(check.getAttribute(attribute))) {
                            return e;
                        }
                    }
                }
            }
        }
        return null;
    }
    
    private void verifyParser() {
        if (getParser() == null) {
            throw new IllegalStateException("No HTMLEditorKit.Parser");
        }
    }
    
    private void installParserIfNecessary() {
        if (getParser() == null) {
            setParser(new HTMLEditorKit().getParser());
        }
    }
    
    private void insertHTML(Element parent, int offset, String html, boolean wantsTrailingNewline) throws BadLocationException, IOException {
        if (parent != null && html != null) {
            HTMLEditorKit$Parser parser = getParser();
            if (parser != null) {
                int lastOffset = Math.max(0, offset - 1);
                Element charElement = getCharacterElement(lastOffset);
                Element commonParent = parent;
                int pop = 0;
                int push = 0;
                if (parent.getStartOffset() > lastOffset) {
                    while (commonParent != null && commonParent.getStartOffset() > lastOffset) {
                        commonParent = commonParent.getParentElement();
                        push++;
                    }
                    if (commonParent == null) {
                        throw new BadLocationException("No common parent", offset);
                    }
                }
                while (charElement != null && charElement != commonParent) {
                    pop++;
                    charElement = charElement.getParentElement();
                }
                if (charElement != null) {
                    HTMLDocument$HTMLReader reader = new HTMLDocument$HTMLReader(this, offset, pop - 1, push, null, false, true, wantsTrailingNewline);
                    parser.parse(new StringReader(html), reader, true);
                    reader.flush();
                }
            }
        }
    }
    
    private void removeElements(Element e, int index, int count) throws BadLocationException {
        writeLock();
        try {
            int start = e.getElement(index).getStartOffset();
            int end = e.getElement(index + count - 1).getEndOffset();
            if (end > getLength()) {
                removeElementsAtEnd(e, index, count, start, end);
            } else {
                removeElements(e, index, count, start, end);
            }
        } finally {
            writeUnlock();
        }
    }
    
    private void removeElementsAtEnd(Element e, int index, int count, int start, int end) throws BadLocationException {
        boolean isLeaf = (e.getElement(index - 1).isLeaf());
        AbstractDocument$DefaultDocumentEvent dde = new AbstractDocument$DefaultDocumentEvent(this, start - 1, end - start + 1, DocumentEvent$EventType.REMOVE);
        if (isLeaf) {
            Element endE = getCharacterElement(getLength());
            index--;
            if (endE.getParentElement() != e) {
                replace(dde, e, index, ++count, start, end, true, true);
            } else {
                replace(dde, e, index, count, start, end, true, false);
            }
        } else {
            Element newLineE = e.getElement(index - 1);
            while (!newLineE.isLeaf()) {
                newLineE = newLineE.getElement(newLineE.getElementCount() - 1);
            }
            newLineE = newLineE.getParentElement();
            replace(dde, e, index, count, start, end, false, false);
            replace(dde, newLineE, newLineE.getElementCount() - 1, 1, start, end, true, true);
        }
        postRemoveUpdate(dde);
        dde.end();
        fireRemoveUpdate(dde);
        fireUndoableEditUpdate(new UndoableEditEvent(this, dde));
    }
    
    private void replace(AbstractDocument$DefaultDocumentEvent dde, Element e, int index, int count, int start, int end, boolean remove, boolean create) throws BadLocationException {
        Element[] added;
        AttributeSet attrs = e.getElement(index).getAttributes();
        Element[] removed = new Element[count];
        for (int counter = 0; counter < count; counter++) {
            removed[counter] = e.getElement(counter + index);
        }
        if (remove) {
            UndoableEdit u = getContent().remove(start - 1, end - start);
            if (u != null) {
                dde.addEdit(u);
            }
        }
        if (create) {
            added = new Element[1];
            added[0] = createLeafElement(e, attrs, start - 1, start);
        } else {
            added = new Element[0];
        }
        dde.addEdit(new AbstractDocument$ElementEdit(e, index, removed, added));
        ((AbstractDocument$BranchElement)(AbstractDocument$BranchElement)e).replace(index, removed.length, added);
    }
    
    private void removeElements(Element e, int index, int count, int start, int end) throws BadLocationException {
        Element[] removed = new Element[count];
        Element[] added = new Element[0];
        for (int counter = 0; counter < count; counter++) {
            removed[counter] = e.getElement(counter + index);
        }
        AbstractDocument$DefaultDocumentEvent dde = new AbstractDocument$DefaultDocumentEvent(this, start, end - start, DocumentEvent$EventType.REMOVE);
        ((AbstractDocument$BranchElement)(AbstractDocument$BranchElement)e).replace(index, removed.length, added);
        dde.addEdit(new AbstractDocument$ElementEdit(e, index, removed, added));
        UndoableEdit u = getContent().remove(start, end - start);
        if (u != null) {
            dde.addEdit(u);
        }
        postRemoveUpdate(dde);
        dde.end();
        fireRemoveUpdate(dde);
        if (u != null) {
            fireUndoableEditUpdate(new UndoableEditEvent(this, dde));
        }
    }
    
    void obtainLock() {
        writeLock();
    }
    
    void releaseLock() {
        writeUnlock();
    }
    
    protected void fireChangedUpdate(DocumentEvent e) {
        super.fireChangedUpdate(e);
    }
    
    protected void fireUndoableEditUpdate(UndoableEditEvent e) {
        super.fireUndoableEditUpdate(e);
    }
    
    boolean hasBaseTag() {
        return hasBaseTag;
    }
    
    String getBaseTarget() {
        return baseTarget;
    }
    private boolean frameDocument = false;
    private boolean preservesUnknownTags = true;
    private HashMap radioButtonGroupsMap;
    static final String TokenThreshold = "token threshold";
    private static final int MaxThreshold = 10000;
    private static final int StepThreshold = 5;
    public static final String AdditionalComments = "AdditionalComments";
    static final String StyleType = "StyleType";
    URL base;
    boolean hasBaseTag = false;
    private String baseTarget = null;
    private HTMLEditorKit$Parser parser;
    private static AttributeSet contentAttributeSet;
    static String MAP_PROPERTY = "__MAP__";
    private static char[] NEWLINE;
    private static final String IMPLIED_CR = "CR";
    private static final String I18NProperty = "i18n";
    
    private static final boolean isComplex(char ch) {
        return (ch >= '\u0900' && ch <= '\u0d7f') || (ch >= '\u0e00' && ch <= '\u0e7f');
    }
    
    private static final boolean isComplex(char[] text, int start, int limit) {
        for (int i = start; i < limit; ++i) {
            if (isComplex(text[i])) {
                return true;
            }
        }
        return false;
    }
    static {
        contentAttributeSet = new SimpleAttributeSet();
        ((MutableAttributeSet)(MutableAttributeSet)contentAttributeSet).addAttribute(StyleConstants.NameAttribute, HTML$Tag.CONTENT);
        NEWLINE = new char[1];
        NEWLINE[0] = '\n';
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
