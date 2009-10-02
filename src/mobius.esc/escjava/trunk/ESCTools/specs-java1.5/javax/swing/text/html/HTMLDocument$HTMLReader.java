package javax.swing.text.html;

import java.awt.font.TextAttribute;
import java.util.*;
import java.net.URL;
import java.net.MalformedURLException;
import java.io.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.swing.undo.*;
import java.text.Bidi;

public class HTMLDocument$HTMLReader extends HTMLEditorKit$ParserCallback {
    
    /*synthetic*/ static boolean access$900(HTMLDocument$HTMLReader x0, HTML$Tag x1, AttributeSet x2, boolean x3) {
        return x0.canInsertTag(x1, x2, x3);
    }
    
    /*synthetic*/ static boolean access$800(HTMLDocument$HTMLReader x0) {
        return x0.insertAfterImplied;
    }
    /*synthetic*/ final HTMLDocument this$0;
    
    public HTMLDocument$HTMLReader(/*synthetic*/ final HTMLDocument this$0, int offset) {
        this(this$0, offset, 0, 0, null);
    }
    
    public HTMLDocument$HTMLReader(/*synthetic*/ final HTMLDocument this$0, int offset, int popDepth, int pushDepth, HTML$Tag insertTag) {
        this(this$0, offset, popDepth, pushDepth, insertTag, true, false, true);
    }
    
    HTMLDocument$HTMLReader(/*synthetic*/ final HTMLDocument this$0, int offset, int popDepth, int pushDepth, HTML$Tag insertTag, boolean insertInsertTag, boolean insertAfterImplied, boolean wantsTrailingNewline) {
        this.this$0 = this$0;
        
        emptyDocument = (this$0.getLength() == 0);
        isStyleCSS = "text/css".equals(this$0.getDefaultStyleSheetType());
        this.offset = offset;
        threshold = this$0.getTokenThreshold();
        tagMap = new Hashtable(57);
        HTMLDocument$HTMLReader$TagAction na = new HTMLDocument$HTMLReader$TagAction(this);
        HTMLDocument$HTMLReader$TagAction ba = new HTMLDocument$HTMLReader$BlockAction(this);
        HTMLDocument$HTMLReader$TagAction pa = new HTMLDocument$HTMLReader$ParagraphAction(this);
        HTMLDocument$HTMLReader$TagAction ca = new HTMLDocument$HTMLReader$CharacterAction(this);
        HTMLDocument$HTMLReader$TagAction sa = new HTMLDocument$HTMLReader$SpecialAction(this);
        HTMLDocument$HTMLReader$TagAction fa = new HTMLDocument$HTMLReader$FormAction(this);
        HTMLDocument$HTMLReader$TagAction ha = new HTMLDocument$HTMLReader$HiddenAction(this);
        HTMLDocument$HTMLReader$TagAction conv = new HTMLDocument$HTMLReader$ConvertAction(this);
        tagMap.put(HTML$Tag.A, new HTMLDocument$HTMLReader$AnchorAction(this));
        tagMap.put(HTML$Tag.ADDRESS, ca);
        tagMap.put(HTML$Tag.APPLET, ha);
        tagMap.put(HTML$Tag.AREA, new HTMLDocument$HTMLReader$AreaAction(this));
        tagMap.put(HTML$Tag.B, conv);
        tagMap.put(HTML$Tag.BASE, new HTMLDocument$HTMLReader$BaseAction(this));
        tagMap.put(HTML$Tag.BASEFONT, ca);
        tagMap.put(HTML$Tag.BIG, ca);
        tagMap.put(HTML$Tag.BLOCKQUOTE, ba);
        tagMap.put(HTML$Tag.BODY, ba);
        tagMap.put(HTML$Tag.BR, sa);
        tagMap.put(HTML$Tag.CAPTION, ba);
        tagMap.put(HTML$Tag.CENTER, ba);
        tagMap.put(HTML$Tag.CITE, ca);
        tagMap.put(HTML$Tag.CODE, ca);
        tagMap.put(HTML$Tag.DD, ba);
        tagMap.put(HTML$Tag.DFN, ca);
        tagMap.put(HTML$Tag.DIR, ba);
        tagMap.put(HTML$Tag.DIV, ba);
        tagMap.put(HTML$Tag.DL, ba);
        tagMap.put(HTML$Tag.DT, pa);
        tagMap.put(HTML$Tag.EM, ca);
        tagMap.put(HTML$Tag.FONT, conv);
        tagMap.put(HTML$Tag.FORM, new HTMLDocument$HTMLReader$FormTagAction(this, null));
        tagMap.put(HTML$Tag.FRAME, sa);
        tagMap.put(HTML$Tag.FRAMESET, ba);
        tagMap.put(HTML$Tag.H1, pa);
        tagMap.put(HTML$Tag.H2, pa);
        tagMap.put(HTML$Tag.H3, pa);
        tagMap.put(HTML$Tag.H4, pa);
        tagMap.put(HTML$Tag.H5, pa);
        tagMap.put(HTML$Tag.H6, pa);
        tagMap.put(HTML$Tag.HEAD, new HTMLDocument$HTMLReader$HeadAction(this));
        tagMap.put(HTML$Tag.HR, sa);
        tagMap.put(HTML$Tag.HTML, ba);
        tagMap.put(HTML$Tag.I, conv);
        tagMap.put(HTML$Tag.IMG, sa);
        tagMap.put(HTML$Tag.INPUT, fa);
        tagMap.put(HTML$Tag.ISINDEX, new HTMLDocument$HTMLReader$IsindexAction(this));
        tagMap.put(HTML$Tag.KBD, ca);
        tagMap.put(HTML$Tag.LI, ba);
        tagMap.put(HTML$Tag.LINK, new HTMLDocument$HTMLReader$LinkAction(this));
        tagMap.put(HTML$Tag.MAP, new HTMLDocument$HTMLReader$MapAction(this));
        tagMap.put(HTML$Tag.MENU, ba);
        tagMap.put(HTML$Tag.META, new HTMLDocument$HTMLReader$MetaAction(this));
        tagMap.put(HTML$Tag.NOBR, ca);
        tagMap.put(HTML$Tag.NOFRAMES, ba);
        tagMap.put(HTML$Tag.OBJECT, sa);
        tagMap.put(HTML$Tag.OL, ba);
        tagMap.put(HTML$Tag.OPTION, fa);
        tagMap.put(HTML$Tag.P, pa);
        tagMap.put(HTML$Tag.PARAM, new HTMLDocument$HTMLReader$ObjectAction(this));
        tagMap.put(HTML$Tag.PRE, new HTMLDocument$HTMLReader$PreAction(this));
        tagMap.put(HTML$Tag.SAMP, ca);
        tagMap.put(HTML$Tag.SCRIPT, ha);
        tagMap.put(HTML$Tag.SELECT, fa);
        tagMap.put(HTML$Tag.SMALL, ca);
        tagMap.put(HTML$Tag.SPAN, ca);
        tagMap.put(HTML$Tag.STRIKE, conv);
        tagMap.put(HTML$Tag.S, ca);
        tagMap.put(HTML$Tag.STRONG, ca);
        tagMap.put(HTML$Tag.STYLE, new HTMLDocument$HTMLReader$StyleAction(this));
        tagMap.put(HTML$Tag.SUB, conv);
        tagMap.put(HTML$Tag.SUP, conv);
        tagMap.put(HTML$Tag.TABLE, ba);
        tagMap.put(HTML$Tag.TD, ba);
        tagMap.put(HTML$Tag.TEXTAREA, fa);
        tagMap.put(HTML$Tag.TH, ba);
        tagMap.put(HTML$Tag.TITLE, new HTMLDocument$HTMLReader$TitleAction(this));
        tagMap.put(HTML$Tag.TR, ba);
        tagMap.put(HTML$Tag.TT, ca);
        tagMap.put(HTML$Tag.U, conv);
        tagMap.put(HTML$Tag.UL, ba);
        tagMap.put(HTML$Tag.VAR, ca);
        if (insertTag != null) {
            this.insertTag = insertTag;
            this.popDepth = popDepth;
            this.pushDepth = pushDepth;
            this.insertInsertTag = insertInsertTag;
            foundInsertTag = false;
        } else {
            foundInsertTag = true;
        }
        if (insertAfterImplied) {
            this.popDepth = popDepth;
            this.pushDepth = pushDepth;
            this.insertAfterImplied = true;
            foundInsertTag = false;
            midInsert = false;
            this.insertInsertTag = true;
            this.wantsTrailingNewline = wantsTrailingNewline;
        } else {
            midInsert = (!emptyDocument && insertTag == null);
            if (midInsert) {
                generateEndsSpecsForMidInsert();
            }
        }
    }
    
    private void generateEndsSpecsForMidInsert() {
        int count = heightToElementWithName(HTML$Tag.BODY, Math.max(0, offset - 1));
        boolean joinNext = false;
        if (count == -1 && offset > 0) {
            count = heightToElementWithName(HTML$Tag.BODY, offset);
            if (count != -1) {
                count = depthTo(offset - 1) - 1;
                joinNext = true;
            }
        }
        if (count == -1) {
            throw new RuntimeException("Must insert new content into body element-");
        }
        if (count != -1) {
            try {
                if (!joinNext && offset > 0 && !this$0.getText(offset - 1, 1).equals("\n")) {
                    SimpleAttributeSet newAttrs = new SimpleAttributeSet();
                    newAttrs.addAttribute(StyleConstants.NameAttribute, HTML$Tag.CONTENT);
                    DefaultStyledDocument$ElementSpec spec = new DefaultStyledDocument$ElementSpec(newAttrs, DefaultStyledDocument$ElementSpec.ContentType, HTMLDocument.access$100(), 0, 1);
                    parseBuffer.addElement(spec);
                }
            } catch (BadLocationException ble) {
            }
            while (count-- > 0) {
                parseBuffer.addElement(new DefaultStyledDocument$ElementSpec(null, DefaultStyledDocument$ElementSpec.EndTagType));
            }
            if (joinNext) {
                DefaultStyledDocument$ElementSpec spec = new DefaultStyledDocument$ElementSpec(null, DefaultStyledDocument$ElementSpec.StartTagType);
                spec.setDirection(DefaultStyledDocument$ElementSpec.JoinNextDirection);
                parseBuffer.addElement(spec);
            }
        }
    }
    
    private int depthTo(int offset) {
        Element e = this$0.getDefaultRootElement();
        int count = 0;
        while (!e.isLeaf()) {
            count++;
            e = e.getElement(e.getElementIndex(offset));
        }
        return count;
    }
    
    private int heightToElementWithName(Object name, int offset) {
        Element e = this$0.getCharacterElement(offset).getParentElement();
        int count = 0;
        while (e != null && e.getAttributes().getAttribute(StyleConstants.NameAttribute) != name) {
            count++;
            e = e.getParentElement();
        }
        return (e == null) ? -1 : count;
    }
    
    private void adjustEndElement() {
        int length = this$0.getLength();
        if (length == 0) {
            return;
        }
        this$0.obtainLock();
        try {
            Element[] pPath = getPathTo(length - 1);
            int pLength = pPath.length;
            if (pLength > 1 && pPath[1].getAttributes().getAttribute(StyleConstants.NameAttribute) == HTML$Tag.BODY && pPath[1].getEndOffset() == length) {
                String lastText = this$0.getText(length - 1, 1);
                AbstractDocument$DefaultDocumentEvent event = null;
                Element[] added;
                Element[] removed;
                int index;
                added = new Element[0];
                removed = new Element[1];
                index = pPath[0].getElementIndex(length);
                removed[0] = pPath[0].getElement(index);
                ((AbstractDocument$BranchElement)(AbstractDocument$BranchElement)pPath[0]).replace(index, 1, added);
                AbstractDocument$ElementEdit firstEdit = new AbstractDocument$ElementEdit(pPath[0], index, removed, added);
                SimpleAttributeSet sas = new SimpleAttributeSet();
                sas.addAttribute(StyleConstants.NameAttribute, HTML$Tag.CONTENT);
                sas.addAttribute("CR", Boolean.TRUE);
                added = new Element[1];
                added[0] = this$0.createLeafElement(pPath[pLength - 1], sas, length, length + 1);
                index = pPath[pLength - 1].getElementCount();
                ((AbstractDocument$BranchElement)(AbstractDocument$BranchElement)pPath[pLength - 1]).replace(index, 0, added);
                event = new AbstractDocument$DefaultDocumentEvent(this$0, length, 1, DocumentEvent$EventType.CHANGE);
                event.addEdit(new AbstractDocument$ElementEdit(pPath[pLength - 1], index, new Element[0], added));
                event.addEdit(firstEdit);
                event.end();
                this$0.fireChangedUpdate(event);
                this$0.fireUndoableEditUpdate(new UndoableEditEvent(this, event));
                if (lastText.equals("\n")) {
                    event = new AbstractDocument$DefaultDocumentEvent(this$0, length - 1, 1, DocumentEvent$EventType.REMOVE);
                    HTMLDocument.access$200(this$0, event);
                    UndoableEdit u = HTMLDocument.access$300(this$0).remove(length - 1, 1);
                    if (u != null) {
                        event.addEdit(u);
                    }
                    HTMLDocument.access$400(this$0, event);
                    event.end();
                    HTMLDocument.access$500(this$0, event);
                    this$0.fireUndoableEditUpdate(new UndoableEditEvent(this, event));
                }
            }
        } catch (BadLocationException ble) {
        } finally {
            this$0.releaseLock();
        }
    }
    
    private Element[] getPathTo(int offset) {
        Stack elements = new Stack();
        Element e = this$0.getDefaultRootElement();
        int index;
        while (!e.isLeaf()) {
            elements.push(e);
            e = e.getElement(e.getElementIndex(offset));
        }
        Element[] retValue = new Element[elements.size()];
        elements.copyInto(retValue);
        return retValue;
    }
    
    public void flush() throws BadLocationException {
        if (emptyDocument && !insertAfterImplied) {
            if (this$0.getLength() > 0 || parseBuffer.size() > 0) {
                flushBuffer(true);
                adjustEndElement();
            }
        } else {
            flushBuffer(true);
        }
    }
    
    public void handleText(char[] data, int pos) {
        if (receivedEndHTML || (midInsert && !inBody)) {
            return;
        }
        if (this$0.getProperty("i18n").equals(Boolean.FALSE)) {
            Object d = this$0.getProperty(TextAttribute.RUN_DIRECTION);
            if ((d != null) && (d.equals(TextAttribute.RUN_DIRECTION_RTL))) {
                this$0.putProperty("i18n", Boolean.TRUE);
            } else {
                if (Bidi.requiresBidi(data, 0, data.length) || HTMLDocument.access$600(data, 0, data.length)) {
                    this$0.putProperty("i18n", Boolean.TRUE);
                }
            }
        }
        if (inTextArea) {
            textAreaContent(data);
        } else if (inPre) {
            preContent(data);
        } else if (inTitle) {
            this$0.putProperty(Document.TitleProperty, new String(data));
        } else if (option != null) {
            option.setLabel(new String(data));
        } else if (inStyle) {
            if (styles != null) {
                styles.addElement(new String(data));
            }
        } else if (inBlock > 0) {
            if (!foundInsertTag && insertAfterImplied) {
                foundInsertTag(false);
                foundInsertTag = true;
                inParagraph = impliedP = true;
            }
            if (data.length >= 1) {
                addContent(data, 0, data.length);
            }
        }
    }
    
    public void handleStartTag(HTML$Tag t, MutableAttributeSet a, int pos) {
        if (receivedEndHTML) {
            return;
        }
        if (midInsert && !inBody) {
            if (t == HTML$Tag.BODY) {
                inBody = true;
                inBlock++;
            }
            return;
        }
        if (!inBody && t == HTML$Tag.BODY) {
            inBody = true;
        }
        if (isStyleCSS && a.isDefined(HTML$Attribute.STYLE)) {
            String decl = (String)(String)a.getAttribute(HTML$Attribute.STYLE);
            a.removeAttribute(HTML$Attribute.STYLE);
            styleAttributes = this$0.getStyleSheet().getDeclaration(decl);
            a.addAttributes(styleAttributes);
        } else {
            styleAttributes = null;
        }
        HTMLDocument$HTMLReader$TagAction action = (HTMLDocument$HTMLReader$TagAction)(HTMLDocument$HTMLReader$TagAction)tagMap.get(t);
        if (action != null) {
            action.start(t, a);
        }
    }
    
    public void handleComment(char[] data, int pos) {
        if (receivedEndHTML) {
            addExternalComment(new String(data));
            return;
        }
        if (inStyle) {
            if (styles != null) {
                styles.addElement(new String(data));
            }
        } else if (this$0.getPreservesUnknownTags()) {
            if (inBlock == 0 && (foundInsertTag || insertTag != HTML$Tag.COMMENT)) {
                addExternalComment(new String(data));
                return;
            }
            SimpleAttributeSet sas = new SimpleAttributeSet();
            sas.addAttribute(HTML$Attribute.COMMENT, new String(data));
            addSpecialElement(HTML$Tag.COMMENT, sas);
        }
        HTMLDocument$HTMLReader$TagAction action = (HTMLDocument$HTMLReader$TagAction)(HTMLDocument$HTMLReader$TagAction)tagMap.get(HTML$Tag.COMMENT);
        if (action != null) {
            action.start(HTML$Tag.COMMENT, new SimpleAttributeSet());
            action.end(HTML$Tag.COMMENT);
        }
    }
    
    private void addExternalComment(String comment) {
        Object comments = this$0.getProperty("AdditionalComments");
        if (comments != null && !(comments instanceof Vector)) {
            return;
        }
        if (comments == null) {
            comments = new Vector();
            this$0.putProperty("AdditionalComments", comments);
        }
        ((Vector)(Vector)comments).addElement(comment);
    }
    
    public void handleEndTag(HTML$Tag t, int pos) {
        if (receivedEndHTML || (midInsert && !inBody)) {
            return;
        }
        if (t == HTML$Tag.HTML) {
            receivedEndHTML = true;
        }
        if (t == HTML$Tag.BODY) {
            inBody = false;
            if (midInsert) {
                inBlock--;
            }
        }
        HTMLDocument$HTMLReader$TagAction action = (HTMLDocument$HTMLReader$TagAction)(HTMLDocument$HTMLReader$TagAction)tagMap.get(t);
        if (action != null) {
            action.end(t);
        }
    }
    
    public void handleSimpleTag(HTML$Tag t, MutableAttributeSet a, int pos) {
        if (receivedEndHTML || (midInsert && !inBody)) {
            return;
        }
        if (isStyleCSS && a.isDefined(HTML$Attribute.STYLE)) {
            String decl = (String)(String)a.getAttribute(HTML$Attribute.STYLE);
            a.removeAttribute(HTML$Attribute.STYLE);
            styleAttributes = this$0.getStyleSheet().getDeclaration(decl);
            a.addAttributes(styleAttributes);
        } else {
            styleAttributes = null;
        }
        HTMLDocument$HTMLReader$TagAction action = (HTMLDocument$HTMLReader$TagAction)(HTMLDocument$HTMLReader$TagAction)tagMap.get(t);
        if (action != null) {
            action.start(t, a);
            action.end(t);
        } else if (this$0.getPreservesUnknownTags()) {
            addSpecialElement(t, a);
        }
    }
    
    public void handleEndOfLineString(String eol) {
        if (emptyDocument && eol != null) {
            this$0.putProperty(DefaultEditorKit.EndOfLineStringProperty, eol);
        }
    }
    
    protected void registerTag(HTML$Tag t, HTMLDocument$HTMLReader$TagAction a) {
        tagMap.put(t, a);
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
    
    protected void pushCharacterStyle() {
        charAttrStack.push(charAttr.copyAttributes());
    }
    
    protected void popCharacterStyle() {
        if (!charAttrStack.empty()) {
            charAttr = (MutableAttributeSet)(MutableAttributeSet)charAttrStack.peek();
            charAttrStack.pop();
        }
    }
    
    protected void textAreaContent(char[] data) {
        try {
            textAreaDocument.insertString(textAreaDocument.getLength(), new String(data), null);
        } catch (BadLocationException e) {
        }
    }
    
    protected void preContent(char[] data) {
        int last = 0;
        for (int i = 0; i < data.length; i++) {
            if (data[i] == '\n') {
                addContent(data, last, i - last + 1);
                blockClose(HTML$Tag.IMPLIED);
                MutableAttributeSet a = new SimpleAttributeSet();
                a.addAttribute(CSS$Attribute.WHITE_SPACE, "pre");
                blockOpen(HTML$Tag.IMPLIED, a);
                last = i + 1;
            }
        }
        if (last < data.length) {
            addContent(data, last, data.length - last);
        }
    }
    
    protected void blockOpen(HTML$Tag t, MutableAttributeSet attr) {
        if (impliedP) {
            blockClose(HTML$Tag.IMPLIED);
        }
        inBlock++;
        if (!canInsertTag(t, attr, true)) {
            return;
        }
        if (attr.isDefined(IMPLIED)) {
            attr.removeAttribute(IMPLIED);
        }
        lastWasNewline = false;
        attr.addAttribute(StyleConstants.NameAttribute, t);
        DefaultStyledDocument$ElementSpec es = new DefaultStyledDocument$ElementSpec(attr.copyAttributes(), DefaultStyledDocument$ElementSpec.StartTagType);
        parseBuffer.addElement(es);
    }
    
    protected void blockClose(HTML$Tag t) {
        inBlock--;
        if (!foundInsertTag) {
            return;
        }
        if (!lastWasNewline) {
            pushCharacterStyle();
            charAttr.addAttribute("CR", Boolean.TRUE);
            addContent(HTMLDocument.access$100(), 0, 1, true);
            popCharacterStyle();
            lastWasNewline = true;
        }
        if (impliedP) {
            impliedP = false;
            inParagraph = false;
            if (t != HTML$Tag.IMPLIED) {
                blockClose(HTML$Tag.IMPLIED);
            }
        }
        DefaultStyledDocument$ElementSpec prev = (parseBuffer.size() > 0) ? (DefaultStyledDocument$ElementSpec)(DefaultStyledDocument$ElementSpec)parseBuffer.lastElement() : null;
        if (prev != null && prev.getType() == DefaultStyledDocument$ElementSpec.StartTagType) {
            char[] one = new char[1];
            one[0] = ' ';
            addContent(one, 0, 1);
        }
        DefaultStyledDocument$ElementSpec es = new DefaultStyledDocument$ElementSpec(null, DefaultStyledDocument$ElementSpec.EndTagType);
        parseBuffer.addElement(es);
    }
    
    protected void addContent(char[] data, int offs, int length) {
        addContent(data, offs, length, true);
    }
    
    protected void addContent(char[] data, int offs, int length, boolean generateImpliedPIfNecessary) {
        if (!foundInsertTag) {
            return;
        }
        if (generateImpliedPIfNecessary && (!inParagraph) && (!inPre)) {
            blockOpen(HTML$Tag.IMPLIED, new SimpleAttributeSet());
            inParagraph = true;
            impliedP = true;
        }
        emptyAnchor = false;
        charAttr.addAttribute(StyleConstants.NameAttribute, HTML$Tag.CONTENT);
        AttributeSet a = charAttr.copyAttributes();
        DefaultStyledDocument$ElementSpec es = new DefaultStyledDocument$ElementSpec(a, DefaultStyledDocument$ElementSpec.ContentType, data, offs, length);
        parseBuffer.addElement(es);
        if (parseBuffer.size() > threshold) {
            if (threshold <= 10000) {
                threshold *= 5;
            }
            try {
                flushBuffer(false);
            } catch (BadLocationException ble) {
            }
        }
        if (length > 0) {
            lastWasNewline = (data[offs + length - 1] == '\n');
        }
    }
    
    protected void addSpecialElement(HTML$Tag t, MutableAttributeSet a) {
        if ((t != HTML$Tag.FRAME) && (!inParagraph) && (!inPre)) {
            blockOpen(HTML$Tag.IMPLIED, new SimpleAttributeSet());
            inParagraph = true;
            impliedP = true;
        }
        if (!canInsertTag(t, a, t.isBlock())) {
            return;
        }
        if (a.isDefined(IMPLIED)) {
            a.removeAttribute(IMPLIED);
        }
        emptyAnchor = false;
        a.addAttributes(charAttr);
        a.addAttribute(StyleConstants.NameAttribute, t);
        char[] one = new char[1];
        one[0] = ' ';
        DefaultStyledDocument$ElementSpec es = new DefaultStyledDocument$ElementSpec(a.copyAttributes(), DefaultStyledDocument$ElementSpec.ContentType, one, 0, 1);
        parseBuffer.addElement(es);
        if (t == HTML$Tag.FRAME) {
            lastWasNewline = true;
        }
    }
    
    void flushBuffer(boolean endOfStream) throws BadLocationException {
        int oldLength = this$0.getLength();
        int size = parseBuffer.size();
        if (endOfStream && (insertTag != null || insertAfterImplied) && size > 0) {
            adjustEndSpecsForPartialInsert();
            size = parseBuffer.size();
        }
        DefaultStyledDocument$ElementSpec[] spec = new DefaultStyledDocument$ElementSpec[size];
        parseBuffer.copyInto(spec);
        if (oldLength == 0 && (insertTag == null && !insertAfterImplied)) {
            this$0.create(spec);
        } else {
            this$0.insert(offset, spec);
        }
        parseBuffer.removeAllElements();
        offset += this$0.getLength() - oldLength;
        flushCount++;
    }
    
    private void adjustEndSpecsForPartialInsert() {
        int size = parseBuffer.size();
        if (insertTagDepthDelta < 0) {
            int removeCounter = insertTagDepthDelta;
            while (removeCounter < 0 && size >= 0 && ((DefaultStyledDocument$ElementSpec)(DefaultStyledDocument$ElementSpec)parseBuffer.elementAt(size - 1)).getType() == DefaultStyledDocument$ElementSpec.EndTagType) {
                parseBuffer.removeElementAt(--size);
                removeCounter++;
            }
        }
        if (flushCount == 0 && (!insertAfterImplied || !wantsTrailingNewline)) {
            int index = 0;
            if (pushDepth > 0) {
                if (((DefaultStyledDocument$ElementSpec)(DefaultStyledDocument$ElementSpec)parseBuffer.elementAt(0)).getType() == DefaultStyledDocument$ElementSpec.ContentType) {
                    index++;
                }
            }
            index += (popDepth + pushDepth);
            int cCount = 0;
            int cStart = index;
            while (index < size && ((DefaultStyledDocument$ElementSpec)(DefaultStyledDocument$ElementSpec)parseBuffer.elementAt(index)).getType() == DefaultStyledDocument$ElementSpec.ContentType) {
                index++;
                cCount++;
            }
            if (cCount > 1) {
                while (index < size && ((DefaultStyledDocument$ElementSpec)(DefaultStyledDocument$ElementSpec)parseBuffer.elementAt(index)).getType() == DefaultStyledDocument$ElementSpec.EndTagType) {
                    index++;
                }
                if (index == size) {
                    char[] lastText = ((DefaultStyledDocument$ElementSpec)(DefaultStyledDocument$ElementSpec)parseBuffer.elementAt(cStart + cCount - 1)).getArray();
                    if (lastText.length == 1 && lastText[0] == HTMLDocument.access$100()[0]) {
                        index = cStart + cCount - 1;
                        while (size > index) {
                            parseBuffer.removeElementAt(--size);
                        }
                    }
                }
            }
        }
        if (wantsTrailingNewline) {
            for (int counter = parseBuffer.size() - 1; counter >= 0; counter--) {
                DefaultStyledDocument$ElementSpec spec = (DefaultStyledDocument$ElementSpec)(DefaultStyledDocument$ElementSpec)parseBuffer.elementAt(counter);
                if (spec.getType() == DefaultStyledDocument$ElementSpec.ContentType) {
                    if (spec.getArray()[spec.getLength() - 1] != '\n') {
                        SimpleAttributeSet attrs = new SimpleAttributeSet();
                        attrs.addAttribute(StyleConstants.NameAttribute, HTML$Tag.CONTENT);
                        parseBuffer.insertElementAt(new DefaultStyledDocument$ElementSpec(attrs, DefaultStyledDocument$ElementSpec.ContentType, HTMLDocument.access$100(), 0, 1), counter + 1);
                    }
                    break;
                }
            }
        }
    }
    
    void addCSSRules(String rules) {
        StyleSheet ss = this$0.getStyleSheet();
        ss.addRule(rules);
    }
    
    void linkCSSStyleSheet(String href) {
        URL url = null;
        try {
            url = new URL(this$0.base, href);
        } catch (MalformedURLException mfe) {
            try {
                url = new URL(href);
            } catch (MalformedURLException mfe2) {
                url = null;
            }
        }
        if (url != null) {
            this$0.getStyleSheet().importStyleSheet(url);
        }
    }
    
    private boolean canInsertTag(HTML$Tag t, AttributeSet attr, boolean isBlockTag) {
        if (!foundInsertTag) {
            if ((insertTag != null && !isInsertTag(t)) || (insertAfterImplied && (t == HTML$Tag.IMPLIED || (attr == null || attr.isDefined(IMPLIED))))) {
                return false;
            }
            foundInsertTag(isBlockTag);
            if (!insertInsertTag) {
                return false;
            }
        }
        return true;
    }
    
    private boolean isInsertTag(HTML$Tag tag) {
        return (insertTag == tag);
    }
    
    private void foundInsertTag(boolean isBlockTag) {
        foundInsertTag = true;
        if (!insertAfterImplied && (popDepth > 0 || pushDepth > 0)) {
            try {
                if (offset == 0 || !this$0.getText(offset - 1, 1).equals("\n")) {
                    AttributeSet newAttrs = null;
                    boolean joinP = true;
                    if (offset != 0) {
                        Element charElement = this$0.getCharacterElement(offset - 1);
                        AttributeSet attrs = charElement.getAttributes();
                        if (attrs.isDefined(StyleConstants.ComposedTextAttribute)) {
                            joinP = false;
                        } else {
                            Object name = attrs.getAttribute(StyleConstants.NameAttribute);
                            if (name instanceof HTML$Tag) {
                                HTML$Tag tag = (HTML$Tag)(HTML$Tag)name;
                                if (tag == HTML$Tag.IMG || tag == HTML$Tag.HR || tag == HTML$Tag.COMMENT || (tag instanceof HTML$UnknownTag)) {
                                    joinP = false;
                                }
                            }
                        }
                    }
                    if (!joinP) {
                        newAttrs = new SimpleAttributeSet();
                        ((SimpleAttributeSet)(SimpleAttributeSet)newAttrs).addAttribute(StyleConstants.NameAttribute, HTML$Tag.CONTENT);
                    }
                    DefaultStyledDocument$ElementSpec es = new DefaultStyledDocument$ElementSpec(newAttrs, DefaultStyledDocument$ElementSpec.ContentType, HTMLDocument.access$100(), 0, HTMLDocument.access$100().length);
                    if (joinP) {
                        es.setDirection(DefaultStyledDocument$ElementSpec.JoinPreviousDirection);
                    }
                    parseBuffer.addElement(es);
                }
            } catch (BadLocationException ble) {
            }
        }
        for (int counter = 0; counter < popDepth; counter++) {
            parseBuffer.addElement(new DefaultStyledDocument$ElementSpec(null, DefaultStyledDocument$ElementSpec.EndTagType));
        }
        for (int counter = 0; counter < pushDepth; counter++) {
            DefaultStyledDocument$ElementSpec es = new DefaultStyledDocument$ElementSpec(null, DefaultStyledDocument$ElementSpec.StartTagType);
            es.setDirection(DefaultStyledDocument$ElementSpec.JoinNextDirection);
            parseBuffer.addElement(es);
        }
        insertTagDepthDelta = depthTo(Math.max(0, offset - 1)) - popDepth + pushDepth - inBlock;
        if (isBlockTag) {
            insertTagDepthDelta++;
        } else {
            insertTagDepthDelta--;
            inParagraph = true;
            lastWasNewline = false;
        }
    }
    private boolean receivedEndHTML;
    private int flushCount;
    private boolean insertAfterImplied;
    private boolean wantsTrailingNewline;
    int threshold;
    int offset;
    boolean inParagraph = false;
    boolean impliedP = false;
    boolean inPre = false;
    boolean inTextArea = false;
    TextAreaDocument textAreaDocument = null;
    boolean inTitle = false;
    boolean lastWasNewline = true;
    boolean emptyAnchor;
    boolean midInsert;
    boolean inBody;
    HTML$Tag insertTag;
    boolean insertInsertTag;
    boolean foundInsertTag;
    int insertTagDepthDelta;
    int popDepth;
    int pushDepth;
    Map lastMap;
    boolean inStyle = false;
    String defaultStyle;
    Vector styles;
    boolean inHead = false;
    boolean isStyleCSS;
    boolean emptyDocument;
    AttributeSet styleAttributes;
    Option option;
    protected Vector parseBuffer = new Vector();
    protected MutableAttributeSet charAttr = new HTMLDocument$TaggedAttributeSet();
    Stack charAttrStack = new Stack();
    Hashtable tagMap;
    int inBlock = 0;
}
