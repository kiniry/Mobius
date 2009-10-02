package javax.swing.text.html;

import javax.swing.text.*;
import java.io.Writer;
import java.util.Stack;
import java.util.Enumeration;
import java.util.Vector;
import java.io.IOException;

public class HTMLWriter extends AbstractWriter {
    private Stack blockElementStack = new Stack();
    private boolean inContent = false;
    private boolean inPre = false;
    private int preEndOffset;
    private boolean inTextArea = false;
    private boolean newlineOutputed = false;
    private boolean completeDoc;
    private Vector tags = new Vector(10);
    private Vector tagValues = new Vector(10);
    private Segment segment;
    private Vector tagsToRemove = new Vector(10);
    private boolean wroteHead;
    private boolean replaceEntities;
    private char[] tempChars;
    
    public HTMLWriter(Writer w, HTMLDocument doc) {
        this(w, doc, 0, doc.getLength());
    }
    
    public HTMLWriter(Writer w, HTMLDocument doc, int pos, int len) {
        super(w, doc, pos, len);
        completeDoc = (pos == 0 && len == doc.getLength());
        setLineLength(80);
    }
    
    public void write() throws IOException, BadLocationException {
        ElementIterator it = getElementIterator();
        Element current = null;
        Element next = null;
        wroteHead = false;
        setCurrentLineLength(0);
        replaceEntities = false;
        setCanWrapLines(false);
        if (segment == null) {
            segment = new Segment();
        }
        inPre = false;
        boolean forcedBody = false;
        while ((next = it.next()) != null) {
            if (!inRange(next)) {
                if (completeDoc && next.getAttributes().getAttribute(StyleConstants.NameAttribute) == HTML$Tag.BODY) {
                    forcedBody = true;
                } else {
                    continue;
                }
            }
            if (current != null) {
                if (indentNeedsIncrementing(current, next)) {
                    incrIndent();
                } else if (current.getParentElement() != next.getParentElement()) {
                    Element top = (Element)(Element)blockElementStack.peek();
                    while (top != next.getParentElement()) {
                        blockElementStack.pop();
                        if (!synthesizedElement(top)) {
                            AttributeSet attrs = top.getAttributes();
                            if (!matchNameAttribute(attrs, HTML$Tag.PRE) && !isFormElementWithContent(attrs)) {
                                decrIndent();
                            }
                            endTag(top);
                        }
                        top = (Element)(Element)blockElementStack.peek();
                    }
                } else if (current.getParentElement() == next.getParentElement()) {
                    Element top = (Element)(Element)blockElementStack.peek();
                    if (top == current) {
                        blockElementStack.pop();
                        endTag(top);
                    }
                }
            }
            if (!next.isLeaf() || isFormElementWithContent(next.getAttributes())) {
                blockElementStack.push(next);
                startTag(next);
            } else {
                emptyTag(next);
            }
            current = next;
        }
        closeOutUnwantedEmbeddedTags(null);
        if (forcedBody) {
            blockElementStack.pop();
            endTag(current);
        }
        while (!blockElementStack.empty()) {
            current = (Element)(Element)blockElementStack.pop();
            if (!synthesizedElement(current)) {
                AttributeSet attrs = current.getAttributes();
                if (!matchNameAttribute(attrs, HTML$Tag.PRE) && !isFormElementWithContent(attrs)) {
                    decrIndent();
                }
                endTag(current);
            }
        }
        if (completeDoc) {
            writeAdditionalComments();
        }
        segment.array = null;
    }
    
    protected void writeAttributes(AttributeSet attr) throws IOException {
        convAttr.removeAttributes(convAttr);
        convertToHTML32(attr, convAttr);
        Enumeration names = convAttr.getAttributeNames();
        while (names.hasMoreElements()) {
            Object name = names.nextElement();
            if (name instanceof HTML$Tag || name instanceof StyleConstants || name == HTML$Attribute.ENDTAG) {
                continue;
            }
            write(" " + name + "=\"" + convAttr.getAttribute(name) + "\"");
        }
    }
    
    protected void emptyTag(Element elem) throws BadLocationException, IOException {
        if (!inContent && !inPre) {
            indent();
        }
        AttributeSet attr = elem.getAttributes();
        closeOutUnwantedEmbeddedTags(attr);
        writeEmbeddedTags(attr);
        if (matchNameAttribute(attr, HTML$Tag.CONTENT)) {
            inContent = true;
            text(elem);
        } else if (matchNameAttribute(attr, HTML$Tag.COMMENT)) {
            comment(elem);
        } else {
            boolean isBlock = isBlockTag(elem.getAttributes());
            if (inContent && isBlock) {
                writeLineSeparator();
                indent();
            }
            Object nameTag = (attr != null) ? attr.getAttribute(StyleConstants.NameAttribute) : null;
            Object endTag = (attr != null) ? attr.getAttribute(HTML$Attribute.ENDTAG) : null;
            boolean outputEndTag = false;
            if (nameTag != null && endTag != null && (endTag instanceof String) && ((String)(String)endTag).equals("true")) {
                outputEndTag = true;
            }
            if (completeDoc && matchNameAttribute(attr, HTML$Tag.HEAD)) {
                if (outputEndTag) {
                    writeStyles(((HTMLDocument)(HTMLDocument)getDocument()).getStyleSheet());
                }
                wroteHead = true;
            }
            write('<');
            if (outputEndTag) {
                write('/');
            }
            write(elem.getName());
            writeAttributes(attr);
            write('>');
            if (matchNameAttribute(attr, HTML$Tag.TITLE) && !outputEndTag) {
                Document doc = elem.getDocument();
                String title = (String)(String)doc.getProperty(Document.TitleProperty);
                write(title);
            } else if (!inContent || isBlock) {
                writeLineSeparator();
                if (isBlock && inContent) {
                    indent();
                }
            }
        }
    }
    
    protected boolean isBlockTag(AttributeSet attr) {
        Object o = attr.getAttribute(StyleConstants.NameAttribute);
        if (o instanceof HTML$Tag) {
            HTML$Tag name = (HTML$Tag)(HTML$Tag)o;
            return name.isBlock();
        }
        return false;
    }
    
    protected void startTag(Element elem) throws IOException, BadLocationException {
        if (synthesizedElement(elem)) {
            return;
        }
        AttributeSet attr = elem.getAttributes();
        Object nameAttribute = attr.getAttribute(StyleConstants.NameAttribute);
        HTML$Tag name;
        if (nameAttribute instanceof HTML$Tag) {
            name = (HTML$Tag)(HTML$Tag)nameAttribute;
        } else {
            name = null;
        }
        if (name == HTML$Tag.PRE) {
            inPre = true;
            preEndOffset = elem.getEndOffset();
        }
        closeOutUnwantedEmbeddedTags(attr);
        if (inContent) {
            writeLineSeparator();
            inContent = false;
            newlineOutputed = false;
        }
        if (completeDoc && name == HTML$Tag.BODY && !wroteHead) {
            wroteHead = true;
            indent();
            write("<head>");
            writeLineSeparator();
            incrIndent();
            writeStyles(((HTMLDocument)(HTMLDocument)getDocument()).getStyleSheet());
            decrIndent();
            writeLineSeparator();
            indent();
            write("</head>");
            writeLineSeparator();
        }
        indent();
        write('<');
        write(elem.getName());
        writeAttributes(attr);
        write('>');
        if (name != HTML$Tag.PRE) {
            writeLineSeparator();
        }
        if (name == HTML$Tag.TEXTAREA) {
            textAreaContent(elem.getAttributes());
        } else if (name == HTML$Tag.SELECT) {
            selectContent(elem.getAttributes());
        } else if (completeDoc && name == HTML$Tag.BODY) {
            writeMaps(((HTMLDocument)(HTMLDocument)getDocument()).getMaps());
        } else if (name == HTML$Tag.HEAD) {
            wroteHead = true;
            incrIndent();
            writeStyles(((HTMLDocument)(HTMLDocument)getDocument()).getStyleSheet());
            decrIndent();
        }
        HTMLDocument document = null;
        if (name == HTML$Tag.BODY && (document = (HTMLDocument)(HTMLDocument)getDocument()).hasBaseTag()) {
            incrIndent();
            indent();
            write("<base href = \"" + document.getBase() + "\">");
            writeLineSeparator();
            decrIndent();
        }
    }
    
    protected void textAreaContent(AttributeSet attr) throws BadLocationException, IOException {
        Document doc = (Document)(Document)attr.getAttribute(StyleConstants.ModelAttribute);
        if (doc != null && doc.getLength() > 0) {
            if (segment == null) {
                segment = new Segment();
            }
            doc.getText(0, doc.getLength(), segment);
            if (segment.count > 0) {
                inTextArea = true;
                incrIndent();
                indent();
                setCanWrapLines(true);
                replaceEntities = true;
                write(segment.array, segment.offset, segment.count);
                replaceEntities = false;
                setCanWrapLines(false);
                writeLineSeparator();
                inTextArea = false;
                decrIndent();
            }
        }
    }
    
    protected void text(Element elem) throws BadLocationException, IOException {
        int start = Math.max(getStartOffset(), elem.getStartOffset());
        int end = Math.min(getEndOffset(), elem.getEndOffset());
        if (start < end) {
            if (segment == null) {
                segment = new Segment();
            }
            getDocument().getText(start, end - start, segment);
            newlineOutputed = false;
            if (segment.count > 0) {
                if (segment.array[segment.offset + segment.count - 1] == '\n') {
                    newlineOutputed = true;
                }
                if (inPre && end == preEndOffset) {
                    if (segment.count > 1) {
                        segment.count--;
                    } else {
                        return;
                    }
                }
                replaceEntities = true;
                setCanWrapLines(!inPre);
                write(segment.array, segment.offset, segment.count);
                setCanWrapLines(false);
                replaceEntities = false;
            }
        }
    }
    
    protected void selectContent(AttributeSet attr) throws IOException {
        Object model = attr.getAttribute(StyleConstants.ModelAttribute);
        incrIndent();
        if (model instanceof OptionListModel) {
            OptionListModel listModel = (OptionListModel)(OptionListModel)model;
            int size = listModel.getSize();
            for (int i = 0; i < size; i++) {
                Option option = (Option)(Option)listModel.getElementAt(i);
                writeOption(option);
            }
        } else if (model instanceof OptionComboBoxModel) {
            OptionComboBoxModel comboBoxModel = (OptionComboBoxModel)(OptionComboBoxModel)model;
            int size = comboBoxModel.getSize();
            for (int i = 0; i < size; i++) {
                Option option = (Option)(Option)comboBoxModel.getElementAt(i);
                writeOption(option);
            }
        }
        decrIndent();
    }
    
    protected void writeOption(Option option) throws IOException {
        indent();
        write('<');
        write("option");
        Object value = option.getAttributes().getAttribute(HTML$Attribute.VALUE);
        if (value != null) {
            write(" value=" + value);
        }
        if (option.isSelected()) {
            write(" selected");
        }
        write('>');
        if (option.getLabel() != null) {
            write(option.getLabel());
        }
        writeLineSeparator();
    }
    
    protected void endTag(Element elem) throws IOException {
        if (synthesizedElement(elem)) {
            return;
        }
        closeOutUnwantedEmbeddedTags(elem.getAttributes());
        if (inContent) {
            if (!newlineOutputed && !inPre) {
                writeLineSeparator();
            }
            newlineOutputed = false;
            inContent = false;
        }
        if (!inPre) {
            indent();
        }
        if (matchNameAttribute(elem.getAttributes(), HTML$Tag.PRE)) {
            inPre = false;
        }
        write('<');
        write('/');
        write(elem.getName());
        write('>');
        writeLineSeparator();
    }
    
    protected void comment(Element elem) throws BadLocationException, IOException {
        AttributeSet as = elem.getAttributes();
        if (matchNameAttribute(as, HTML$Tag.COMMENT)) {
            Object comment = as.getAttribute(HTML$Attribute.COMMENT);
            if (comment instanceof String) {
                writeComment((String)(String)comment);
            } else {
                writeComment(null);
            }
        }
    }
    
    void writeComment(String string) throws IOException {
        write("<!--");
        if (string != null) {
            write(string);
        }
        write("-->");
        writeLineSeparator();
    }
    
    void writeAdditionalComments() throws IOException {
        Object comments = getDocument().getProperty(HTMLDocument.AdditionalComments);
        if (comments instanceof Vector) {
            Vector v = (Vector)(Vector)comments;
            for (int counter = 0, maxCounter = v.size(); counter < maxCounter; counter++) {
                writeComment(v.elementAt(counter).toString());
            }
        }
    }
    
    protected boolean synthesizedElement(Element elem) {
        if (matchNameAttribute(elem.getAttributes(), HTML$Tag.IMPLIED)) {
            return true;
        }
        return false;
    }
    
    protected boolean matchNameAttribute(AttributeSet attr, HTML$Tag tag) {
        Object o = attr.getAttribute(StyleConstants.NameAttribute);
        if (o instanceof HTML$Tag) {
            HTML$Tag name = (HTML$Tag)(HTML$Tag)o;
            if (name == tag) {
                return true;
            }
        }
        return false;
    }
    
    protected void writeEmbeddedTags(AttributeSet attr) throws IOException {
        attr = convertToHTML(attr, oConvAttr);
        Enumeration names = attr.getAttributeNames();
        while (names.hasMoreElements()) {
            Object name = names.nextElement();
            if (name instanceof HTML$Tag) {
                HTML$Tag tag = (HTML$Tag)(HTML$Tag)name;
                if (tag == HTML$Tag.FORM || tags.contains(tag)) {
                    continue;
                }
                write('<');
                write(tag.toString());
                Object o = attr.getAttribute(tag);
                if (o != null && o instanceof AttributeSet) {
                    writeAttributes((AttributeSet)(AttributeSet)o);
                }
                write('>');
                tags.addElement(tag);
                tagValues.addElement(o);
            }
        }
    }
    
    private boolean noMatchForTagInAttributes(AttributeSet attr, HTML$Tag t, Object tagValue) {
        if (attr != null && attr.isDefined(t)) {
            Object newValue = attr.getAttribute(t);
            if ((tagValue == null) ? (newValue == null) : (newValue != null && tagValue.equals(newValue))) {
                return false;
            }
        }
        return true;
    }
    
    protected void closeOutUnwantedEmbeddedTags(AttributeSet attr) throws IOException {
        tagsToRemove.removeAllElements();
        attr = convertToHTML(attr, null);
        HTML$Tag t;
        Object tValue;
        int firstIndex = -1;
        int size = tags.size();
        for (int i = size - 1; i >= 0; i--) {
            t = (HTML$Tag)(HTML$Tag)tags.elementAt(i);
            tValue = tagValues.elementAt(i);
            if ((attr == null) || noMatchForTagInAttributes(attr, t, tValue)) {
                firstIndex = i;
                tagsToRemove.addElement(t);
            }
        }
        if (firstIndex != -1) {
            boolean removeAll = ((size - firstIndex) == tagsToRemove.size());
            for (int i = size - 1; i >= firstIndex; i--) {
                t = (HTML$Tag)(HTML$Tag)tags.elementAt(i);
                if (removeAll || tagsToRemove.contains(t)) {
                    tags.removeElementAt(i);
                    tagValues.removeElementAt(i);
                }
                write('<');
                write('/');
                write(t.toString());
                write('>');
            }
            size = tags.size();
            for (int i = firstIndex; i < size; i++) {
                t = (HTML$Tag)(HTML$Tag)tags.elementAt(i);
                write('<');
                write(t.toString());
                Object o = tagValues.elementAt(i);
                if (o != null && o instanceof AttributeSet) {
                    writeAttributes((AttributeSet)(AttributeSet)o);
                }
                write('>');
            }
        }
    }
    
    private boolean isFormElementWithContent(AttributeSet attr) {
        if (matchNameAttribute(attr, HTML$Tag.TEXTAREA) || matchNameAttribute(attr, HTML$Tag.SELECT)) {
            return true;
        }
        return false;
    }
    private boolean indentNext = false;
    
    private boolean indentNeedsIncrementing(Element current, Element next) {
        if ((next.getParentElement() == current) && !inPre) {
            if (indentNext) {
                indentNext = false;
                return true;
            } else if (synthesizedElement(next)) {
                indentNext = true;
            } else if (!synthesizedElement(current)) {
                return true;
            }
        }
        return false;
    }
    
    void writeMaps(Enumeration maps) throws IOException {
        if (maps != null) {
            while (maps.hasMoreElements()) {
                Map map = (Map)(Map)maps.nextElement();
                String name = map.getName();
                incrIndent();
                indent();
                write("<map");
                if (name != null) {
                    write(" name=\"");
                    write(name);
                    write("\">");
                } else {
                    write('>');
                }
                writeLineSeparator();
                incrIndent();
                AttributeSet[] areas = map.getAreas();
                if (areas != null) {
                    for (int counter = 0, maxCounter = areas.length; counter < maxCounter; counter++) {
                        indent();
                        write("<area");
                        writeAttributes(areas[counter]);
                        write("></area>");
                        writeLineSeparator();
                    }
                }
                decrIndent();
                indent();
                write("</map>");
                writeLineSeparator();
                decrIndent();
            }
        }
    }
    
    void writeStyles(StyleSheet sheet) throws IOException {
        if (sheet != null) {
            Enumeration styles = sheet.getStyleNames();
            if (styles != null) {
                boolean outputStyle = false;
                while (styles.hasMoreElements()) {
                    String name = (String)(String)styles.nextElement();
                    if (!StyleContext.DEFAULT_STYLE.equals(name) && writeStyle(name, sheet.getStyle(name), outputStyle)) {
                        outputStyle = true;
                    }
                }
                if (outputStyle) {
                    writeStyleEndTag();
                }
            }
        }
    }
    
    boolean writeStyle(String name, Style style, boolean outputStyle) throws IOException {
        boolean didOutputStyle = false;
        Enumeration attributes = style.getAttributeNames();
        if (attributes != null) {
            while (attributes.hasMoreElements()) {
                Object attribute = attributes.nextElement();
                if (attribute instanceof CSS$Attribute) {
                    String value = style.getAttribute(attribute).toString();
                    if (value != null) {
                        if (!outputStyle) {
                            writeStyleStartTag();
                            outputStyle = true;
                        }
                        if (!didOutputStyle) {
                            didOutputStyle = true;
                            indent();
                            write(name);
                            write(" {");
                        } else {
                            write(";");
                        }
                        write(' ');
                        write(attribute.toString());
                        write(": ");
                        write(value);
                    }
                }
            }
        }
        if (didOutputStyle) {
            write(" }");
            writeLineSeparator();
        }
        return didOutputStyle;
    }
    
    void writeStyleStartTag() throws IOException {
        indent();
        write("<style type=\"text/css\">");
        incrIndent();
        writeLineSeparator();
        indent();
        write("<!--");
        incrIndent();
        writeLineSeparator();
    }
    
    void writeStyleEndTag() throws IOException {
        decrIndent();
        indent();
        write("-->");
        writeLineSeparator();
        decrIndent();
        indent();
        write("</style>");
        writeLineSeparator();
        indent();
    }
    
    AttributeSet convertToHTML(AttributeSet from, MutableAttributeSet to) {
        if (to == null) {
            to = convAttr;
        }
        to.removeAttributes(to);
        if (writeCSS) {
            convertToHTML40(from, to);
        } else {
            convertToHTML32(from, to);
        }
        return to;
    }
    private boolean writeCSS = false;
    private MutableAttributeSet convAttr = new SimpleAttributeSet();
    private MutableAttributeSet oConvAttr = new SimpleAttributeSet();
    
    private static void convertToHTML32(AttributeSet from, MutableAttributeSet to) {
        if (from == null) {
            return;
        }
        Enumeration keys = from.getAttributeNames();
        String value = "";
        while (keys.hasMoreElements()) {
            Object key = keys.nextElement();
            if (key instanceof CSS$Attribute) {
                if ((key == CSS$Attribute.FONT_FAMILY) || (key == CSS$Attribute.FONT_SIZE) || (key == CSS$Attribute.COLOR)) {
                    createFontAttribute((CSS$Attribute)(CSS$Attribute)key, from, to);
                } else if (key == CSS$Attribute.FONT_WEIGHT) {
                    CSS$FontWeight weightValue = (CSS$FontWeight)(CSS$FontWeight)from.getAttribute(CSS$Attribute.FONT_WEIGHT);
                    if ((weightValue != null) && (weightValue.getValue() > 400)) {
                        addAttribute(to, HTML$Tag.B, SimpleAttributeSet.EMPTY);
                    }
                } else if (key == CSS$Attribute.FONT_STYLE) {
                    String s = from.getAttribute(key).toString();
                    if (s.indexOf("italic") >= 0) {
                        addAttribute(to, HTML$Tag.I, SimpleAttributeSet.EMPTY);
                    }
                } else if (key == CSS$Attribute.TEXT_DECORATION) {
                    String decor = from.getAttribute(key).toString();
                    if (decor.indexOf("underline") >= 0) {
                        addAttribute(to, HTML$Tag.U, SimpleAttributeSet.EMPTY);
                    }
                    if (decor.indexOf("line-through") >= 0) {
                        addAttribute(to, HTML$Tag.STRIKE, SimpleAttributeSet.EMPTY);
                    }
                } else if (key == CSS$Attribute.VERTICAL_ALIGN) {
                    String vAlign = from.getAttribute(key).toString();
                    if (vAlign.indexOf("sup") >= 0) {
                        addAttribute(to, HTML$Tag.SUP, SimpleAttributeSet.EMPTY);
                    }
                    if (vAlign.indexOf("sub") >= 0) {
                        addAttribute(to, HTML$Tag.SUB, SimpleAttributeSet.EMPTY);
                    }
                } else if (key == CSS$Attribute.TEXT_ALIGN) {
                    addAttribute(to, HTML$Attribute.ALIGN, from.getAttribute(key).toString());
                } else {
                    if (value.length() > 0) {
                        value = value + "; ";
                    }
                    value = value + key + ": " + from.getAttribute(key);
                }
            } else {
                Object attr = from.getAttribute(key);
                if (attr instanceof AttributeSet) {
                    attr = ((AttributeSet)(AttributeSet)attr).copyAttributes();
                }
                addAttribute(to, key, attr);
            }
        }
        if (value.length() > 0) {
            to.addAttribute(HTML$Attribute.STYLE, value);
        }
    }
    
    private static void addAttribute(MutableAttributeSet to, Object key, Object value) {
        Object attr = to.getAttribute(key);
        if (attr == null || attr == SimpleAttributeSet.EMPTY) {
            to.addAttribute(key, value);
        } else {
            if (attr instanceof MutableAttributeSet && value instanceof AttributeSet) {
                ((MutableAttributeSet)(MutableAttributeSet)attr).addAttributes((AttributeSet)(AttributeSet)value);
            }
        }
    }
    
    private static void createFontAttribute(CSS$Attribute a, AttributeSet from, MutableAttributeSet to) {
        MutableAttributeSet fontAttr = (MutableAttributeSet)(MutableAttributeSet)to.getAttribute(HTML$Tag.FONT);
        if (fontAttr == null) {
            fontAttr = new SimpleAttributeSet();
            to.addAttribute(HTML$Tag.FONT, fontAttr);
        }
        String htmlValue = from.getAttribute(a).toString();
        if (a == CSS$Attribute.FONT_FAMILY) {
            fontAttr.addAttribute(HTML$Attribute.FACE, htmlValue);
        } else if (a == CSS$Attribute.FONT_SIZE) {
            fontAttr.addAttribute(HTML$Attribute.SIZE, htmlValue);
        } else if (a == CSS$Attribute.COLOR) {
            fontAttr.addAttribute(HTML$Attribute.COLOR, htmlValue);
        }
    }
    
    private static void convertToHTML40(AttributeSet from, MutableAttributeSet to) {
        Enumeration keys = from.getAttributeNames();
        String value = "";
        while (keys.hasMoreElements()) {
            Object key = keys.nextElement();
            if (key instanceof CSS$Attribute) {
                value = value + " " + key + "=" + from.getAttribute(key) + ";";
            } else {
                to.addAttribute(key, from.getAttribute(key));
            }
        }
        if (value.length() > 0) {
            to.addAttribute(HTML$Attribute.STYLE, value);
        }
    }
    
    protected void writeLineSeparator() throws IOException {
        boolean oldReplace = replaceEntities;
        replaceEntities = false;
        super.writeLineSeparator();
        replaceEntities = oldReplace;
    }
    
    protected void output(char[] chars, int start, int length) throws IOException {
        if (!replaceEntities) {
            super.output(chars, start, length);
            return;
        }
        int last = start;
        length += start;
        for (int counter = start; counter < length; counter++) {
            switch (chars[counter]) {
            case '<': 
                if (counter > last) {
                    super.output(chars, last, counter - last);
                }
                last = counter + 1;
                output("&lt;");
                break;
            
            case '>': 
                if (counter > last) {
                    super.output(chars, last, counter - last);
                }
                last = counter + 1;
                output("&gt;");
                break;
            
            case '&': 
                if (counter > last) {
                    super.output(chars, last, counter - last);
                }
                last = counter + 1;
                output("&amp;");
                break;
            
            case '\"': 
                if (counter > last) {
                    super.output(chars, last, counter - last);
                }
                last = counter + 1;
                output("&quot;");
                break;
            
            case '\n': 
            
            case '\t': 
            
            case '\r': 
                break;
            
            default: 
                if (chars[counter] < ' ' || chars[counter] > 127) {
                    if (counter > last) {
                        super.output(chars, last, counter - last);
                    }
                    last = counter + 1;
                    output("&#");
                    output(String.valueOf((int)chars[counter]));
                    output(";");
                }
                break;
            
            }
        }
        if (last < length) {
            super.output(chars, last, length - last);
        }
    }
    
    private void output(String string) throws IOException {
        int length = string.length();
        if (tempChars == null || tempChars.length < length) {
            tempChars = new char[length];
        }
        string.getChars(0, length, tempChars, 0);
        super.output(tempChars, 0, length);
    }
}
