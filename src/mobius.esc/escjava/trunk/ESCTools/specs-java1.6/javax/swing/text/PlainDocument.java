package javax.swing.text;

import java.util.Vector;
import javax.swing.event.*;

public class PlainDocument extends AbstractDocument {
    public static final String tabSizeAttribute = "tabSize";
    public static final String lineLimitAttribute = "lineLimit";
    
    public PlainDocument() {
        this(new GapContent());
    }
    
    public PlainDocument(AbstractDocument$Content c) {
        super(c);
        putProperty(tabSizeAttribute, new Integer(8));
        defaultRoot = createDefaultRoot();
    }
    
    public void insertString(int offs, String str, AttributeSet a) throws BadLocationException {
        Object filterNewlines = getProperty("filterNewlines");
        if ((filterNewlines instanceof Boolean) && filterNewlines.equals(Boolean.TRUE)) {
            if ((str != null) && (str.indexOf('\n') >= 0)) {
                StringBuffer filtered = new StringBuffer(str);
                int n = filtered.length();
                for (int i = 0; i < n; i++) {
                    if (filtered.charAt(i) == '\n') {
                        filtered.setCharAt(i, ' ');
                    }
                }
                str = filtered.toString();
            }
        }
        super.insertString(offs, str, a);
    }
    
    public Element getDefaultRootElement() {
        return defaultRoot;
    }
    
    protected AbstractDocument$AbstractElement createDefaultRoot() {
        AbstractDocument$BranchElement map = (AbstractDocument$BranchElement)(AbstractDocument$BranchElement)createBranchElement(null, null);
        Element line = createLeafElement(map, null, 0, 1);
        Element[] lines = new Element[1];
        lines[0] = line;
        map.replace(0, 0, lines);
        return map;
    }
    
    public Element getParagraphElement(int pos) {
        Element lineMap = getDefaultRootElement();
        return lineMap.getElement(lineMap.getElementIndex(pos));
    }
    
    protected void insertUpdate(AbstractDocument$DefaultDocumentEvent chng, AttributeSet attr) {
        removed.removeAllElements();
        added.removeAllElements();
        AbstractDocument$BranchElement lineMap = (AbstractDocument$BranchElement)(AbstractDocument$BranchElement)getDefaultRootElement();
        int offset = chng.getOffset();
        int length = chng.getLength();
        if (offset > 0) {
            offset -= 1;
            length += 1;
        }
        int index = lineMap.getElementIndex(offset);
        Element rmCandidate = lineMap.getElement(index);
        int rmOffs0 = rmCandidate.getStartOffset();
        int rmOffs1 = rmCandidate.getEndOffset();
        int lastOffset = rmOffs0;
        try {
            if (s == null) {
                s = new Segment();
            }
            getContent().getChars(offset, length, s);
            boolean hasBreaks = false;
            for (int i = 0; i < length; i++) {
                char c = s.array[s.offset + i];
                if (c == '\n') {
                    int breakOffset = offset + i + 1;
                    added.addElement(createLeafElement(lineMap, null, lastOffset, breakOffset));
                    lastOffset = breakOffset;
                    hasBreaks = true;
                }
            }
            if (hasBreaks) {
                int rmCount = 1;
                removed.addElement(rmCandidate);
                if ((offset + length == rmOffs1) && (lastOffset != rmOffs1) && ((index + 1) < lineMap.getElementCount())) {
                    rmCount += 1;
                    Element e = lineMap.getElement(index + 1);
                    removed.addElement(e);
                    rmOffs1 = e.getEndOffset();
                }
                if (lastOffset < rmOffs1) {
                    added.addElement(createLeafElement(lineMap, null, lastOffset, rmOffs1));
                }
                Element[] aelems = new Element[added.size()];
                added.copyInto(aelems);
                Element[] relems = new Element[removed.size()];
                removed.copyInto(relems);
                AbstractDocument$ElementEdit ee = new AbstractDocument$ElementEdit(lineMap, index, relems, aelems);
                chng.addEdit(ee);
                lineMap.replace(index, relems.length, aelems);
            }
            if (Utilities.isComposedTextAttributeDefined(attr)) {
                insertComposedTextUpdate(chng, attr);
            }
        } catch (BadLocationException e) {
            throw new Error("Internal error: " + e.toString());
        }
        super.insertUpdate(chng, attr);
    }
    
    protected void removeUpdate(AbstractDocument$DefaultDocumentEvent chng) {
        removed.removeAllElements();
        AbstractDocument$BranchElement map = (AbstractDocument$BranchElement)(AbstractDocument$BranchElement)getDefaultRootElement();
        int offset = chng.getOffset();
        int length = chng.getLength();
        int line0 = map.getElementIndex(offset);
        int line1 = map.getElementIndex(offset + length);
        if (line0 != line1) {
            for (int i = line0; i <= line1; i++) {
                removed.addElement(map.getElement(i));
            }
            int p0 = map.getElement(line0).getStartOffset();
            int p1 = map.getElement(line1).getEndOffset();
            Element[] aelems = new Element[1];
            aelems[0] = createLeafElement(map, null, p0, p1);
            Element[] relems = new Element[removed.size()];
            removed.copyInto(relems);
            AbstractDocument$ElementEdit ee = new AbstractDocument$ElementEdit(map, line0, relems, aelems);
            chng.addEdit(ee);
            map.replace(line0, relems.length, aelems);
        } else {
            Element line = map.getElement(line0);
            if (!line.isLeaf()) {
                Element leaf = line.getElement(line.getElementIndex(offset));
                if (Utilities.isComposedTextElement(leaf)) {
                    Element[] aelem = new Element[1];
                    aelem[0] = createLeafElement(map, null, line.getStartOffset(), line.getEndOffset());
                    Element[] relem = new Element[1];
                    relem[0] = line;
                    AbstractDocument$ElementEdit ee = new AbstractDocument$ElementEdit(map, line0, relem, aelem);
                    chng.addEdit(ee);
                    map.replace(line0, 1, aelem);
                }
            }
        }
        super.removeUpdate(chng);
    }
    
    private void insertComposedTextUpdate(AbstractDocument$DefaultDocumentEvent chng, AttributeSet attr) {
        added.removeAllElements();
        AbstractDocument$BranchElement lineMap = (AbstractDocument$BranchElement)(AbstractDocument$BranchElement)getDefaultRootElement();
        int offset = chng.getOffset();
        int length = chng.getLength();
        int index = lineMap.getElementIndex(offset);
        Element elem = lineMap.getElement(index);
        int elemStart = elem.getStartOffset();
        int elemEnd = elem.getEndOffset();
        AbstractDocument$BranchElement[] abelem = new AbstractDocument$BranchElement[1];
        abelem[0] = (AbstractDocument$BranchElement)(AbstractDocument$BranchElement)createBranchElement(lineMap, null);
        Element[] relem = new Element[1];
        relem[0] = elem;
        if (elemStart != offset) added.addElement(createLeafElement(abelem[0], null, elemStart, offset));
        added.addElement(createLeafElement(abelem[0], attr, offset, offset + length));
        if (elemEnd != offset + length) added.addElement(createLeafElement(abelem[0], null, offset + length, elemEnd));
        Element[] alelem = new Element[added.size()];
        added.copyInto(alelem);
        AbstractDocument$ElementEdit ee = new AbstractDocument$ElementEdit(lineMap, index, relem, abelem);
        chng.addEdit(ee);
        abelem[0].replace(0, 0, alelem);
        lineMap.replace(index, 1, abelem);
    }
    private AbstractDocument$AbstractElement defaultRoot;
    private Vector added = new Vector();
    private Vector removed = new Vector();
    private transient Segment s;
}
