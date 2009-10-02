package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.text.*;
import javax.swing.Action;
import javax.swing.SwingConstants;

public class DefaultEditorKit extends EditorKit {
    
    public DefaultEditorKit() {
        
    }
    
    public String getContentType() {
        return "text/plain";
    }
    
    public ViewFactory getViewFactory() {
        return null;
    }
    
    public Action[] getActions() {
        return defaultActions;
    }
    
    public Caret createCaret() {
        return null;
    }
    
    public Document createDefaultDocument() {
        return new PlainDocument();
    }
    
    public void read(InputStream in, Document doc, int pos) throws IOException, BadLocationException {
        read(new InputStreamReader(in), doc, pos);
    }
    
    public void write(OutputStream out, Document doc, int pos, int len) throws IOException, BadLocationException {
        OutputStreamWriter osw = new OutputStreamWriter(out);
        write(osw, doc, pos, len);
        osw.flush();
    }
    
    MutableAttributeSet getInputAttributes() {
        return null;
    }
    
    public void read(Reader in, Document doc, int pos) throws IOException, BadLocationException {
        char[] buff = new char[4096];
        int nch;
        boolean lastWasCR = false;
        boolean isCRLF = false;
        boolean isCR = false;
        int last;
        boolean wasEmpty = (doc.getLength() == 0);
        AttributeSet attr = getInputAttributes();
        while ((nch = in.read(buff, 0, buff.length)) != -1) {
            last = 0;
            for (int counter = 0; counter < nch; counter++) {
                switch (buff[counter]) {
                case '\r': 
                    if (lastWasCR) {
                        isCR = true;
                        if (counter == 0) {
                            doc.insertString(pos, "\n", attr);
                            pos++;
                        } else {
                            buff[counter - 1] = '\n';
                        }
                    } else {
                        lastWasCR = true;
                    }
                    break;
                
                case '\n': 
                    if (lastWasCR) {
                        if (counter > (last + 1)) {
                            doc.insertString(pos, new String(buff, last, counter - last - 1), attr);
                            pos += (counter - last - 1);
                        }
                        lastWasCR = false;
                        last = counter;
                        isCRLF = true;
                    }
                    break;
                
                default: 
                    if (lastWasCR) {
                        isCR = true;
                        if (counter == 0) {
                            doc.insertString(pos, "\n", attr);
                            pos++;
                        } else {
                            buff[counter - 1] = '\n';
                        }
                        lastWasCR = false;
                    }
                    break;
                
                }
            }
            if (last < nch) {
                if (lastWasCR) {
                    if (last < (nch - 1)) {
                        doc.insertString(pos, new String(buff, last, nch - last - 1), attr);
                        pos += (nch - last - 1);
                    }
                } else {
                    doc.insertString(pos, new String(buff, last, nch - last), attr);
                    pos += (nch - last);
                }
            }
        }
        if (lastWasCR) {
            doc.insertString(pos, "\n", attr);
            isCR = true;
        }
        if (wasEmpty) {
            if (isCRLF) {
                doc.putProperty(EndOfLineStringProperty, "\r\n");
            } else if (isCR) {
                doc.putProperty(EndOfLineStringProperty, "\r");
            } else {
                doc.putProperty(EndOfLineStringProperty, "\n");
            }
        }
    }
    
    public void write(Writer out, Document doc, int pos, int len) throws IOException, BadLocationException {
        if ((pos < 0) || ((pos + len) > doc.getLength())) {
            throw new BadLocationException("DefaultEditorKit.write", pos);
        }
        Segment data = new Segment();
        int nleft = len;
        int offs = pos;
        Object endOfLineProperty = doc.getProperty(EndOfLineStringProperty);
        if (endOfLineProperty == null) {
            try {
                endOfLineProperty = System.getProperty("line.separator");
            } catch (SecurityException se) {
            }
        }
        String endOfLine;
        if (endOfLineProperty instanceof String) {
            endOfLine = (String)(String)endOfLineProperty;
        } else {
            endOfLine = null;
        }
        if (endOfLineProperty != null && !endOfLine.equals("\n")) {
            while (nleft > 0) {
                int n = Math.min(nleft, 4096);
                doc.getText(offs, n, data);
                int last = data.offset;
                char[] array = data.array;
                int maxCounter = last + data.count;
                for (int counter = last; counter < maxCounter; counter++) {
                    if (array[counter] == '\n') {
                        if (counter > last) {
                            out.write(array, last, counter - last);
                        }
                        out.write(endOfLine);
                        last = counter + 1;
                    }
                }
                if (maxCounter > last) {
                    out.write(array, last, maxCounter - last);
                }
                offs += n;
                nleft -= n;
            }
        } else {
            while (nleft > 0) {
                int n = Math.min(nleft, 4096);
                doc.getText(offs, n, data);
                out.write(data.array, data.offset, data.count);
                offs += n;
                nleft -= n;
            }
        }
        out.flush();
    }
    public static final String EndOfLineStringProperty = "__EndOfLine__";
    public static final String insertContentAction = "insert-content";
    public static final String insertBreakAction = "insert-break";
    public static final String insertTabAction = "insert-tab";
    public static final String deletePrevCharAction = "delete-previous";
    public static final String deleteNextCharAction = "delete-next";
    public static final String readOnlyAction = "set-read-only";
    public static final String writableAction = "set-writable";
    public static final String cutAction = "cut-to-clipboard";
    public static final String copyAction = "copy-to-clipboard";
    public static final String pasteAction = "paste-from-clipboard";
    public static final String beepAction = "beep";
    public static final String pageUpAction = "page-up";
    public static final String pageDownAction = "page-down";
    static final String selectionPageUpAction = "selection-page-up";
    static final String selectionPageDownAction = "selection-page-down";
    static final String selectionPageLeftAction = "selection-page-left";
    static final String selectionPageRightAction = "selection-page-right";
    public static final String forwardAction = "caret-forward";
    public static final String backwardAction = "caret-backward";
    public static final String selectionForwardAction = "selection-forward";
    public static final String selectionBackwardAction = "selection-backward";
    public static final String upAction = "caret-up";
    public static final String downAction = "caret-down";
    public static final String selectionUpAction = "selection-up";
    public static final String selectionDownAction = "selection-down";
    public static final String beginWordAction = "caret-begin-word";
    public static final String endWordAction = "caret-end-word";
    public static final String selectionBeginWordAction = "selection-begin-word";
    public static final String selectionEndWordAction = "selection-end-word";
    public static final String previousWordAction = "caret-previous-word";
    public static final String nextWordAction = "caret-next-word";
    public static final String selectionPreviousWordAction = "selection-previous-word";
    public static final String selectionNextWordAction = "selection-next-word";
    public static final String beginLineAction = "caret-begin-line";
    public static final String endLineAction = "caret-end-line";
    public static final String selectionBeginLineAction = "selection-begin-line";
    public static final String selectionEndLineAction = "selection-end-line";
    public static final String beginParagraphAction = "caret-begin-paragraph";
    public static final String endParagraphAction = "caret-end-paragraph";
    public static final String selectionBeginParagraphAction = "selection-begin-paragraph";
    public static final String selectionEndParagraphAction = "selection-end-paragraph";
    public static final String beginAction = "caret-begin";
    public static final String endAction = "caret-end";
    public static final String selectionBeginAction = "selection-begin";
    public static final String selectionEndAction = "selection-end";
    public static final String selectWordAction = "select-word";
    public static final String selectLineAction = "select-line";
    public static final String selectParagraphAction = "select-paragraph";
    public static final String selectAllAction = "select-all";
    static final String unselectAction = "unselect";
    static final String toggleComponentOrientationAction = "toggle-componentOrientation";
    public static final String defaultKeyTypedAction = "default-typed";
    private static final Action[] defaultActions = {new DefaultEditorKit$InsertContentAction(), new DefaultEditorKit$DeletePrevCharAction(), new DefaultEditorKit$DeleteNextCharAction(), new DefaultEditorKit$ReadOnlyAction(), new DefaultEditorKit$WritableAction(), new DefaultEditorKit$CutAction(), new DefaultEditorKit$CopyAction(), new DefaultEditorKit$PasteAction(), new DefaultEditorKit$VerticalPageAction(pageUpAction, -1, false), new DefaultEditorKit$VerticalPageAction(pageDownAction, 1, false), new DefaultEditorKit$VerticalPageAction(selectionPageUpAction, -1, true), new DefaultEditorKit$VerticalPageAction(selectionPageDownAction, 1, true), new DefaultEditorKit$PageAction(selectionPageLeftAction, true, true), new DefaultEditorKit$PageAction(selectionPageRightAction, false, true), new DefaultEditorKit$InsertBreakAction(), new DefaultEditorKit$BeepAction(), new DefaultEditorKit$NextVisualPositionAction(forwardAction, false, SwingConstants.EAST), new DefaultEditorKit$NextVisualPositionAction(backwardAction, false, SwingConstants.WEST), new DefaultEditorKit$NextVisualPositionAction(selectionForwardAction, true, SwingConstants.EAST), new DefaultEditorKit$NextVisualPositionAction(selectionBackwardAction, true, SwingConstants.WEST), new DefaultEditorKit$NextVisualPositionAction(upAction, false, SwingConstants.NORTH), new DefaultEditorKit$NextVisualPositionAction(downAction, false, SwingConstants.SOUTH), new DefaultEditorKit$NextVisualPositionAction(selectionUpAction, true, SwingConstants.NORTH), new DefaultEditorKit$NextVisualPositionAction(selectionDownAction, true, SwingConstants.SOUTH), new DefaultEditorKit$BeginWordAction(beginWordAction, false), new DefaultEditorKit$EndWordAction(endWordAction, false), new DefaultEditorKit$BeginWordAction(selectionBeginWordAction, true), new DefaultEditorKit$EndWordAction(selectionEndWordAction, true), new DefaultEditorKit$PreviousWordAction(previousWordAction, false), new DefaultEditorKit$NextWordAction(nextWordAction, false), new DefaultEditorKit$PreviousWordAction(selectionPreviousWordAction, true), new DefaultEditorKit$NextWordAction(selectionNextWordAction, true), new DefaultEditorKit$BeginLineAction(beginLineAction, false), new DefaultEditorKit$EndLineAction(endLineAction, false), new DefaultEditorKit$BeginLineAction(selectionBeginLineAction, true), new DefaultEditorKit$EndLineAction(selectionEndLineAction, true), new DefaultEditorKit$BeginParagraphAction(beginParagraphAction, false), new DefaultEditorKit$EndParagraphAction(endParagraphAction, false), new DefaultEditorKit$BeginParagraphAction(selectionBeginParagraphAction, true), new DefaultEditorKit$EndParagraphAction(selectionEndParagraphAction, true), new DefaultEditorKit$BeginAction(beginAction, false), new DefaultEditorKit$EndAction(endAction, false), new DefaultEditorKit$BeginAction(selectionBeginAction, true), new DefaultEditorKit$EndAction(selectionEndAction, true), new DefaultEditorKit$DefaultKeyTypedAction(), new DefaultEditorKit$InsertTabAction(), new DefaultEditorKit$SelectWordAction(), new DefaultEditorKit$SelectLineAction(), new DefaultEditorKit$SelectParagraphAction(), new DefaultEditorKit$SelectAllAction(), new DefaultEditorKit$UnselectAction(), new DefaultEditorKit$ToggleComponentOrientationAction(), new DefaultEditorKit$DumpModelAction()};
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
