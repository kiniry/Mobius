package javax.swing.text;

public class DocumentFilter {
    
    public DocumentFilter() {
        
    }
    
    public void remove(DocumentFilter$FilterBypass fb, int offset, int length) throws BadLocationException {
        fb.remove(offset, length);
    }
    
    public void insertString(DocumentFilter$FilterBypass fb, int offset, String string, AttributeSet attr) throws BadLocationException {
        fb.insertString(offset, string, attr);
    }
    
    public void replace(DocumentFilter$FilterBypass fb, int offset, int length, String text, AttributeSet attrs) throws BadLocationException {
        fb.replace(offset, length, text, attrs);
    }
    {
    }
}
