package javax.swing.text;

public abstract class DocumentFilter$FilterBypass {
    
    public DocumentFilter$FilterBypass() {
        
    }
    
    public abstract Document getDocument();
    
    public abstract void remove(int offset, int length) throws BadLocationException;
    
    public abstract void insertString(int offset, String string, AttributeSet attr) throws BadLocationException;
    
    public abstract void replace(int offset, int length, String string, AttributeSet attrs) throws BadLocationException;
}
