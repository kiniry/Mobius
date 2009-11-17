package javax.swing.text;

import java.io.*;
import javax.swing.Action;
import javax.swing.JEditorPane;

public abstract class EditorKit implements Cloneable, Serializable {
    
    public EditorKit() {
        
    }
    
    public Object clone() {
        Object o;
        try {
            o = super.clone();
        } catch (CloneNotSupportedException cnse) {
            o = null;
        }
        return o;
    }
    
    public void install(JEditorPane c) {
    }
    
    public void deinstall(JEditorPane c) {
    }
    
    public abstract String getContentType();
    
    public abstract ViewFactory getViewFactory();
    
    public abstract Action[] getActions();
    
    public abstract Caret createCaret();
    
    public abstract Document createDefaultDocument();
    
    public abstract void read(InputStream in, Document doc, int pos) throws IOException, BadLocationException;
    
    public abstract void write(OutputStream out, Document doc, int pos, int len) throws IOException, BadLocationException;
    
    public abstract void read(Reader in, Document doc, int pos) throws IOException, BadLocationException;
    
    public abstract void write(Writer out, Document doc, int pos, int len) throws IOException, BadLocationException;
}
