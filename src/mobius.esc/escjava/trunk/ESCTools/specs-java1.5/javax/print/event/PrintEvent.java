package javax.print.event;

public class PrintEvent extends java.util.EventObject {
    private static final long serialVersionUID = 2286914924430763847L;
    
    public PrintEvent(Object source) {
        super(source);
    }
    
    public String toString() {
        return ("PrintEvent on " + getSource().toString());
    }
}
