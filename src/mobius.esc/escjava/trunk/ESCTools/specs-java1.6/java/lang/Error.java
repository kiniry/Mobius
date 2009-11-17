package java.lang;

public class Error extends Throwable {
    static final long serialVersionUID = 4980196508277280342L;
    
    public Error() {
        
    }
    
    public Error(String message) {
        super(message);
    }
    
    public Error(String message, Throwable cause) {
        super(message, cause);
    }
    
    public Error(Throwable cause) {
        super(cause);
    }
}
