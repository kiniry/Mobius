package java.rmi.activation;

public class UnknownObjectException extends ActivationException {
    private static final long serialVersionUID = 3425547551622251430L;
    
    public UnknownObjectException(String s) {
        super(s);
    }
}
