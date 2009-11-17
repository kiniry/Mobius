package java.text;

import java.io.InvalidObjectException;

public class MessageFormat$Field extends Format$Field {
    private static final long serialVersionUID = 7899943957617360810L;
    
    protected MessageFormat$Field(String name) {
        super(name);
    }
    
    protected Object readResolve() throws InvalidObjectException {
        if (this.getClass() != MessageFormat.Field.class) {
            throw new InvalidObjectException("subclass didn\'t correctly implement readResolve");
        }
        return ARGUMENT;
    }
    public static final MessageFormat$Field ARGUMENT = new MessageFormat$Field("message argument field");
}
