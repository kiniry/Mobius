package java.text;

import java.io.InvalidObjectException;
import java.util.HashMap;
import java.util.Map;

public class NumberFormat$Field extends Format$Field {
    private static final long serialVersionUID = 7494728892700160890L;
    private static final Map instanceMap = new HashMap(11);
    
    protected NumberFormat$Field(String name) {
        super(name);
        if (this.getClass() == NumberFormat.Field.class) {
            instanceMap.put(name, this);
        }
    }
    
    protected Object readResolve() throws InvalidObjectException {
        if (this.getClass() != NumberFormat.Field.class) {
            throw new InvalidObjectException("subclass didn\'t correctly implement readResolve");
        }
        Object instance = instanceMap.get(getName());
        if (instance != null) {
            return instance;
        } else {
            throw new InvalidObjectException("unknown attribute name");
        }
    }
    public static final NumberFormat$Field INTEGER = new NumberFormat$Field("integer");
    public static final NumberFormat$Field FRACTION = new NumberFormat$Field("fraction");
    public static final NumberFormat$Field EXPONENT = new NumberFormat$Field("exponent");
    public static final NumberFormat$Field DECIMAL_SEPARATOR = new NumberFormat$Field("decimal separator");
    public static final NumberFormat$Field SIGN = new NumberFormat$Field("sign");
    public static final NumberFormat$Field GROUPING_SEPARATOR = new NumberFormat$Field("grouping separator");
    public static final NumberFormat$Field EXPONENT_SYMBOL = new NumberFormat$Field("exponent symbol");
    public static final NumberFormat$Field PERCENT = new NumberFormat$Field("percent");
    public static final NumberFormat$Field PERMILLE = new NumberFormat$Field("per mille");
    public static final NumberFormat$Field CURRENCY = new NumberFormat$Field("currency");
    public static final NumberFormat$Field EXPONENT_SIGN = new NumberFormat$Field("exponent sign");
}
