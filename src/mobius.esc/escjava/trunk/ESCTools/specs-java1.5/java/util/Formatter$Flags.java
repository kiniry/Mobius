package java.util;

class Formatter$Flags {
    
    /*synthetic*/ static Formatter$Flags access$100(Formatter$Flags x0, Formatter$Flags x1) {
        return x0.add(x1);
    }
    private int flags;
    static final Formatter$Flags NONE = new Formatter$Flags(0);
    static final Formatter$Flags LEFT_JUSTIFY = new Formatter$Flags(1 << 0);
    static final Formatter$Flags UPPERCASE = new Formatter$Flags(1 << 1);
    static final Formatter$Flags ALTERNATE = new Formatter$Flags(1 << 2);
    static final Formatter$Flags PLUS = new Formatter$Flags(1 << 3);
    static final Formatter$Flags LEADING_SPACE = new Formatter$Flags(1 << 4);
    static final Formatter$Flags ZERO_PAD = new Formatter$Flags(1 << 5);
    static final Formatter$Flags GROUP = new Formatter$Flags(1 << 6);
    static final Formatter$Flags PARENTHESES = new Formatter$Flags(1 << 7);
    static final Formatter$Flags PREVIOUS = new Formatter$Flags(1 << 8);
    
    private Formatter$Flags(int f) {
        
        flags = f;
    }
    
    public int valueOf() {
        return flags;
    }
    
    public boolean contains(Formatter$Flags f) {
        return (flags & f.valueOf()) == f.valueOf();
    }
    
    public Formatter$Flags dup() {
        return new Formatter$Flags(flags);
    }
    
    private Formatter$Flags add(Formatter$Flags f) {
        flags |= f.valueOf();
        return this;
    }
    
    public Formatter$Flags remove(Formatter$Flags f) {
        flags &= ~f.valueOf();
        return this;
    }
    
    public static Formatter$Flags parse(String s) {
        char[] ca = s.toCharArray();
        Formatter$Flags f = new Formatter$Flags(0);
        for (int i = 0; i < ca.length; i++) {
            Formatter$Flags v = parse(ca[i]);
            if (f.contains(v)) throw new DuplicateFormatFlagsException(v.toString());
            f.add(v);
        }
        return f;
    }
    
    private static Formatter$Flags parse(char c) {
        switch (c) {
        case '-': 
            return LEFT_JUSTIFY;
        
        case '#': 
            return ALTERNATE;
        
        case '+': 
            return PLUS;
        
        case ' ': 
            return LEADING_SPACE;
        
        case '0': 
            return ZERO_PAD;
        
        case ',': 
            return GROUP;
        
        case '(': 
            return PARENTHESES;
        
        case '<': 
            return PREVIOUS;
        
        default: 
            throw new UnknownFormatFlagsException(String.valueOf(c));
        
        }
    }
    
    public static String toString(Formatter$Flags f) {
        return f.toString();
    }
    
    public String toString() {
        StringBuilder sb = new StringBuilder();
        if (contains(LEFT_JUSTIFY)) sb.append('-');
        if (contains(UPPERCASE)) sb.append('^');
        if (contains(ALTERNATE)) sb.append('#');
        if (contains(PLUS)) sb.append('+');
        if (contains(LEADING_SPACE)) sb.append(' ');
        if (contains(ZERO_PAD)) sb.append('0');
        if (contains(GROUP)) sb.append(',');
        if (contains(PARENTHESES)) sb.append('(');
        if (contains(PREVIOUS)) sb.append('<');
        return sb.toString();
    }
}
