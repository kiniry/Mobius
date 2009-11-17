package java.nio.charset;

import java.nio.*;

public class CoderResult {
    
    /*synthetic*/ CoderResult(int x0, int x1, java.nio.charset.CoderResult$1 x2) {
        this(x0, x1);
    }
    /*synthetic*/ static final boolean $assertionsDisabled = !CoderResult.class.desiredAssertionStatus();
    private static final int CR_UNDERFLOW = 0;
    private static final int CR_OVERFLOW = 1;
    private static final int CR_ERROR_MIN = 2;
    private static final int CR_MALFORMED = 2;
    private static final int CR_UNMAPPABLE = 3;
    private static final String[] names = {"UNDERFLOW", "OVERFLOW", "MALFORMED", "UNMAPPABLE"};
    private final int type;
    private final int length;
    
    private CoderResult(int type, int length) {
        
        this.type = type;
        this.length = length;
    }
    
    public String toString() {
        String nm = names[type];
        return isError() ? nm + "[" + length + "]" : nm;
    }
    
    public boolean isUnderflow() {
        return (type == CR_UNDERFLOW);
    }
    
    public boolean isOverflow() {
        return (type == CR_OVERFLOW);
    }
    
    public boolean isError() {
        return (type >= CR_ERROR_MIN);
    }
    
    public boolean isMalformed() {
        return (type == CR_MALFORMED);
    }
    
    public boolean isUnmappable() {
        return (type == CR_UNMAPPABLE);
    }
    
    public int length() {
        if (!isError()) throw new UnsupportedOperationException();
        return length;
    }
    public static final CoderResult UNDERFLOW = new CoderResult(CR_UNDERFLOW, 0);
    public static final CoderResult OVERFLOW = new CoderResult(CR_OVERFLOW, 0);
    {
    }
    private static CoderResult$Cache malformedCache = new CoderResult$1();
    
    public static CoderResult malformedForLength(int length) {
        return CoderResult.Cache.access$200(malformedCache, length);
    }
    private static CoderResult$Cache unmappableCache = new CoderResult$2();
    
    public static CoderResult unmappableForLength(int length) {
        return CoderResult.Cache.access$200(unmappableCache, length);
    }
    
    public void throwException() throws CharacterCodingException {
        switch (type) {
        case CR_UNDERFLOW: 
            throw new BufferUnderflowException();
        
        case CR_OVERFLOW: 
            throw new BufferOverflowException();
        
        case CR_MALFORMED: 
            throw new MalformedInputException(length);
        
        case CR_UNMAPPABLE: 
            throw new UnmappableCharacterException(length);
        
        default: 
            if (!$assertionsDisabled) throw new AssertionError();
        
        }
    }
}
