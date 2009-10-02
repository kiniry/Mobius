package java.io;

public class OptionalDataException extends ObjectStreamException {
    
    OptionalDataException(int len) {
        
        eof = false;
        length = len;
    }
    
    OptionalDataException(boolean end) {
        
        length = 0;
        eof = end;
    }
    public int length;
    public boolean eof;
}
