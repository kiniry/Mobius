package java.nio.charset;

public class UnmappableCharacterException extends CharacterCodingException {
    private int inputLength;
    
    public UnmappableCharacterException(int inputLength) {
        
        this.inputLength = inputLength;
    }
    
    public int getInputLength() {
        return inputLength;
    }
    
    public String getMessage() {
        return "Input length = " + inputLength;
    }
}
