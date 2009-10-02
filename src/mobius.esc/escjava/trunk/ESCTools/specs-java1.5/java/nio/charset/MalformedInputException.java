package java.nio.charset;

public class MalformedInputException extends CharacterCodingException {
    private int inputLength;
    
    public MalformedInputException(int inputLength) {
        
        this.inputLength = inputLength;
    }
    
    public int getInputLength() {
        return inputLength;
    }
    
    public String getMessage() {
        return "Input length = " + inputLength;
    }
}
