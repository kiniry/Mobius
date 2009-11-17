package java.nio.charset;

public class IllegalCharsetNameException extends IllegalArgumentException {
    private String charsetName;
    
    public IllegalCharsetNameException(String charsetName) {
        super(String.valueOf(charsetName));
        this.charsetName = charsetName;
    }
    
    public String getCharsetName() {
        return charsetName;
    }
}
