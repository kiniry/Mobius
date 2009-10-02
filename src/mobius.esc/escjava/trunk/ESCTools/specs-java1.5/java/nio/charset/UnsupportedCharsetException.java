package java.nio.charset;

public class UnsupportedCharsetException extends IllegalArgumentException {
    private String charsetName;
    
    public UnsupportedCharsetException(String charsetName) {
        super(String.valueOf(charsetName));
        this.charsetName = charsetName;
    }
    
    public String getCharsetName() {
        return charsetName;
    }
}
