package java.lang;

abstract class StringCoding$StringEncoder {
    private final String requestedCharsetName;
    
    protected StringCoding$StringEncoder(String requestedCharsetName) {
        
        this.requestedCharsetName = requestedCharsetName;
    }
    
    final String requestedCharsetName() {
        return requestedCharsetName;
    }
    
    abstract String charsetName();
    
    abstract byte[] encode(char[] cs, int off, int len);
}
