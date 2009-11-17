package java.lang;

abstract class StringCoding$StringDecoder {
    private final String requestedCharsetName;
    
    protected StringCoding$StringDecoder(String requestedCharsetName) {
        
        this.requestedCharsetName = requestedCharsetName;
    }
    
    final String requestedCharsetName() {
        return requestedCharsetName;
    }
    
    abstract String charsetName();
    
    abstract char[] decode(byte[] ba, int off, int len);
}
