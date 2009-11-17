package java.lang;

import java.io.CharConversionException;
import sun.io.CharToByteConverter;

class StringCoding$ConverterSE extends StringCoding$StringEncoder {
    
    /*synthetic*/ StringCoding$ConverterSE(CharToByteConverter x0, String x1, java.lang.StringCoding$1 x2) {
        this(x0, x1);
    }
    private CharToByteConverter ctb;
    
    private StringCoding$ConverterSE(CharToByteConverter ctb, String rcn) {
        super(rcn);
        this.ctb = ctb;
    }
    
    String charsetName() {
        return ctb.getCharacterEncoding();
    }
    
    byte[] encode(char[] ca, int off, int len) {
        int en = StringCoding.access$000(len, ctb.getMaxBytesPerChar());
        byte[] ba = new byte[en];
        if (len == 0) return ba;
        ctb.reset();
        int n;
        try {
            n = ctb.convertAny(ca, off, (off + len), ba, 0, en);
            n += ctb.flushAny(ba, ctb.nextByteIndex(), en);
        } catch (CharConversionException x) {
            throw new Error("Converter malfunction: " + ctb.getClass().getName(), x);
        }
        return StringCoding.access$400(ba, n);
    }
}
