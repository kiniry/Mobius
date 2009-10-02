package java.lang;

import java.io.CharConversionException;
import sun.io.ByteToCharConverter;

class StringCoding$ConverterSD extends StringCoding$StringDecoder {
    
    /*synthetic*/ StringCoding$ConverterSD(ByteToCharConverter x0, String x1, java.lang.StringCoding$1 x2) {
        this(x0, x1);
    }
    private ByteToCharConverter btc;
    
    private StringCoding$ConverterSD(ByteToCharConverter btc, String rcn) {
        super(rcn);
        this.btc = btc;
    }
    
    String charsetName() {
        return btc.getCharacterEncoding();
    }
    
    char[] decode(byte[] ba, int off, int len) {
        int en = StringCoding.access$000(len, btc.getMaxCharsPerByte());
        char[] ca = new char[en];
        if (len == 0) return ca;
        btc.reset();
        int n = 0;
        try {
            n = btc.convert(ba, off, off + len, ca, 0, en);
            n += btc.flush(ca, btc.nextCharIndex(), en);
        } catch (CharConversionException x) {
            n = btc.nextCharIndex();
        }
        return StringCoding.access$100(ca, n);
    }
}
