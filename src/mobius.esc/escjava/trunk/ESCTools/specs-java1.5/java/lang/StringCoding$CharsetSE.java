package java.lang;

import java.nio.ByteBuffer;
import java.nio.CharBuffer;
import java.nio.charset.Charset;
import java.nio.charset.CharsetEncoder;
import java.nio.charset.CharacterCodingException;
import java.nio.charset.CoderResult;
import java.nio.charset.CodingErrorAction;
import sun.nio.cs.HistoricallyNamedCharset;

class StringCoding$CharsetSE extends StringCoding$StringEncoder {
    
    /*synthetic*/ StringCoding$CharsetSE(Charset x0, String x1, java.lang.StringCoding$1 x2) {
        this(x0, x1);
    }
    private Charset cs;
    private CharsetEncoder ce;
    
    private StringCoding$CharsetSE(Charset cs, String rcn) {
        super(rcn);
        this.cs = cs;
        this.ce = cs.newEncoder().onMalformedInput(CodingErrorAction.REPLACE).onUnmappableCharacter(CodingErrorAction.REPLACE);
    }
    
    String charsetName() {
        if (cs instanceof HistoricallyNamedCharset) return ((HistoricallyNamedCharset)(HistoricallyNamedCharset)cs).historicalName();
        return cs.name();
    }
    
    byte[] encode(char[] ca, int off, int len) {
        int en = StringCoding.access$000(len, ce.maxBytesPerChar());
        byte[] ba = new byte[en];
        if (len == 0) return ba;
        ce.reset();
        ByteBuffer bb = ByteBuffer.wrap(ba);
        CharBuffer cb = CharBuffer.wrap(ca, off, len);
        try {
            CoderResult cr = ce.encode(cb, bb, true);
            if (!cr.isUnderflow()) cr.throwException();
            cr = ce.flush(bb);
            if (!cr.isUnderflow()) cr.throwException();
        } catch (CharacterCodingException x) {
            throw new Error(x);
        }
        return StringCoding.access$400(ba, bb.position());
    }
}
