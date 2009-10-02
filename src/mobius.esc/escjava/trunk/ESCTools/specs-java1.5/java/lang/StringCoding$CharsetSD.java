package java.lang;

import java.nio.ByteBuffer;
import java.nio.CharBuffer;
import java.nio.charset.Charset;
import java.nio.charset.CharsetDecoder;
import java.nio.charset.CharacterCodingException;
import java.nio.charset.CoderResult;
import java.nio.charset.CodingErrorAction;
import sun.nio.cs.HistoricallyNamedCharset;

class StringCoding$CharsetSD extends StringCoding$StringDecoder {
    
    /*synthetic*/ StringCoding$CharsetSD(Charset x0, String x1, java.lang.StringCoding$1 x2) {
        this(x0, x1);
    }
    private final Charset cs;
    private final CharsetDecoder cd;
    
    private StringCoding$CharsetSD(Charset cs, String rcn) {
        super(rcn);
        this.cs = cs;
        this.cd = cs.newDecoder().onMalformedInput(CodingErrorAction.REPLACE).onUnmappableCharacter(CodingErrorAction.REPLACE);
    }
    
    String charsetName() {
        if (cs instanceof HistoricallyNamedCharset) return ((HistoricallyNamedCharset)(HistoricallyNamedCharset)cs).historicalName();
        return cs.name();
    }
    
    char[] decode(byte[] ba, int off, int len) {
        int en = StringCoding.access$000(len, cd.maxCharsPerByte());
        char[] ca = new char[en];
        if (len == 0) return ca;
        cd.reset();
        ByteBuffer bb = ByteBuffer.wrap(ba, off, len);
        CharBuffer cb = CharBuffer.wrap(ca);
        try {
            CoderResult cr = cd.decode(bb, cb, true);
            if (!cr.isUnderflow()) cr.throwException();
            cr = cd.flush(cb);
            if (!cr.isUnderflow()) cr.throwException();
        } catch (CharacterCodingException x) {
            throw new Error(x);
        }
        return StringCoding.access$100(ca, cb.position());
    }
}
