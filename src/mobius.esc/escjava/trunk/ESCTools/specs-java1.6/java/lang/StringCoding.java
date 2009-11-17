package java.lang;

import java.io.UnsupportedEncodingException;
import java.lang.ref.SoftReference;
import java.nio.charset.Charset;
import java.nio.charset.IllegalCharsetNameException;
import java.nio.charset.UnsupportedCharsetException;
import sun.io.ByteToCharConverter;
import sun.io.CharToByteConverter;
import sun.io.Converters;
import sun.misc.MessageUtils;

class StringCoding {
    
    /*synthetic*/ static byte[] access$400(byte[] x0, int x1) {
        return trim(x0, x1);
    }
    
    /*synthetic*/ static char[] access$100(char[] x0, int x1) {
        return trim(x0, x1);
    }
    
    /*synthetic*/ static int access$000(int x0, float x1) {
        return scale(x0, x1);
    }
    {
    }
    
    private StringCoding() {
        
    }
    private static ThreadLocal decoder = new ThreadLocal();
    private static ThreadLocal encoder = new ThreadLocal();
    private static boolean warnUnsupportedCharset = true;
    
    private static Object deref(ThreadLocal tl) {
        SoftReference sr = (SoftReference)(SoftReference)tl.get();
        if (sr == null) return null;
        return sr.get();
    }
    
    private static void set(ThreadLocal tl, Object ob) {
        tl.set(new SoftReference(ob));
    }
    
    private static byte[] trim(byte[] ba, int len) {
        if (len == ba.length) return ba;
        byte[] tba = new byte[len];
        System.arraycopy(ba, 0, tba, 0, len);
        return tba;
    }
    
    private static char[] trim(char[] ca, int len) {
        if (len == ca.length) return ca;
        char[] tca = new char[len];
        System.arraycopy(ca, 0, tca, 0, len);
        return tca;
    }
    
    private static int scale(int len, float expansionFactor) {
        return (int)(len * (double)expansionFactor);
    }
    
    private static Charset lookupCharset(String csn) {
        if (Charset.isSupported(csn)) {
            try {
                return Charset.forName(csn);
            } catch (UnsupportedCharsetException x) {
                throw new Error(x);
            }
        }
        return null;
    }
    
    private static void warnUnsupportedCharset(String csn) {
        if (warnUnsupportedCharset) {
            MessageUtils.err("WARNING: Default charset " + csn + " not supported, using ISO-8859-1 instead");
            warnUnsupportedCharset = false;
        }
    }
    {
    }
    {
    }
    {
    }
    
    static char[] decode(String charsetName, byte[] ba, int off, int len) throws UnsupportedEncodingException {
        StringCoding$StringDecoder sd = (StringCoding$StringDecoder)(StringCoding$StringDecoder)deref(decoder);
        String csn = (charsetName == null) ? "ISO-8859-1" : charsetName;
        if ((sd == null) || !(csn.equals(sd.requestedCharsetName()) || csn.equals(sd.charsetName()))) {
            sd = null;
            try {
                Charset cs = lookupCharset(csn);
                if (cs != null) sd = new StringCoding$CharsetSD(cs, csn, null); else sd = null;
            } catch (IllegalCharsetNameException x) {
            }
            if (sd == null) sd = new StringCoding$ConverterSD(ByteToCharConverter.getConverter(csn), csn, null);
            set(decoder, sd);
        }
        return sd.decode(ba, off, len);
    }
    
    static char[] decode(byte[] ba, int off, int len) {
        String csn = Converters.getDefaultEncodingName();
        try {
            return decode(csn, ba, off, len);
        } catch (UnsupportedEncodingException x) {
            Converters.resetDefaultEncodingName();
            warnUnsupportedCharset(csn);
        }
        try {
            return decode("ISO-8859-1", ba, off, len);
        } catch (UnsupportedEncodingException x) {
            MessageUtils.err("ISO-8859-1 charset not available: " + x.toString());
            System.exit(1);
            return null;
        }
    }
    {
    }
    {
    }
    {
    }
    
    static byte[] encode(String charsetName, char[] ca, int off, int len) throws UnsupportedEncodingException {
        StringCoding$StringEncoder se = (StringCoding$StringEncoder)(StringCoding$StringEncoder)deref(encoder);
        String csn = (charsetName == null) ? "ISO-8859-1" : charsetName;
        if ((se == null) || !(csn.equals(se.requestedCharsetName()) || csn.equals(se.charsetName()))) {
            se = null;
            try {
                Charset cs = lookupCharset(csn);
                if (cs != null) se = new StringCoding$CharsetSE(cs, csn, null);
            } catch (IllegalCharsetNameException x) {
            }
            if (se == null) se = new StringCoding$ConverterSE(CharToByteConverter.getConverter(csn), csn, null);
            set(encoder, se);
        }
        return se.encode(ca, off, len);
    }
    
    static byte[] encode(char[] ca, int off, int len) {
        String csn = Converters.getDefaultEncodingName();
        try {
            return encode(csn, ca, off, len);
        } catch (UnsupportedEncodingException x) {
            Converters.resetDefaultEncodingName();
            warnUnsupportedCharset(csn);
        }
        try {
            return encode("ISO-8859-1", ca, off, len);
        } catch (UnsupportedEncodingException x) {
            MessageUtils.err("ISO-8859-1 charset not available: " + x.toString());
            System.exit(1);
            return null;
        }
    }
}
