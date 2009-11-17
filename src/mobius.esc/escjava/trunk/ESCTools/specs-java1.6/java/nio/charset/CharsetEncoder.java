package java.nio.charset;

import java.nio.ByteBuffer;
import java.nio.CharBuffer;
import java.nio.BufferOverflowException;
import java.nio.BufferUnderflowException;
import java.lang.ref.WeakReference;
import java.nio.charset.CoderMalfunctionError;

public abstract class CharsetEncoder {
    /*synthetic*/ static final boolean $assertionsDisabled = !CharsetEncoder.class.desiredAssertionStatus();
    private final Charset charset;
    private final float averageBytesPerChar;
    private final float maxBytesPerChar;
    private byte[] replacement;
    private CodingErrorAction malformedInputAction = CodingErrorAction.REPORT;
    private CodingErrorAction unmappableCharacterAction = CodingErrorAction.REPORT;
    private static final int ST_RESET = 0;
    private static final int ST_CODING = 1;
    private static final int ST_END = 2;
    private static final int ST_FLUSHED = 3;
    private int state = ST_RESET;
    private static String[] stateNames = {"RESET", "CODING", "CODING_END", "FLUSHED"};
    
    protected CharsetEncoder(Charset cs, float averageBytesPerChar, float maxBytesPerChar, byte[] replacement) {
        
        this.charset = cs;
        if (averageBytesPerChar <= 0.0F) throw new IllegalArgumentException("Non-positive averageBytesPerChar");
        if (maxBytesPerChar <= 0.0F) throw new IllegalArgumentException("Non-positive maxBytesPerChar");
        if (!Charset.atBugLevel("1.4")) {
            if (averageBytesPerChar > maxBytesPerChar) throw new IllegalArgumentException("averageBytesPerChar exceeds maxBytesPerChar");
        }
        this.replacement = replacement;
        this.averageBytesPerChar = averageBytesPerChar;
        this.maxBytesPerChar = maxBytesPerChar;
        replaceWith(replacement);
    }
    
    protected CharsetEncoder(Charset cs, float averageBytesPerChar, float maxBytesPerChar) {
        this(cs, averageBytesPerChar, maxBytesPerChar, new byte[]{(byte)'?'});
    }
    
    public final Charset charset() {
        return charset;
    }
    
    public final byte[] replacement() {
        return replacement;
    }
    
    public final CharsetEncoder replaceWith(byte[] newReplacement) {
        if (newReplacement == null) throw new IllegalArgumentException("Null replacement");
        int len = newReplacement.length;
        if (len == 0) throw new IllegalArgumentException("Empty replacement");
        if (len > maxBytesPerChar) throw new IllegalArgumentException("Replacement too long");
        if (!isLegalReplacement(newReplacement)) throw new IllegalArgumentException("Illegal replacement");
        this.replacement = newReplacement;
        implReplaceWith(newReplacement);
        return this;
    }
    
    protected void implReplaceWith(byte[] newReplacement) {
    }
    private WeakReference cachedDecoder = null;
    
    public boolean isLegalReplacement(byte[] repl) {
        WeakReference wr = cachedDecoder;
        CharsetDecoder dec = null;
        if ((wr == null) || ((dec = (CharsetDecoder)(CharsetDecoder)wr.get()) == null)) {
            dec = charset().newDecoder();
            dec.onMalformedInput(CodingErrorAction.REPORT);
            dec.onUnmappableCharacter(CodingErrorAction.REPORT);
            cachedDecoder = new WeakReference(dec);
        } else {
            dec.reset();
        }
        ByteBuffer bb = ByteBuffer.wrap(repl);
        CharBuffer cb = CharBuffer.allocate((int)(bb.remaining() * (double)dec.maxCharsPerByte()));
        CoderResult cr = dec.decode(bb, cb, true);
        return !cr.isError();
    }
    
    public CodingErrorAction malformedInputAction() {
        return malformedInputAction;
    }
    
    public final CharsetEncoder onMalformedInput(CodingErrorAction newAction) {
        if (newAction == null) throw new IllegalArgumentException("Null action");
        malformedInputAction = newAction;
        implOnMalformedInput(newAction);
        return this;
    }
    
    protected void implOnMalformedInput(CodingErrorAction newAction) {
    }
    
    public CodingErrorAction unmappableCharacterAction() {
        return unmappableCharacterAction;
    }
    
    public final CharsetEncoder onUnmappableCharacter(CodingErrorAction newAction) {
        if (newAction == null) throw new IllegalArgumentException("Null action");
        unmappableCharacterAction = newAction;
        implOnUnmappableCharacter(newAction);
        return this;
    }
    
    protected void implOnUnmappableCharacter(CodingErrorAction newAction) {
    }
    
    public final float averageBytesPerChar() {
        return averageBytesPerChar;
    }
    
    public final float maxBytesPerChar() {
        return maxBytesPerChar;
    }
    
    public final CoderResult encode(CharBuffer in, ByteBuffer out, boolean endOfInput) {
        int newState = endOfInput ? ST_END : ST_CODING;
        if ((state != ST_RESET) && (state != ST_CODING) && !(endOfInput && (state == ST_END))) throwIllegalStateException(state, newState);
        state = newState;
        for (; ; ) {
            CoderResult cr;
            try {
                cr = encodeLoop(in, out);
            } catch (BufferUnderflowException x) {
                throw new CoderMalfunctionError(x);
            } catch (BufferOverflowException x) {
                throw new CoderMalfunctionError(x);
            }
            if (cr.isOverflow()) return cr;
            if (cr.isUnderflow()) {
                if (endOfInput && in.hasRemaining()) {
                    cr = CoderResult.malformedForLength(in.remaining());
                } else {
                    return cr;
                }
            }
            CodingErrorAction action = null;
            if (cr.isMalformed()) action = malformedInputAction; else if (cr.isUnmappable()) action = unmappableCharacterAction; else if (!$assertionsDisabled) throw new AssertionError(cr.toString());
            if (action == CodingErrorAction.REPORT) return cr;
            if (action == CodingErrorAction.REPLACE) {
                if (out.remaining() < replacement.length) return CoderResult.OVERFLOW;
                out.put(replacement);
            }
            if ((action == CodingErrorAction.IGNORE) || (action == CodingErrorAction.REPLACE)) {
                in.position(in.position() + cr.length());
                continue;
            }
            if (!$assertionsDisabled) throw new AssertionError();
        }
    }
    
    public final CoderResult flush(ByteBuffer out) {
        if (state != ST_END) throwIllegalStateException(state, ST_FLUSHED);
        state = ST_FLUSHED;
        return implFlush(out);
    }
    
    protected CoderResult implFlush(ByteBuffer out) {
        return CoderResult.UNDERFLOW;
    }
    
    public final CharsetEncoder reset() {
        implReset();
        state = ST_RESET;
        return this;
    }
    
    protected void implReset() {
    }
    
    protected abstract CoderResult encodeLoop(CharBuffer in, ByteBuffer out);
    
    public final ByteBuffer encode(CharBuffer in) throws CharacterCodingException {
        int n = (int)(in.remaining() * averageBytesPerChar());
        ByteBuffer out = ByteBuffer.allocate(n);
        if (n == 0) return out;
        reset();
        for (; ; ) {
            CoderResult cr;
            if (in.hasRemaining()) cr = encode(in, out, true); else cr = flush(out);
            if (cr.isUnderflow()) break;
            if (cr.isOverflow()) {
                n *= 2;
                ByteBuffer o = ByteBuffer.allocate(n);
                out.flip();
                o.put(out);
                out = o;
                continue;
            }
            cr.throwException();
        }
        out.flip();
        return out;
    }
    
    private boolean canEncode(CharBuffer cb) {
        if (state == ST_FLUSHED) reset(); else if (state != ST_RESET) throwIllegalStateException(state, ST_CODING);
        CodingErrorAction ma = malformedInputAction();
        CodingErrorAction ua = unmappableCharacterAction();
        try {
            onMalformedInput(CodingErrorAction.REPORT);
            onUnmappableCharacter(CodingErrorAction.REPORT);
            encode(cb);
        } catch (CharacterCodingException x) {
            return false;
        } finally {
            onMalformedInput(ma);
            onUnmappableCharacter(ua);
            reset();
        }
        return true;
    }
    
    public boolean canEncode(char c) {
        CharBuffer cb = CharBuffer.allocate(1);
        cb.put(c);
        cb.flip();
        return canEncode(cb);
    }
    
    public boolean canEncode(CharSequence cs) {
        CharBuffer cb;
        if (cs instanceof CharBuffer) cb = ((CharBuffer)(CharBuffer)cs).duplicate(); else cb = CharBuffer.wrap(cs.toString());
        return canEncode(cb);
    }
    
    private void throwIllegalStateException(int from, int to) {
        throw new IllegalStateException("Current state = " + stateNames[from] + ", new state = " + stateNames[to]);
    }
}
