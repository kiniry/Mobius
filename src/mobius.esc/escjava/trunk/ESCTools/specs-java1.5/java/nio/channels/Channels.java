package java.nio.channels;

import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.Reader;
import java.io.Writer;
import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.charset.Charset;
import java.nio.charset.CharsetDecoder;
import java.nio.charset.CharsetEncoder;
import sun.nio.cs.StreamDecoder;
import sun.nio.cs.StreamEncoder;

public final class Channels {
    
    /*synthetic*/ static void access$000(WritableByteChannel x0, ByteBuffer x1) throws IOException {
        writeFully(x0, x1);
    }
    
    private Channels() {
        
    }
    
    private static void writeFullyImpl(WritableByteChannel ch, ByteBuffer bb) throws IOException {
        while (bb.remaining() > 0) {
            int n = ch.write(bb);
            if (n <= 0) throw new RuntimeException("no bytes written");
        }
    }
    
    private static void writeFully(WritableByteChannel ch, ByteBuffer bb) throws IOException {
        if (ch instanceof SelectableChannel) {
            SelectableChannel sc = (SelectableChannel)(SelectableChannel)ch;
            synchronized (sc.blockingLock()) {
                if (!sc.isBlocking()) throw new IllegalBlockingModeException();
                writeFullyImpl(ch, bb);
            }
        } else {
            writeFullyImpl(ch, bb);
        }
    }
    
    public static InputStream newInputStream(ReadableByteChannel ch) {
        return new sun.nio.ch.ChannelInputStream(ch);
    }
    
    public static OutputStream newOutputStream(final WritableByteChannel ch) {
        return new Channels$1(ch);
    }
    
    public static ReadableByteChannel newChannel(final InputStream in) {
        if (in instanceof FileInputStream) {
            String inClass = in.getClass().toString();
            if (inClass.equals("java.io.FileInputStream")) return ((FileInputStream)(FileInputStream)in).getChannel();
        }
        return new Channels$ReadableByteChannelImpl(in);
    }
    {
    }
    
    public static WritableByteChannel newChannel(final OutputStream out) {
        if (out instanceof FileOutputStream) {
            String outClass = out.getClass().toString();
            if (outClass.equals("java.io.FileOutputStream")) return ((FileOutputStream)(FileOutputStream)out).getChannel();
        }
        return new Channels$WritableByteChannelImpl(out);
    }
    {
    }
    
    public static Reader newReader(ReadableByteChannel ch, CharsetDecoder dec, int minBufferCap) {
        dec.reset();
        return StreamDecoder.forDecoder(ch, dec, minBufferCap);
    }
    
    public static Reader newReader(ReadableByteChannel ch, String csName) {
        return newReader(ch, Charset.forName(csName).newDecoder(), -1);
    }
    
    public static Writer newWriter(final WritableByteChannel ch, final CharsetEncoder enc, final int minBufferCap) {
        enc.reset();
        return StreamEncoder.forEncoder(ch, enc, minBufferCap);
    }
    
    public static Writer newWriter(WritableByteChannel ch, String csName) {
        return newWriter(ch, Charset.forName(csName).newEncoder(), -1);
    }
}
