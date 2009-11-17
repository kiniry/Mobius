package java.nio.channels;

import java.io.OutputStream;
import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.channels.spi.AbstractInterruptibleChannel;

class Channels$WritableByteChannelImpl extends AbstractInterruptibleChannel implements WritableByteChannel {
    OutputStream out;
    private static final int TRANSFER_SIZE = 8192;
    private byte[] buf = new byte[0];
    private boolean open = true;
    private Object writeLock = new Object();
    
    Channels$WritableByteChannelImpl(OutputStream out) {
        
        this.out = out;
    }
    
    public int write(ByteBuffer src) throws IOException {
        int len = src.remaining();
        int totalWritten = 0;
        synchronized (writeLock) {
            while (totalWritten < len) {
                int bytesToWrite = Math.min((len - totalWritten), TRANSFER_SIZE);
                if (buf.length < bytesToWrite) buf = new byte[bytesToWrite];
                src.get(buf, 0, bytesToWrite);
                try {
                    begin();
                    out.write(buf, 0, bytesToWrite);
                } finally {
                    end(bytesToWrite > 0);
                }
                totalWritten += bytesToWrite;
            }
            return totalWritten;
        }
    }
    
    protected void implCloseChannel() throws IOException {
        out.close();
        open = false;
    }
}
