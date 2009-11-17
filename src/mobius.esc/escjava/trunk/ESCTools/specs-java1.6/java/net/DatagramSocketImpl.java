package java.net;

import java.io.FileDescriptor;
import java.io.IOException;

public abstract class DatagramSocketImpl implements SocketOptions {
    
    public DatagramSocketImpl() {
        
    }
    protected int localPort;
    protected FileDescriptor fd;
    
    protected abstract void create() throws SocketException;
    
    protected abstract void bind(int lport, InetAddress laddr) throws SocketException;
    
    protected abstract void send(DatagramPacket p) throws IOException;
    
    protected void connect(InetAddress address, int port) throws SocketException {
    }
    
    protected void disconnect() {
    }
    
    protected abstract int peek(InetAddress i) throws IOException;
    
    protected abstract int peekData(DatagramPacket p) throws IOException;
    
    protected abstract void receive(DatagramPacket p) throws IOException;
    
    
    protected abstract void setTTL(byte ttl) throws IOException;
    
    
    protected abstract byte getTTL() throws IOException;
    
    protected abstract void setTimeToLive(int ttl) throws IOException;
    
    protected abstract int getTimeToLive() throws IOException;
    
    protected abstract void join(InetAddress inetaddr) throws IOException;
    
    protected abstract void leave(InetAddress inetaddr) throws IOException;
    
    protected abstract void joinGroup(SocketAddress mcastaddr, NetworkInterface netIf) throws IOException;
    
    protected abstract void leaveGroup(SocketAddress mcastaddr, NetworkInterface netIf) throws IOException;
    
    protected abstract void close();
    
    protected int getLocalPort() {
        return localPort;
    }
    
    protected FileDescriptor getFileDescriptor() {
        return fd;
    }
}
