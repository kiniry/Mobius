package java.net;

import java.io.FileDescriptor;
import java.io.IOException;
import java.nio.channels.ServerSocketChannel;
import java.security.AccessController;

public class ServerSocket {
    
    /*synthetic*/ static SocketImpl access$000(ServerSocket x0) {
        return x0.impl;
    }
    private boolean created = false;
    private boolean bound = false;
    private boolean closed = false;
    private Object closeLock = new Object();
    private SocketImpl impl;
    private boolean oldImpl = false;
    
    public ServerSocket() throws IOException {
        
        setImpl();
    }
    
    public ServerSocket(int port) throws IOException {
        this(port, 50, null);
    }
    
    public ServerSocket(int port, int backlog) throws IOException {
        this(port, backlog, null);
    }
    
    public ServerSocket(int port, int backlog, InetAddress bindAddr) throws IOException {
        
        setImpl();
        if (port < 0 || port > 65535) throw new IllegalArgumentException("Port value out of range: " + port);
        if (backlog < 1) backlog = 50;
        try {
            bind(new InetSocketAddress(bindAddr, port), backlog);
        } catch (SecurityException e) {
            close();
            throw e;
        } catch (IOException e) {
            close();
            throw e;
        }
    }
    
    SocketImpl getImpl() throws SocketException {
        if (!created) createImpl();
        return impl;
    }
    
    private void checkOldImpl() {
        if (impl == null) return;
        try {
            AccessController.doPrivileged(new ServerSocket$1(this));
        } catch (java.security.PrivilegedActionException e) {
            oldImpl = true;
        }
    }
    
    private void setImpl() {
        if (factory != null) {
            impl = factory.createSocketImpl();
            checkOldImpl();
        } else {
            impl = new SocksSocketImpl();
        }
        if (impl != null) impl.setServerSocket(this);
    }
    
    void createImpl() throws SocketException {
        if (impl == null) setImpl();
        try {
            impl.create(true);
            created = true;
        } catch (IOException e) {
            throw new SocketException(e.getMessage());
        }
    }
    
    public void bind(SocketAddress endpoint) throws IOException {
        bind(endpoint, 50);
    }
    
    public void bind(SocketAddress endpoint, int backlog) throws IOException {
        if (isClosed()) throw new SocketException("Socket is closed");
        if (!oldImpl && isBound()) throw new SocketException("Already bound");
        if (endpoint == null) endpoint = new InetSocketAddress(0);
        if (!(endpoint instanceof InetSocketAddress)) throw new IllegalArgumentException("Unsupported address type");
        InetSocketAddress epoint = (InetSocketAddress)(InetSocketAddress)endpoint;
        if (epoint.isUnresolved()) throw new SocketException("Unresolved address");
        if (backlog < 1) backlog = 50;
        try {
            SecurityManager security = System.getSecurityManager();
            if (security != null) security.checkListen(epoint.getPort());
            getImpl().bind(epoint.getAddress(), epoint.getPort());
            getImpl().listen(backlog);
            bound = true;
        } catch (SecurityException e) {
            bound = false;
            throw e;
        } catch (IOException e) {
            bound = false;
            throw e;
        }
    }
    
    public InetAddress getInetAddress() {
        if (!isBound()) return null;
        try {
            return getImpl().getInetAddress();
        } catch (SocketException e) {
        }
        return null;
    }
    
    public int getLocalPort() {
        if (!isBound()) return -1;
        try {
            return getImpl().getLocalPort();
        } catch (SocketException e) {
        }
        return -1;
    }
    
    public SocketAddress getLocalSocketAddress() {
        if (!isBound()) return null;
        return new InetSocketAddress(getInetAddress(), getLocalPort());
    }
    
    public Socket accept() throws IOException {
        if (isClosed()) throw new SocketException("Socket is closed");
        if (!isBound()) throw new SocketException("Socket is not bound yet");
        Socket s = new Socket((SocketImpl)null);
        implAccept(s);
        return s;
    }
    
    protected final void implAccept(Socket s) throws IOException {
        SocketImpl si = null;
        try {
            if (s.impl == null) s.setImpl();
            si = s.impl;
            s.impl = null;
            si.address = new InetAddress();
            si.fd = new FileDescriptor();
            getImpl().accept(si);
            SecurityManager security = System.getSecurityManager();
            if (security != null) {
                security.checkAccept(si.getInetAddress().getHostAddress(), si.getPort());
            }
        } catch (IOException e) {
            if (si != null) si.reset();
            s.impl = si;
            throw e;
        } catch (SecurityException e) {
            if (si != null) si.reset();
            s.impl = si;
            throw e;
        }
        s.impl = si;
        s.postAccept();
    }
    
    public void close() throws IOException {
        synchronized (closeLock) {
            if (isClosed()) return;
            if (created) impl.close();
            closed = true;
        }
    }
    
    public ServerSocketChannel getChannel() {
        return null;
    }
    
    public boolean isBound() {
        return bound || oldImpl;
    }
    
    public boolean isClosed() {
        synchronized (closeLock) {
            return closed;
        }
    }
    
    public synchronized void setSoTimeout(int timeout) throws SocketException {
        if (isClosed()) throw new SocketException("Socket is closed");
        getImpl().setOption(SocketOptions.SO_TIMEOUT, new Integer(timeout));
    }
    
    public synchronized int getSoTimeout() throws IOException {
        if (isClosed()) throw new SocketException("Socket is closed");
        Object o = getImpl().getOption(SocketOptions.SO_TIMEOUT);
        if (o instanceof Integer) {
            return ((Integer)(Integer)o).intValue();
        } else {
            return 0;
        }
    }
    
    public void setReuseAddress(boolean on) throws SocketException {
        if (isClosed()) throw new SocketException("Socket is closed");
        getImpl().setOption(SocketOptions.SO_REUSEADDR, Boolean.valueOf(on));
    }
    
    public boolean getReuseAddress() throws SocketException {
        if (isClosed()) throw new SocketException("Socket is closed");
        return ((Boolean)((Boolean)getImpl().getOption(SocketOptions.SO_REUSEADDR))).booleanValue();
    }
    
    public String toString() {
        if (!isBound()) return "ServerSocket[unbound]";
        return "ServerSocket[addr=" + impl.getInetAddress() + ",port=" + impl.getPort() + ",localport=" + impl.getLocalPort() + "]";
    }
    
    void setBound() {
        bound = true;
    }
    
    void setCreated() {
        created = true;
    }
    private static SocketImplFactory factory = null;
    
    public static synchronized void setSocketFactory(SocketImplFactory fac) throws IOException {
        if (factory != null) {
            throw new SocketException("factory already defined");
        }
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkSetFactory();
        }
        factory = fac;
    }
    
    public synchronized void setReceiveBufferSize(int size) throws SocketException {
        if (!(size > 0)) {
            throw new IllegalArgumentException("negative receive size");
        }
        if (isClosed()) throw new SocketException("Socket is closed");
        getImpl().setOption(SocketOptions.SO_RCVBUF, new Integer(size));
    }
    
    public synchronized int getReceiveBufferSize() throws SocketException {
        if (isClosed()) throw new SocketException("Socket is closed");
        int result = 0;
        Object o = getImpl().getOption(SocketOptions.SO_RCVBUF);
        if (o instanceof Integer) {
            result = ((Integer)(Integer)o).intValue();
        }
        return result;
    }
    
    public void setPerformancePreferences(int connectionTime, int latency, int bandwidth) {
    }
}
