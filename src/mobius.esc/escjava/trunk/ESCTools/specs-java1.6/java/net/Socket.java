package java.net;

import java.io.InputStream;
import java.io.OutputStream;
import java.io.IOException;
import java.nio.channels.SocketChannel;
import java.security.AccessController;

public class Socket {
    private boolean created = false;
    private boolean bound = false;
    private boolean connected = false;
    private boolean closed = false;
    private Object closeLock = new Object();
    private boolean shutIn = false;
    private boolean shutOut = false;
    SocketImpl impl;
    private boolean oldImpl = false;
    
    public Socket() {
        
        setImpl();
    }
    
    public Socket(Proxy proxy) {
        
        if (proxy != null && proxy.type() == Proxy$Type.SOCKS) {
            SecurityManager security = System.getSecurityManager();
            InetSocketAddress epoint = (InetSocketAddress)(InetSocketAddress)proxy.address();
            if (security != null) {
                if (epoint.isUnresolved()) epoint = new InetSocketAddress(epoint.getHostName(), epoint.getPort());
                if (epoint.isUnresolved()) security.checkConnect(epoint.getHostName(), epoint.getPort()); else security.checkConnect(epoint.getAddress().getHostAddress(), epoint.getPort());
            }
            impl = new SocksSocketImpl(proxy);
            impl.setSocket(this);
        } else {
            if (proxy == Proxy.NO_PROXY) {
                if (factory == null) {
                    impl = new PlainSocketImpl();
                    impl.setSocket(this);
                } else setImpl();
            } else throw new IllegalArgumentException("Invalid Proxy");
        }
    }
    
    protected Socket(SocketImpl impl) throws SocketException {
        
        this.impl = impl;
        if (impl != null) {
            checkOldImpl();
            this.impl.setSocket(this);
        }
    }
    
    public Socket(String host, int port) throws UnknownHostException, IOException {
        this(host != null ? new InetSocketAddress(host, port) : new InetSocketAddress(InetAddress.getByName(null), port), new InetSocketAddress(0), true);
    }
    
    public Socket(InetAddress address, int port) throws IOException {
        this(address != null ? new InetSocketAddress(address, port) : null, new InetSocketAddress(0), true);
    }
    
    public Socket(String host, int port, InetAddress localAddr, int localPort) throws IOException {
        this(host != null ? new InetSocketAddress(host, port) : new InetSocketAddress(InetAddress.getByName(null), port), new InetSocketAddress(localAddr, localPort), true);
    }
    
    public Socket(InetAddress address, int port, InetAddress localAddr, int localPort) throws IOException {
        this(address != null ? new InetSocketAddress(address, port) : null, new InetSocketAddress(localAddr, localPort), true);
    }
    
    
    public Socket(String host, int port, boolean stream) throws IOException {
        this(host != null ? new InetSocketAddress(host, port) : new InetSocketAddress(InetAddress.getByName(null), port), new InetSocketAddress(0), stream);
    }
    
    
    public Socket(InetAddress host, int port, boolean stream) throws IOException {
        this(host != null ? new InetSocketAddress(host, port) : null, new InetSocketAddress(0), stream);
    }
    
    private Socket(SocketAddress address, SocketAddress localAddr, boolean stream) throws IOException {
        
        setImpl();
        if (address == null) throw new NullPointerException();
        try {
            createImpl(stream);
            if (localAddr == null) localAddr = new InetSocketAddress(0);
            bind(localAddr);
            if (address != null) connect(address);
        } catch (IOException e) {
            close();
            throw e;
        }
    }
    
    void createImpl(boolean stream) throws SocketException {
        if (impl == null) setImpl();
        try {
            impl.create(stream);
            created = true;
        } catch (IOException e) {
            throw new SocketException(e.getMessage());
        }
    }
    
    private void checkOldImpl() {
        if (impl == null) return;
        Boolean tmpBool = (Boolean)(Boolean)AccessController.doPrivileged(new Socket$1(this));
        oldImpl = tmpBool.booleanValue();
    }
    
    void setImpl() {
        if (factory != null) {
            impl = factory.createSocketImpl();
            checkOldImpl();
        } else {
            impl = new SocksSocketImpl();
        }
        if (impl != null) impl.setSocket(this);
    }
    
    SocketImpl getImpl() throws SocketException {
        if (!created) createImpl(true);
        return impl;
    }
    
    public void connect(SocketAddress endpoint) throws IOException {
        connect(endpoint, 0);
    }
    
    public void connect(SocketAddress endpoint, int timeout) throws IOException {
        if (endpoint == null) throw new IllegalArgumentException("connect: The address can\'t be null");
        if (timeout < 0) throw new IllegalArgumentException("connect: timeout can\'t be negative");
        if (isClosed()) throw new SocketException("Socket is closed");
        if (!oldImpl && isConnected()) throw new SocketException("already connected");
        if (!(endpoint instanceof InetSocketAddress)) throw new IllegalArgumentException("Unsupported address type");
        InetSocketAddress epoint = (InetSocketAddress)(InetSocketAddress)endpoint;
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            if (epoint.isUnresolved()) security.checkConnect(epoint.getHostName(), epoint.getPort()); else security.checkConnect(epoint.getAddress().getHostAddress(), epoint.getPort());
        }
        if (!created) createImpl(true);
        if (!oldImpl) impl.connect(epoint, timeout); else if (timeout == 0) {
            if (epoint.isUnresolved()) impl.connect(epoint.getAddress().getHostName(), epoint.getPort()); else impl.connect(epoint.getAddress(), epoint.getPort());
        } else throw new UnsupportedOperationException("SocketImpl.connect(addr, timeout)");
        connected = true;
        bound = true;
    }
    
    public void bind(SocketAddress bindpoint) throws IOException {
        if (isClosed()) throw new SocketException("Socket is closed");
        if (!oldImpl && isBound()) throw new SocketException("Already bound");
        if (bindpoint != null && (!(bindpoint instanceof InetSocketAddress))) throw new IllegalArgumentException("Unsupported address type");
        InetSocketAddress epoint = (InetSocketAddress)(InetSocketAddress)bindpoint;
        if (epoint != null && epoint.isUnresolved()) throw new SocketException("Unresolved address");
        if (bindpoint == null) getImpl().bind(InetAddress.anyLocalAddress(), 0); else getImpl().bind(epoint.getAddress(), epoint.getPort());
        bound = true;
    }
    
    final void postAccept() {
        connected = true;
        created = true;
        bound = true;
    }
    
    void setCreated() {
        created = true;
    }
    
    void setBound() {
        bound = true;
    }
    
    void setConnected() {
        connected = true;
    }
    
    public InetAddress getInetAddress() {
        if (!isConnected()) return null;
        try {
            return getImpl().getInetAddress();
        } catch (SocketException e) {
        }
        return null;
    }
    
    public InetAddress getLocalAddress() {
        if (!isBound()) return InetAddress.anyLocalAddress();
        InetAddress in = null;
        try {
            in = (InetAddress)(InetAddress)getImpl().getOption(SocketOptions.SO_BINDADDR);
            if (in.isAnyLocalAddress()) {
                in = InetAddress.anyLocalAddress();
            }
        } catch (Exception e) {
            in = InetAddress.anyLocalAddress();
        }
        return in;
    }
    
    public int getPort() {
        if (!isConnected()) return 0;
        try {
            return getImpl().getPort();
        } catch (SocketException e) {
        }
        return -1;
    }
    
    public int getLocalPort() {
        if (!isBound()) return -1;
        try {
            return getImpl().getLocalPort();
        } catch (SocketException e) {
        }
        return -1;
    }
    
    public SocketAddress getRemoteSocketAddress() {
        if (!isConnected()) return null;
        return new InetSocketAddress(getInetAddress(), getPort());
    }
    
    public SocketAddress getLocalSocketAddress() {
        if (!isBound()) return null;
        return new InetSocketAddress(getLocalAddress(), getLocalPort());
    }
    
    public SocketChannel getChannel() {
        return null;
    }
    
    public InputStream getInputStream() throws IOException {
        if (isClosed()) throw new SocketException("Socket is closed");
        if (!isConnected()) throw new SocketException("Socket is not connected");
        if (isInputShutdown()) throw new SocketException("Socket input is shutdown");
        final Socket s = this;
        InputStream is = null;
        try {
            is = (InputStream)(InputStream)AccessController.doPrivileged(new Socket$2(this));
        } catch (java.security.PrivilegedActionException e) {
            throw (IOException)(IOException)e.getException();
        }
        return is;
    }
    
    public OutputStream getOutputStream() throws IOException {
        if (isClosed()) throw new SocketException("Socket is closed");
        if (!isConnected()) throw new SocketException("Socket is not connected");
        if (isOutputShutdown()) throw new SocketException("Socket output is shutdown");
        final Socket s = this;
        OutputStream os = null;
        try {
            os = (OutputStream)(OutputStream)AccessController.doPrivileged(new Socket$3(this));
        } catch (java.security.PrivilegedActionException e) {
            throw (IOException)(IOException)e.getException();
        }
        return os;
    }
    
    public void setTcpNoDelay(boolean on) throws SocketException {
        if (isClosed()) throw new SocketException("Socket is closed");
        getImpl().setOption(SocketOptions.TCP_NODELAY, Boolean.valueOf(on));
    }
    
    public boolean getTcpNoDelay() throws SocketException {
        if (isClosed()) throw new SocketException("Socket is closed");
        return ((Boolean)(Boolean)getImpl().getOption(SocketOptions.TCP_NODELAY)).booleanValue();
    }
    
    public void setSoLinger(boolean on, int linger) throws SocketException {
        if (isClosed()) throw new SocketException("Socket is closed");
        if (!on) {
            getImpl().setOption(SocketOptions.SO_LINGER, new Boolean(on));
        } else {
            if (linger < 0) {
                throw new IllegalArgumentException("invalid value for SO_LINGER");
            }
            if (linger > 65535) linger = 65535;
            getImpl().setOption(SocketOptions.SO_LINGER, new Integer(linger));
        }
    }
    
    public int getSoLinger() throws SocketException {
        if (isClosed()) throw new SocketException("Socket is closed");
        Object o = getImpl().getOption(SocketOptions.SO_LINGER);
        if (o instanceof Integer) {
            return ((Integer)(Integer)o).intValue();
        } else {
            return -1;
        }
    }
    
    public void sendUrgentData(int data) throws IOException {
        if (!getImpl().supportsUrgentData()) {
            throw new SocketException("Urgent data not supported");
        }
        getImpl().sendUrgentData(data);
    }
    
    public void setOOBInline(boolean on) throws SocketException {
        if (isClosed()) throw new SocketException("Socket is closed");
        getImpl().setOption(SocketOptions.SO_OOBINLINE, Boolean.valueOf(on));
    }
    
    public boolean getOOBInline() throws SocketException {
        if (isClosed()) throw new SocketException("Socket is closed");
        return ((Boolean)(Boolean)getImpl().getOption(SocketOptions.SO_OOBINLINE)).booleanValue();
    }
    
    public synchronized void setSoTimeout(int timeout) throws SocketException {
        if (isClosed()) throw new SocketException("Socket is closed");
        if (timeout < 0) throw new IllegalArgumentException("timeout can\'t be negative");
        getImpl().setOption(SocketOptions.SO_TIMEOUT, new Integer(timeout));
    }
    
    public synchronized int getSoTimeout() throws SocketException {
        if (isClosed()) throw new SocketException("Socket is closed");
        Object o = getImpl().getOption(SocketOptions.SO_TIMEOUT);
        if (o instanceof Integer) {
            return ((Integer)(Integer)o).intValue();
        } else {
            return 0;
        }
    }
    
    public synchronized void setSendBufferSize(int size) throws SocketException {
        if (!(size > 0)) {
            throw new IllegalArgumentException("negative send size");
        }
        if (isClosed()) throw new SocketException("Socket is closed");
        getImpl().setOption(SocketOptions.SO_SNDBUF, new Integer(size));
    }
    
    public synchronized int getSendBufferSize() throws SocketException {
        if (isClosed()) throw new SocketException("Socket is closed");
        int result = 0;
        Object o = getImpl().getOption(SocketOptions.SO_SNDBUF);
        if (o instanceof Integer) {
            result = ((Integer)(Integer)o).intValue();
        }
        return result;
    }
    
    public synchronized void setReceiveBufferSize(int size) throws SocketException {
        if (size <= 0) {
            throw new IllegalArgumentException("invalid receive size");
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
    
    public void setKeepAlive(boolean on) throws SocketException {
        if (isClosed()) throw new SocketException("Socket is closed");
        getImpl().setOption(SocketOptions.SO_KEEPALIVE, Boolean.valueOf(on));
    }
    
    public boolean getKeepAlive() throws SocketException {
        if (isClosed()) throw new SocketException("Socket is closed");
        return ((Boolean)(Boolean)getImpl().getOption(SocketOptions.SO_KEEPALIVE)).booleanValue();
    }
    
    public void setTrafficClass(int tc) throws SocketException {
        if (tc < 0 || tc > 255) throw new IllegalArgumentException("tc is not in range 0 -- 255");
        if (isClosed()) throw new SocketException("Socket is closed");
        getImpl().setOption(SocketOptions.IP_TOS, new Integer(tc));
    }
    
    public int getTrafficClass() throws SocketException {
        return ((Integer)((Integer)getImpl().getOption(SocketOptions.IP_TOS))).intValue();
    }
    
    public void setReuseAddress(boolean on) throws SocketException {
        if (isClosed()) throw new SocketException("Socket is closed");
        getImpl().setOption(SocketOptions.SO_REUSEADDR, Boolean.valueOf(on));
    }
    
    public boolean getReuseAddress() throws SocketException {
        if (isClosed()) throw new SocketException("Socket is closed");
        return ((Boolean)((Boolean)getImpl().getOption(SocketOptions.SO_REUSEADDR))).booleanValue();
    }
    
    public synchronized void close() throws IOException {
        synchronized (closeLock) {
            if (isClosed()) return;
            if (created) impl.close();
            closed = true;
        }
    }
    
    public void shutdownInput() throws IOException {
        if (isClosed()) throw new SocketException("Socket is closed");
        if (!isConnected()) throw new SocketException("Socket is not connected");
        if (isInputShutdown()) throw new SocketException("Socket input is already shutdown");
        getImpl().shutdownInput();
        shutIn = true;
    }
    
    public void shutdownOutput() throws IOException {
        if (isClosed()) throw new SocketException("Socket is closed");
        if (!isConnected()) throw new SocketException("Socket is not connected");
        if (isOutputShutdown()) throw new SocketException("Socket output is already shutdown");
        getImpl().shutdownOutput();
        shutOut = true;
    }
    
    public String toString() {
        try {
            if (isConnected()) return "Socket[addr=" + getImpl().getInetAddress() + ",port=" + getImpl().getPort() + ",localport=" + getImpl().getLocalPort() + "]";
        } catch (SocketException e) {
        }
        return "Socket[unconnected]";
    }
    
    public boolean isConnected() {
        return connected || oldImpl;
    }
    
    public boolean isBound() {
        return bound || oldImpl;
    }
    
    public boolean isClosed() {
        synchronized (closeLock) {
            return closed;
        }
    }
    
    public boolean isInputShutdown() {
        return shutIn;
    }
    
    public boolean isOutputShutdown() {
        return shutOut;
    }
    private static SocketImplFactory factory = null;
    
    public static synchronized void setSocketImplFactory(SocketImplFactory fac) throws IOException {
        if (factory != null) {
            throw new SocketException("factory already defined");
        }
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkSetFactory();
        }
        factory = fac;
    }
    
    public void setPerformancePreferences(int connectionTime, int latency, int bandwidth) {
    }
}
