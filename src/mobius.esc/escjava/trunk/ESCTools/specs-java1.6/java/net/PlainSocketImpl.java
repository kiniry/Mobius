package java.net;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.FileDescriptor;
import sun.net.ConnectionResetException;

class PlainSocketImpl extends SocketImpl {
    int timeout;
    private int trafficClass;
    private boolean shut_rd = false;
    private boolean shut_wr = false;
    private SocketInputStream socketInputStream = null;
    private int fdUseCount = 0;
    private Object fdLock = new Object();
    private boolean closePending = false;
    private int CONNECTION_NOT_RESET = 0;
    private int CONNECTION_RESET_PENDING = 1;
    private int CONNECTION_RESET = 2;
    private int resetState;
    private Object resetLock = new Object();
    private FileDescriptor fd1;
    private InetAddress anyLocalBoundAddr = null;
    private int lastfd = -1;
    static {
        java.security.AccessController.doPrivileged(new sun.security.action.LoadLibraryAction("net"));
        initProto();
    }
    
    PlainSocketImpl() {
        
    }
    
    PlainSocketImpl(FileDescriptor fd) {
        
        this.fd = fd;
    }
    
    protected synchronized void create(boolean stream) throws IOException {
        fd = new FileDescriptor();
        fd1 = new FileDescriptor();
        socketCreate(stream);
        if (socket != null) socket.setCreated();
        if (serverSocket != null) serverSocket.setCreated();
    }
    
    protected void connect(String host, int port) throws UnknownHostException, IOException {
        IOException pending = null;
        try {
            InetAddress address = InetAddress.getByName(host);
            try {
                connectToAddress(address, port, timeout);
                return;
            } catch (IOException e) {
                pending = e;
            }
        } catch (UnknownHostException e) {
            pending = e;
        }
        close();
        throw pending;
    }
    
    protected void connect(InetAddress address, int port) throws IOException {
        this.port = port;
        this.address = address;
        try {
            connectToAddress(address, port, timeout);
            return;
        } catch (IOException e) {
            close();
            throw e;
        }
    }
    
    protected void connect(SocketAddress address, int timeout) throws IOException {
        if (address == null || !(address instanceof InetSocketAddress)) throw new IllegalArgumentException("unsupported address type");
        InetSocketAddress addr = (InetSocketAddress)(InetSocketAddress)address;
        if (addr.isUnresolved()) throw new UnknownHostException(addr.getHostName());
        this.port = addr.getPort();
        this.address = addr.getAddress();
        try {
            connectToAddress(this.address, port, timeout);
            return;
        } catch (IOException e) {
            close();
            throw e;
        }
    }
    
    private void connectToAddress(InetAddress address, int port, int timeout) throws IOException {
        if (address.isAnyLocalAddress()) {
            doConnect(InetAddress.getLocalHost(), port, timeout);
        } else {
            doConnect(address, port, timeout);
        }
    }
    
    public void setOption(int opt, Object val) throws SocketException {
        if (isClosedOrPending()) {
            throw new SocketException("Socket Closed");
        }
        boolean on = true;
        switch (opt) {
        case SO_LINGER: 
            if (val == null || (!(val instanceof Integer) && !(val instanceof Boolean))) throw new SocketException("Bad parameter for option");
            if (val instanceof Boolean) {
                on = false;
            }
            break;
        
        case SO_TIMEOUT: 
            if (val == null || (!(val instanceof Integer))) throw new SocketException("Bad parameter for SO_TIMEOUT");
            int tmp = ((Integer)(Integer)val).intValue();
            if (tmp < 0) throw new IllegalArgumentException("timeout < 0");
            timeout = tmp;
            break;
        
        case IP_TOS: 
            if (val == null || !(val instanceof Integer)) {
                throw new SocketException("bad argument for IP_TOS");
            }
            trafficClass = ((Integer)(Integer)val).intValue();
            break;
        
        case SO_BINDADDR: 
            throw new SocketException("Cannot re-bind socket");
        
        case TCP_NODELAY: 
            if (val == null || !(val instanceof Boolean)) throw new SocketException("bad parameter for TCP_NODELAY");
            on = ((Boolean)(Boolean)val).booleanValue();
            break;
        
        case SO_SNDBUF: 
        
        case SO_RCVBUF: 
            if (val == null || !(val instanceof Integer) || !(((Integer)(Integer)val).intValue() > 0)) {
                throw new SocketException("bad parameter for SO_SNDBUF or SO_RCVBUF");
            }
            break;
        
        case SO_KEEPALIVE: 
            if (val == null || !(val instanceof Boolean)) throw new SocketException("bad parameter for SO_KEEPALIVE");
            on = ((Boolean)(Boolean)val).booleanValue();
            break;
        
        case SO_OOBINLINE: 
            if (val == null || !(val instanceof Boolean)) throw new SocketException("bad parameter for SO_OOBINLINE");
            on = ((Boolean)(Boolean)val).booleanValue();
            break;
        
        case SO_REUSEADDR: 
            if (val == null || !(val instanceof Boolean)) throw new SocketException("bad parameter for SO_REUSEADDR");
            on = ((Boolean)(Boolean)val).booleanValue();
            break;
        
        default: 
            throw new SocketException("unrecognized TCP option: " + opt);
        
        }
        socketSetOption(opt, on, val);
    }
    
    public Object getOption(int opt) throws SocketException {
        if (isClosedOrPending()) {
            throw new SocketException("Socket Closed");
        }
        if (opt == SO_TIMEOUT) {
            return new Integer(timeout);
        }
        int ret = 0;
        switch (opt) {
        case TCP_NODELAY: 
            ret = socketGetOption(opt, null);
            return Boolean.valueOf(ret != -1);
        
        case SO_OOBINLINE: 
            ret = socketGetOption(opt, null);
            return Boolean.valueOf(ret != -1);
        
        case SO_LINGER: 
            ret = socketGetOption(opt, null);
            return (ret == -1) ? Boolean.FALSE : (Object)(new Integer(ret));
        
        case SO_REUSEADDR: 
            ret = socketGetOption(opt, null);
            return Boolean.valueOf(ret != -1);
        
        case SO_BINDADDR: 
            if (fd != null && fd1 != null) {
                return anyLocalBoundAddr;
            }
            InetAddressContainer in = new InetAddressContainer();
            ret = socketGetOption(opt, in);
            return in.addr;
        
        case SO_SNDBUF: 
        
        case SO_RCVBUF: 
            ret = socketGetOption(opt, null);
            return new Integer(ret);
        
        case IP_TOS: 
            ret = socketGetOption(opt, null);
            if (ret == -1) {
                return new Integer(trafficClass);
            } else {
                return new Integer(ret);
            }
        
        case SO_KEEPALIVE: 
            ret = socketGetOption(opt, null);
            return Boolean.valueOf(ret != -1);
        
        default: 
            return null;
        
        }
    }
    
    private synchronized void doConnect(InetAddress address, int port, int timeout) throws IOException {
        try {
            FileDescriptor fd = acquireFD();
            try {
                socketConnect(address, port, timeout);
                if (socket != null) {
                    socket.setBound();
                    socket.setConnected();
                }
            } finally {
                releaseFD();
            }
        } catch (IOException e) {
            close();
            throw e;
        }
    }
    
    protected synchronized void bind(InetAddress address, int lport) throws IOException {
        socketBind(address, lport);
        if (socket != null) socket.setBound();
        if (serverSocket != null) serverSocket.setBound();
        if (address.isAnyLocalAddress()) {
            anyLocalBoundAddr = address;
        }
    }
    
    protected synchronized void listen(int count) throws IOException {
        socketListen(count);
    }
    
    protected synchronized void accept(SocketImpl s) throws IOException {
        FileDescriptor fd = acquireFD();
        try {
            socketAccept(s);
        } finally {
            releaseFD();
        }
    }
    
    protected synchronized InputStream getInputStream() throws IOException {
        if (isClosedOrPending()) {
            throw new IOException("Socket Closed");
        }
        if (shut_rd) {
            throw new IOException("Socket input is shutdown");
        }
        if (socketInputStream == null) {
            socketInputStream = new SocketInputStream(this);
        }
        return socketInputStream;
    }
    
    void setInputStream(SocketInputStream in) {
        socketInputStream = in;
    }
    
    protected synchronized OutputStream getOutputStream() throws IOException {
        if (isClosedOrPending()) {
            throw new IOException("Socket Closed");
        }
        if (shut_wr) {
            throw new IOException("Socket output is shutdown");
        }
        return new SocketOutputStream(this);
    }
    
    protected synchronized int available() throws IOException {
        if (isClosedOrPending()) {
            throw new IOException("Stream closed.");
        }
        if (isConnectionReset()) {
            return 0;
        }
        int n = 0;
        try {
            n = socketAvailable();
            if (n == 0 && isConnectionResetPending()) {
                setConnectionReset();
            }
        } catch (ConnectionResetException exc1) {
            setConnectionResetPending();
            try {
                n = socketAvailable();
                if (n == 0) {
                    setConnectionReset();
                }
            } catch (ConnectionResetException exc2) {
            }
        }
        return n;
    }
    
    protected void close() throws IOException {
        synchronized (fdLock) {
            if (fd != null || fd1 != null) {
                if (fdUseCount == 0) {
                    if (closePending) {
                        return;
                    }
                    closePending = true;
                    try {
                        socketPreClose();
                    } finally {
                        socketClose();
                    }
                    fd = null;
                    fd1 = null;
                    return;
                } else {
                    if (!closePending) {
                        closePending = true;
                        fdUseCount--;
                        socketPreClose();
                    }
                }
            }
        }
    }
    
    protected void shutdownInput() throws IOException {
        if (fd != null) {
            socketShutdown(SHUT_RD);
            if (socketInputStream != null) {
                socketInputStream.setEOF(true);
            }
            shut_rd = true;
        }
    }
    
    protected void shutdownOutput() throws IOException {
        if (fd != null) {
            socketShutdown(SHUT_WR);
            shut_wr = true;
        }
    }
    
    protected boolean supportsUrgentData() {
        return true;
    }
    
    protected void sendUrgentData(int data) throws IOException {
        if (fd == null) {
            throw new IOException("Socket Closed");
        }
        socketSendUrgentData(data);
    }
    
    protected void finalize() throws IOException {
        close();
    }
    
    public final FileDescriptor acquireFD() {
        synchronized (fdLock) {
            fdUseCount++;
            return fd;
        }
    }
    
    public final void releaseFD() {
        synchronized (fdLock) {
            fdUseCount--;
            if (fdUseCount == -1) {
                if (fd != null) {
                    try {
                        socketClose();
                    } catch (IOException e) {
                    } finally {
                        fd = null;
                    }
                }
            }
        }
    }
    
    public boolean isConnectionReset() {
        synchronized (resetLock) {
            return (resetState == CONNECTION_RESET);
        }
    }
    
    public boolean isConnectionResetPending() {
        synchronized (resetLock) {
            return (resetState == CONNECTION_RESET_PENDING);
        }
    }
    
    public void setConnectionReset() {
        synchronized (resetLock) {
            resetState = CONNECTION_RESET;
        }
    }
    
    public void setConnectionResetPending() {
        synchronized (resetLock) {
            if (resetState == CONNECTION_NOT_RESET) {
                resetState = CONNECTION_RESET_PENDING;
            }
        }
    }
    
    public boolean isClosedOrPending() {
        synchronized (fdLock) {
            if (closePending || (fd == null && fd1 == null)) {
                return true;
            } else {
                return false;
            }
        }
    }
    
    public int getTimeout() {
        return timeout;
    }
    
    private void socketPreClose() throws IOException {
        socketClose0(true);
    }
    
    private void socketClose() throws IOException {
        socketClose0(false);
    }
    
    private native void socketCreate(boolean isServer) throws IOException;
    
    private native void socketConnect(InetAddress address, int port, int timeout) throws IOException;
    
    private native void socketBind(InetAddress address, int port) throws IOException;
    
    private native void socketListen(int count) throws IOException;
    
    private native void socketAccept(SocketImpl s) throws IOException;
    
    private native int socketAvailable() throws IOException;
    
    private native void socketClose0(boolean useDeferredClose) throws IOException;
    
    private native void socketShutdown(int howto) throws IOException;
    
    private static native void initProto();
    
    private native void socketSetOption(int cmd, boolean on, Object value) throws SocketException;
    
    private native int socketGetOption(int opt, Object iaContainerObj) throws SocketException;
    
    private native int socketGetOption1(int opt, Object iaContainerObj, FileDescriptor fd) throws SocketException;
    
    private native void socketSendUrgentData(int data) throws IOException;
    public static final int SHUT_RD = 0;
    public static final int SHUT_WR = 1;
}
