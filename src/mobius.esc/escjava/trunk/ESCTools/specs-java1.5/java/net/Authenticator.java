package java.net;

public abstract class Authenticator {
    
    public Authenticator() {
        
    }
    private static Authenticator theAuthenticator;
    private String requestingHost;
    private InetAddress requestingSite;
    private int requestingPort;
    private String requestingProtocol;
    private String requestingPrompt;
    private String requestingScheme;
    private URL requestingURL;
    private Authenticator$RequestorType requestingAuthType;
    {
    }
    
    private void reset() {
        requestingHost = null;
        requestingSite = null;
        requestingPort = -1;
        requestingProtocol = null;
        requestingPrompt = null;
        requestingScheme = null;
        requestingURL = null;
        requestingAuthType = Authenticator$RequestorType.SERVER;
    }
    
    public static synchronized void setDefault(Authenticator a) {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            NetPermission setDefaultPermission = new NetPermission("setDefaultAuthenticator");
            sm.checkPermission(setDefaultPermission);
        }
        theAuthenticator = a;
    }
    
    public static PasswordAuthentication requestPasswordAuthentication(InetAddress addr, int port, String protocol, String prompt, String scheme) {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            NetPermission requestPermission = new NetPermission("requestPasswordAuthentication");
            sm.checkPermission(requestPermission);
        }
        Authenticator a = theAuthenticator;
        if (a == null) {
            return null;
        } else {
            synchronized (a) {
                a.reset();
                a.requestingSite = addr;
                a.requestingPort = port;
                a.requestingProtocol = protocol;
                a.requestingPrompt = prompt;
                a.requestingScheme = scheme;
                return a.getPasswordAuthentication();
            }
        }
    }
    
    public static PasswordAuthentication requestPasswordAuthentication(String host, InetAddress addr, int port, String protocol, String prompt, String scheme) {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            NetPermission requestPermission = new NetPermission("requestPasswordAuthentication");
            sm.checkPermission(requestPermission);
        }
        Authenticator a = theAuthenticator;
        if (a == null) {
            return null;
        } else {
            synchronized (a) {
                a.reset();
                a.requestingHost = host;
                a.requestingSite = addr;
                a.requestingPort = port;
                a.requestingProtocol = protocol;
                a.requestingPrompt = prompt;
                a.requestingScheme = scheme;
                return a.getPasswordAuthentication();
            }
        }
    }
    
    public static PasswordAuthentication requestPasswordAuthentication(String host, InetAddress addr, int port, String protocol, String prompt, String scheme, URL url, Authenticator$RequestorType reqType) {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            NetPermission requestPermission = new NetPermission("requestPasswordAuthentication");
            sm.checkPermission(requestPermission);
        }
        Authenticator a = theAuthenticator;
        if (a == null) {
            return null;
        } else {
            synchronized (a) {
                a.reset();
                a.requestingHost = host;
                a.requestingSite = addr;
                a.requestingPort = port;
                a.requestingProtocol = protocol;
                a.requestingPrompt = prompt;
                a.requestingScheme = scheme;
                a.requestingURL = url;
                a.requestingAuthType = reqType;
                return a.getPasswordAuthentication();
            }
        }
    }
    
    protected final String getRequestingHost() {
        return requestingHost;
    }
    
    protected final InetAddress getRequestingSite() {
        return requestingSite;
    }
    
    protected final int getRequestingPort() {
        return requestingPort;
    }
    
    protected final String getRequestingProtocol() {
        return requestingProtocol;
    }
    
    protected final String getRequestingPrompt() {
        return requestingPrompt;
    }
    
    protected final String getRequestingScheme() {
        return requestingScheme;
    }
    
    protected PasswordAuthentication getPasswordAuthentication() {
        return null;
    }
    
    protected URL getRequestingURL() {
        return requestingURL;
    }
    
    protected Authenticator$RequestorType getRequestorType() {
        return requestingAuthType;
    }
}
