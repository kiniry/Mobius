package java.rmi;

import java.rmi.registry.*;
import java.net.MalformedURLException;
import java.net.URI;
import java.net.URISyntaxException;

public final class Naming {
    
    private Naming() {
        
    }
    
    public static Remote lookup(String name) throws NotBoundException, java.net.MalformedURLException, RemoteException {
        Naming$ParsedNamingURL parsed = parseURL(name);
        Registry registry = getRegistry(parsed);
        if (parsed.name == null) return registry;
        return registry.lookup(parsed.name);
    }
    
    public static void bind(String name, Remote obj) throws AlreadyBoundException, java.net.MalformedURLException, RemoteException {
        Naming$ParsedNamingURL parsed = parseURL(name);
        Registry registry = getRegistry(parsed);
        if (obj == null) throw new NullPointerException("cannot bind to null");
        registry.bind(parsed.name, obj);
    }
    
    public static void unbind(String name) throws RemoteException, NotBoundException, java.net.MalformedURLException {
        Naming$ParsedNamingURL parsed = parseURL(name);
        Registry registry = getRegistry(parsed);
        registry.unbind(parsed.name);
    }
    
    public static void rebind(String name, Remote obj) throws RemoteException, java.net.MalformedURLException {
        Naming$ParsedNamingURL parsed = parseURL(name);
        Registry registry = getRegistry(parsed);
        if (obj == null) throw new NullPointerException("cannot bind to null");
        registry.rebind(parsed.name, obj);
    }
    
    public static String[] list(String name) throws RemoteException, java.net.MalformedURLException {
        Naming$ParsedNamingURL parsed = parseURL(name);
        Registry registry = getRegistry(parsed);
        String prefix = "";
        if (parsed.port > 0 || !parsed.host.equals("")) prefix += "//" + parsed.host;
        if (parsed.port > 0) prefix += ":" + parsed.port;
        prefix += "/";
        String[] names = registry.list();
        for (int i = 0; i < names.length; i++) {
            names[i] = prefix + names[i];
        }
        return names;
    }
    
    private static Registry getRegistry(Naming$ParsedNamingURL parsed) throws RemoteException {
        return LocateRegistry.getRegistry(parsed.host, parsed.port);
    }
    
    private static Naming$ParsedNamingURL parseURL(String str) throws MalformedURLException {
        try {
            URI uri = new URI(str);
            if (uri.getFragment() != null) {
                throw new MalformedURLException("invalid character, \'#\', in URL name: " + str);
            } else if (uri.getQuery() != null) {
                throw new MalformedURLException("invalid character, \'?\', in URL name: " + str);
            } else if (uri.getUserInfo() != null) {
                throw new MalformedURLException("invalid character, \'@\', in URL host: " + str);
            }
            String scheme = uri.getScheme();
            if (scheme != null && !scheme.equals("rmi")) {
                throw new MalformedURLException("invalid URL scheme: " + str);
            }
            String name = uri.getPath();
            if (name != null) {
                if (name.startsWith("/")) {
                    name = name.substring(1);
                }
                if (name.length() == 0) {
                    name = null;
                }
            }
            String host = uri.getHost();
            if (host == null) {
                host = "";
                if (uri.getPort() == -1) {
                    String authority = uri.getAuthority();
                    if (authority != null && authority.startsWith(":")) {
                        authority = "localhost" + authority;
                        uri = new URI(null, authority, null, null, null);
                    }
                }
            }
            int port = uri.getPort();
            if (port == -1) {
                port = Registry.REGISTRY_PORT;
            }
            return new Naming$ParsedNamingURL(host, port, name);
        } catch (URISyntaxException ex) {
            throw (MalformedURLException)(MalformedURLException)new MalformedURLException("invalid URL string: " + str).initCause(ex);
        }
    }
    {
    }
}
