package com.sun.security.auth;

import java.io.*;
import java.lang.reflect.*;
import java.net.URL;
import java.util.*;
import java.security.CodeSource;
import java.security.IdentityScope;
import java.security.KeyStore;
import java.security.KeyStoreException;
import java.security.Permission;
import java.security.Permissions;
import java.security.PermissionCollection;
import java.security.Principal;
import java.security.UnresolvedPermission;
import java.security.Security;
import java.security.cert.Certificate;
import java.security.cert.X509Certificate;
import javax.security.auth.Subject;
import javax.security.auth.PrivateCredentialPermission;
import sun.security.util.PropertyExpander;


public class PolicyFile extends javax.security.auth.Policy {
    
    /*synthetic*/ static boolean access$100(PolicyFile x0) {
        return x0.initialized;
    }
    
    /*synthetic*/ static void access$000(PolicyFile x0) {
        x0.init();
    }
    static final java.util.ResourceBundle rb = (java.util.ResourceBundle)(ResourceBundle)java.security.AccessController.doPrivileged(new PolicyFile$1());
    private static final sun.security.util.Debug debug = sun.security.util.Debug.getInstance("policy", "\t[Auth Policy]");
    private static final String AUTH_POLICY = "java.security.auth.policy";
    private static final String SECURITY_MANAGER = "java.security.manager";
    private static final String AUTH_POLICY_URL = "auth.policy.url.";
    private Vector policyEntries;
    private Hashtable aliasMapping;
    private boolean initialized = false;
    private boolean expandProperties = true;
    private boolean ignoreIdentityScope = false;
    private static final Class[] PARAMS = {String.class, String.class};
    
    public PolicyFile() {
        
        String prop = System.getProperty(AUTH_POLICY);
        if (prop == null) {
            prop = System.getProperty(SECURITY_MANAGER);
        }
        if (prop != null) init();
    }
    
    private synchronized void init() {
        if (initialized) return;
        policyEntries = new Vector();
        aliasMapping = new Hashtable(11);
        initPolicyFile();
        initialized = true;
    }
    
    public synchronized void refresh() {
        java.lang.SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            sm.checkPermission(new javax.security.auth.AuthPermission("refreshPolicy"));
        }
        initialized = false;
        java.security.AccessController.doPrivileged(new PolicyFile$2(this));
    }
    
    private KeyStore initKeyStore(URL policyUrl, String keyStoreName, String keyStoreType) {
        if (keyStoreName != null) {
            try {
                URL keyStoreUrl = null;
                try {
                    keyStoreUrl = new URL(keyStoreName);
                } catch (java.net.MalformedURLException e) {
                    keyStoreUrl = new URL(policyUrl, keyStoreName);
                }
                if (debug != null) {
                    debug.println("reading keystore" + keyStoreUrl);
                }
                InputStream inStream = new BufferedInputStream(getInputStream(keyStoreUrl));
                KeyStore ks;
                if (keyStoreType != null) ks = KeyStore.getInstance(keyStoreType); else ks = KeyStore.getInstance(KeyStore.getDefaultType());
                ks.load(inStream, null);
                inStream.close();
                return ks;
            } catch (Exception e) {
                if (debug != null) {
                    e.printStackTrace();
                }
                return null;
            }
        }
        return null;
    }
    
    private void initPolicyFile() {
        String prop = Security.getProperty("policy.expandProperties");
        if (prop != null) expandProperties = prop.equalsIgnoreCase("true");
        String iscp = Security.getProperty("policy.ignoreIdentityScope");
        if (iscp != null) ignoreIdentityScope = iscp.equalsIgnoreCase("true");
        String allowSys = Security.getProperty("policy.allowSystemProperty");
        if ((allowSys != null) && allowSys.equalsIgnoreCase("true")) {
            String extra_policy = System.getProperty(AUTH_POLICY);
            if (extra_policy != null) {
                boolean overrideAll = false;
                if (extra_policy.startsWith("=")) {
                    overrideAll = true;
                    extra_policy = extra_policy.substring(1);
                }
                try {
                    extra_policy = PropertyExpander.expand(extra_policy);
                    URL policyURL;
                    ;
                    File policyFile = new File(extra_policy);
                    if (policyFile.exists()) {
                        policyURL = new URL("file:" + policyFile.getCanonicalPath());
                    } else {
                        policyURL = new URL(extra_policy);
                    }
                    if (debug != null) debug.println("reading " + policyURL);
                    init(policyURL);
                } catch (Exception e) {
                    if (debug != null) {
                        debug.println("caught exception: " + e);
                    }
                }
                if (overrideAll) {
                    if (debug != null) {
                        debug.println("overriding other policies!");
                    }
                    return;
                }
            }
        }
        int n = 1;
        boolean loaded_one = false;
        String policy_url;
        while ((policy_url = Security.getProperty(AUTH_POLICY_URL + n)) != null) {
            try {
                policy_url = PropertyExpander.expand(policy_url).replace(File.separatorChar, '/');
                if (debug != null) debug.println("reading " + policy_url);
                init(new URL(policy_url));
                loaded_one = true;
            } catch (Exception e) {
                if (debug != null) {
                    debug.println("error reading policy " + e);
                    e.printStackTrace();
                }
            }
            n++;
        }
        if (loaded_one == false) {
        }
    }
    private static IdentityScope scope = null;
    
    private boolean checkForTrustedIdentity(final Certificate cert) {
        return false;
    }
    
    private void init(URL policy) {
        PolicyParser pp = new PolicyParser(expandProperties);
        try {
            InputStreamReader isr = new InputStreamReader(getInputStream(policy));
            pp.read(isr);
            isr.close();
            KeyStore keyStore = initKeyStore(policy, pp.getKeyStoreUrl(), pp.getKeyStoreType());
            Enumeration enum_ = pp.grantElements();
            while (enum_.hasMoreElements()) {
                PolicyParser$GrantEntry ge = (PolicyParser$GrantEntry)(PolicyParser$GrantEntry)enum_.nextElement();
                addGrantEntry(ge, keyStore);
            }
        } catch (PolicyParser$ParsingException pe) {
            System.err.println(AUTH_POLICY + rb.getString(": error parsing ") + policy);
            System.err.println(AUTH_POLICY + rb.getString(": ") + pe.getMessage());
            if (debug != null) pe.printStackTrace();
        } catch (Exception e) {
            if (debug != null) {
                debug.println("error parsing " + policy);
                debug.println(e.toString());
                e.printStackTrace();
            }
        }
    }
    
    private InputStream getInputStream(URL url) throws IOException {
        if ("file".equals(url.getProtocol())) {
            String path = url.getFile().replace('/', File.separatorChar);
            return new FileInputStream(path);
        } else {
            return url.openStream();
        }
    }
    
    CodeSource getCodeSource(PolicyParser$GrantEntry ge, KeyStore keyStore) throws java.net.MalformedURLException {
        Certificate[] certs = null;
        if (ge.signedBy != null) {
            certs = getCertificates(keyStore, ge.signedBy);
            if (certs == null) {
                if (debug != null) {
                    debug.println(" no certs for alias " + ge.signedBy + ", ignoring.");
                }
                return null;
            }
        }
        URL location;
        if (ge.codeBase != null) location = new URL(ge.codeBase); else location = null;
        if (ge.principals == null || ge.principals.size() == 0) {
            return (canonicalizeCodebase(new CodeSource(location, certs), false));
        } else {
            return (canonicalizeCodebase(new SubjectCodeSource(null, ge.principals, location, certs), false));
        }
    }
    
    private void addGrantEntry(PolicyParser$GrantEntry ge, KeyStore keyStore) {
        if (debug != null) {
            debug.println("Adding policy entry: ");
            debug.println("  signedBy " + ge.signedBy);
            debug.println("  codeBase " + ge.codeBase);
            if (ge.principals != null && ge.principals.size() > 0) {
                ListIterator li = ge.principals.listIterator();
                while (li.hasNext()) {
                    PolicyParser$PrincipalEntry pppe = (PolicyParser$PrincipalEntry)(PolicyParser$PrincipalEntry)li.next();
                    debug.println("  " + pppe.principalClass + " " + pppe.principalName);
                }
            }
            debug.println();
        }
        try {
            CodeSource codesource = getCodeSource(ge, keyStore);
            if (codesource == null) return;
            PolicyFile$PolicyEntry entry = new PolicyFile$PolicyEntry(codesource);
            Enumeration enum_ = ge.permissionElements();
            while (enum_.hasMoreElements()) {
                PolicyParser$PermissionEntry pe = (PolicyParser$PermissionEntry)(PolicyParser$PermissionEntry)enum_.nextElement();
                try {
                    Permission perm;
                    if (pe.permission.equals("javax.security.auth.PrivateCredentialPermission") && pe.name.endsWith(" self")) {
                        perm = getInstance(pe.permission, pe.name + " \"self\"", pe.action);
                    } else {
                        perm = getInstance(pe.permission, pe.name, pe.action);
                    }
                    entry.add(perm);
                    if (debug != null) {
                        debug.println("  " + perm);
                    }
                } catch (ClassNotFoundException cnfe) {
                    Certificate[] certs;
                    if (pe.signedBy != null) certs = getCertificates(keyStore, pe.signedBy); else certs = null;
                    if (certs != null || pe.signedBy == null) {
                        Permission perm = new UnresolvedPermission(pe.permission, pe.name, pe.action, certs);
                        entry.add(perm);
                        if (debug != null) {
                            debug.println("  " + perm);
                        }
                    }
                } catch (java.lang.reflect.InvocationTargetException ite) {
                    System.err.println(AUTH_POLICY + rb.getString(": error adding Permission ") + pe.permission + rb.getString(" ") + ite.getTargetException());
                } catch (Exception e) {
                    System.err.println(AUTH_POLICY + rb.getString(": error adding Permission ") + pe.permission + rb.getString(" ") + e);
                }
            }
            policyEntries.addElement(entry);
        } catch (Exception e) {
            System.err.println(AUTH_POLICY + rb.getString(": error adding Entry ") + ge + rb.getString(" ") + e);
        }
        if (debug != null) debug.println();
    }
    
    private static final Permission getInstance(String type, String name, String actions) throws ClassNotFoundException, InstantiationException, IllegalAccessException, NoSuchMethodException, InvocationTargetException {
        Class pc = Class.forName(type);
        Constructor c = pc.getConstructor(PARAMS);
        return (Permission)(Permission)c.newInstance(new Object[]{name, actions});
    }
    
    Certificate[] getCertificates(KeyStore keyStore, String aliases) {
        Vector vcerts = null;
        StringTokenizer st = new StringTokenizer(aliases, ",");
        int n = 0;
        while (st.hasMoreTokens()) {
            String alias = st.nextToken().trim();
            n++;
            Certificate cert = null;
            cert = (Certificate)(Certificate)aliasMapping.get(alias);
            if (cert == null && keyStore != null) {
                try {
                    cert = keyStore.getCertificate(alias);
                } catch (KeyStoreException kse) {
                }
                if (cert != null) {
                    aliasMapping.put(alias, cert);
                    aliasMapping.put(cert, alias);
                }
            }
            if (cert != null) {
                if (vcerts == null) vcerts = new Vector();
                vcerts.addElement(cert);
            }
        }
        if (vcerts != null && n == vcerts.size()) {
            Certificate[] certs = new Certificate[vcerts.size()];
            vcerts.copyInto(certs);
            return certs;
        } else {
            return null;
        }
    }
    
    private final synchronized Enumeration elements() {
        return policyEntries.elements();
    }
    
    public PermissionCollection getPermissions(final Subject subject, final CodeSource codesource) {
        return (PermissionCollection)(PermissionCollection)java.security.AccessController.doPrivileged(new PolicyFile$3(this, subject, codesource));
    }
    
    PermissionCollection getPermissions(CodeSource codesource) {
        if (initialized) return getPermissions(new Permissions(), codesource); else return new PolicyPermissions(this, codesource);
    }
    
    Permissions getPermissions(final Permissions perms, final CodeSource cs) {
        if (!initialized) {
            init();
        }
        final CodeSource[] codesource = {null};
        codesource[0] = canonicalizeCodebase(cs, true);
        if (debug != null) {
            debug.println("evaluate(" + codesource[0] + ")\n");
        }
        for (int i = 0; i < policyEntries.size(); i++) {
            PolicyFile$PolicyEntry entry = (PolicyFile$PolicyEntry)(PolicyFile$PolicyEntry)policyEntries.elementAt(i);
            if (debug != null) {
                debug.println("PolicyFile CodeSource implies: " + entry.codesource.toString() + "\n\n" + "\t" + codesource[0].toString() + "\n\n");
            }
            if (entry.codesource.implies(codesource[0])) {
                for (int j = 0; j < entry.permissions.size(); j++) {
                    Permission p = (Permission)(Permission)entry.permissions.elementAt(j);
                    if (debug != null) {
                        debug.println("  granting " + p);
                    }
                    if (!addSelfPermissions(p, entry.codesource, codesource[0], perms)) {
                        perms.add(p);
                    }
                }
            }
        }
        if (!ignoreIdentityScope) {
            Certificate[] certs = codesource[0].getCertificates();
            if (certs != null) {
                for (int k = 0; k < certs.length; k++) {
                    if ((aliasMapping.get(certs[k]) == null) && checkForTrustedIdentity(certs[k])) {
                        perms.add(new java.security.AllPermission());
                    }
                }
            }
        }
        return perms;
    }
    
    private boolean addSelfPermissions(final Permission p, CodeSource entryCs, CodeSource accCs, Permissions perms) {
        if (!(p instanceof PrivateCredentialPermission)) return false;
        if (!(entryCs instanceof SubjectCodeSource)) return false;
        PrivateCredentialPermission pcp = (PrivateCredentialPermission)(PrivateCredentialPermission)p;
        SubjectCodeSource scs = (SubjectCodeSource)(SubjectCodeSource)entryCs;
        String[][] pPrincipals = pcp.getPrincipals();
        if (pPrincipals.length <= 0 || !pPrincipals[0][0].equalsIgnoreCase("self") || !pPrincipals[0][1].equalsIgnoreCase("self")) {
            return false;
        } else {
            if (scs.getPrincipals() == null) {
                return true;
            }
            ListIterator pli = scs.getPrincipals().listIterator();
            while (pli.hasNext()) {
                PolicyParser$PrincipalEntry principal = (PolicyParser$PrincipalEntry)(PolicyParser$PrincipalEntry)pli.next();
                String[][] principalInfo = getPrincipalInfo(principal, accCs);
                for (int i = 0; i < principalInfo.length; i++) {
                    PrivateCredentialPermission newPcp = new PrivateCredentialPermission(pcp.getCredentialClass() + " " + principalInfo[i][0] + " " + "\"" + principalInfo[i][1] + "\"", "read");
                    if (debug != null) {
                        debug.println("adding SELF permission: " + newPcp.toString());
                    }
                    perms.add(newPcp);
                }
            }
        }
        return true;
    }
    
    private String[][] getPrincipalInfo(PolicyParser$PrincipalEntry principal, final CodeSource accCs) {
        if (!principal.principalClass.equals(PolicyParser$PrincipalEntry.WILDCARD_CLASS) && !principal.principalName.equals(PolicyParser$PrincipalEntry.WILDCARD_NAME)) {
            String[][] info = new String[1][2];
            info[0][0] = principal.principalClass;
            info[0][1] = principal.principalName;
            return info;
        } else if (!principal.principalClass.equals(PolicyParser$PrincipalEntry.WILDCARD_CLASS) && principal.principalName.equals(PolicyParser$PrincipalEntry.WILDCARD_NAME)) {
            SubjectCodeSource scs = (SubjectCodeSource)(SubjectCodeSource)accCs;
            Set principalSet = null;
            try {
                Class pClass = Class.forName(principal.principalClass, false, ClassLoader.getSystemClassLoader());
                principalSet = scs.getSubject().getPrincipals(pClass);
            } catch (Exception e) {
                if (debug != null) {
                    debug.println("problem finding Principal Class " + "when expanding SELF permission: " + e.toString());
                }
            }
            if (principalSet == null) {
                return new String[0][0];
            }
            String[][] info = new String[principalSet.size()][2];
            java.util.Iterator pIterator = principalSet.iterator();
            int i = 0;
            while (pIterator.hasNext()) {
                Principal p = (Principal)(Principal)pIterator.next();
                info[i][0] = p.getClass().getName();
                info[i][1] = p.getName();
                i++;
            }
            return info;
        } else {
            SubjectCodeSource scs = (SubjectCodeSource)(SubjectCodeSource)accCs;
            Set principalSet = scs.getSubject().getPrincipals();
            String[][] info = new String[principalSet.size()][2];
            java.util.Iterator pIterator = principalSet.iterator();
            int i = 0;
            while (pIterator.hasNext()) {
                Principal p = (Principal)(Principal)pIterator.next();
                info[i][0] = p.getClass().getName();
                info[i][1] = p.getName();
                i++;
            }
            return info;
        }
    }
    
    Certificate[] getSignerCertificates(CodeSource cs) {
        Certificate[] certs = null;
        if ((certs = cs.getCertificates()) == null) return null;
        for (int i = 0; i < certs.length; i++) {
            if (!(certs[i] instanceof X509Certificate)) return cs.getCertificates();
        }
        int i = 0;
        int count = 0;
        while (i < certs.length) {
            count++;
            while (((i + 1) < certs.length) && ((X509Certificate)(X509Certificate)certs[i]).getIssuerDN().equals(((X509Certificate)(X509Certificate)certs[i + 1]).getSubjectDN())) {
                i++;
            }
            i++;
        }
        if (count == certs.length) return certs;
        ArrayList userCertList = new ArrayList();
        i = 0;
        while (i < certs.length) {
            userCertList.add(certs[i]);
            while (((i + 1) < certs.length) && ((X509Certificate)(X509Certificate)certs[i]).getIssuerDN().equals(((X509Certificate)(X509Certificate)certs[i + 1]).getSubjectDN())) {
                i++;
            }
            i++;
        }
        Certificate[] userCerts = new Certificate[userCertList.size()];
        userCertList.toArray(userCerts);
        return userCerts;
    }
    
    private CodeSource canonicalizeCodebase(CodeSource cs, boolean extractSignerCerts) {
        CodeSource canonCs = cs;
        if (cs.getLocation() != null && cs.getLocation().getProtocol().equalsIgnoreCase("file")) {
            try {
                String path = cs.getLocation().getFile().replace('/', File.separatorChar);
                URL csUrl = null;
                if (path.endsWith("*")) {
                    path = path.substring(0, path.length() - 1);
                    boolean appendFileSep = false;
                    if (path.endsWith(File.separator)) appendFileSep = true;
                    if (path.equals("")) {
                        path = System.getProperty("user.dir");
                    }
                    File f = new File(path);
                    path = f.getCanonicalPath();
                    StringBuffer sb = new StringBuffer(path);
                    if (!path.endsWith(File.separator) && (appendFileSep || f.isDirectory())) sb.append(File.separatorChar);
                    sb.append('*');
                    path = sb.toString();
                } else {
                    path = new File(path).getCanonicalPath();
                }
                csUrl = new File(path).toURL();
                if (cs instanceof SubjectCodeSource) {
                    SubjectCodeSource scs = (SubjectCodeSource)(SubjectCodeSource)cs;
                    if (extractSignerCerts) {
                        canonCs = new SubjectCodeSource(scs.getSubject(), scs.getPrincipals(), csUrl, getSignerCertificates(scs));
                    } else {
                        canonCs = new SubjectCodeSource(scs.getSubject(), scs.getPrincipals(), csUrl, scs.getCertificates());
                    }
                } else {
                    if (extractSignerCerts) {
                        canonCs = new CodeSource(csUrl, getSignerCertificates(cs));
                    } else {
                        canonCs = new CodeSource(csUrl, cs.getCertificates());
                    }
                }
            } catch (IOException ioe) {
                if (extractSignerCerts) {
                    if (!(cs instanceof SubjectCodeSource)) {
                        canonCs = new CodeSource(cs.getLocation(), getSignerCertificates(cs));
                    } else {
                        SubjectCodeSource scs = (SubjectCodeSource)(SubjectCodeSource)cs;
                        canonCs = new SubjectCodeSource(scs.getSubject(), scs.getPrincipals(), scs.getLocation(), getSignerCertificates(scs));
                    }
                }
            }
        } else {
            if (extractSignerCerts) {
                if (!(cs instanceof SubjectCodeSource)) {
                    canonCs = new CodeSource(cs.getLocation(), getSignerCertificates(cs));
                } else {
                    SubjectCodeSource scs = (SubjectCodeSource)(SubjectCodeSource)cs;
                    canonCs = new SubjectCodeSource(scs.getSubject(), scs.getPrincipals(), scs.getLocation(), getSignerCertificates(scs));
                }
            }
        }
        return canonCs;
    }
    {
    }
}
