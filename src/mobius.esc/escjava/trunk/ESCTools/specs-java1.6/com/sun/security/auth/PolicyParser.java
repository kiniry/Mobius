package com.sun.security.auth;

import java.io.*;
import java.util.Enumeration;
import java.util.LinkedList;
import java.util.Vector;
import sun.security.util.PropertyExpander;


class PolicyParser {
    
    /*synthetic*/ static java.util.ResourceBundle access$000() {
        return rb;
    }
    private static final java.util.ResourceBundle rb = (java.util.ResourceBundle)(java.util.ResourceBundle)java.security.AccessController.doPrivileged(new PolicyParser$1());
    private Vector grantEntries;
    private static final sun.security.util.Debug debug = sun.security.util.Debug.getInstance("parser", "\t[Auth Policy Parser]");
    private StreamTokenizer st;
    private int lookahead;
    private int linenum;
    private boolean expandProp = false;
    private String keyStoreUrlString = null;
    private String keyStoreType = null;
    
    private String expand(String value) throws PropertyExpander$ExpandException {
        if (expandProp) return PropertyExpander.expand(value); else return value;
    }
    
    public PolicyParser() {
        
        grantEntries = new Vector();
    }
    
    public PolicyParser(boolean expandProp) {
        this();
        this.expandProp = expandProp;
    }
    
    public void read(Reader policy) throws PolicyParser$ParsingException, IOException {
        if (!(policy instanceof BufferedReader)) {
            policy = new BufferedReader(policy);
        }
        st = new StreamTokenizer(policy);
        st.resetSyntax();
        st.wordChars('a', 'z');
        st.wordChars('A', 'Z');
        st.wordChars('.', '.');
        st.wordChars('0', '9');
        st.wordChars('_', '_');
        st.wordChars('$', '$');
        st.wordChars(128 + 32, 255);
        st.whitespaceChars(0, ' ');
        st.commentChar('/');
        st.quoteChar('\'');
        st.quoteChar('\"');
        st.lowerCaseMode(false);
        st.ordinaryChar('/');
        st.slashSlashComments(true);
        st.slashStarComments(true);
        lookahead = st.nextToken();
        while (lookahead != StreamTokenizer.TT_EOF) {
            if (peek("grant")) {
                PolicyParser$GrantEntry ge = parseGrantEntry();
                if (ge != null) add(ge);
            } else if (peek("keystore") && keyStoreUrlString == null) {
                parseKeyStoreEntry();
            } else {
            }
            match(";");
        }
    }
    
    public void add(PolicyParser$GrantEntry ge) {
        grantEntries.addElement(ge);
    }
    
    public void replace(PolicyParser$GrantEntry origGe, PolicyParser$GrantEntry newGe) {
        grantEntries.setElementAt(newGe, grantEntries.indexOf(origGe));
    }
    
    public boolean remove(PolicyParser$GrantEntry ge) {
        return grantEntries.removeElement(ge);
    }
    
    public String getKeyStoreUrl() {
        try {
            if (keyStoreUrlString != null && keyStoreUrlString.length() != 0) {
                return expand(keyStoreUrlString).replace(File.separatorChar, '/');
            }
        } catch (PropertyExpander$ExpandException peee) {
            return null;
        }
        return null;
    }
    
    public void setKeyStoreUrl(String url) {
        keyStoreUrlString = url;
    }
    
    public String getKeyStoreType() {
        return keyStoreType;
    }
    
    public void setKeyStoreType(String type) {
        keyStoreType = type;
    }
    
    public Enumeration grantElements() {
        return grantEntries.elements();
    }
    
    public void write(Writer policy) {
        PrintWriter out = new PrintWriter(new BufferedWriter(policy));
        Enumeration enum_ = grantElements();
        out.println("/* AUTOMATICALLY GENERATED ON " + (new java.util.Date()) + "*/");
        out.println("/* DO NOT EDIT */");
        out.println();
        if (keyStoreUrlString != null) {
            writeKeyStoreEntry(out);
        }
        while (enum_.hasMoreElements()) {
            PolicyParser$GrantEntry ge = (PolicyParser$GrantEntry)(PolicyParser$GrantEntry)enum_.nextElement();
            ge.write(out);
            out.println();
        }
        out.flush();
    }
    
    private void parseKeyStoreEntry() throws PolicyParser$ParsingException, IOException {
        match("keystore");
        keyStoreUrlString = match("quoted string");
        if (!peek(",")) {
            return;
        }
        match(",");
        if (peek("\"")) {
            keyStoreType = match("quoted string");
        } else {
            throw new PolicyParser$ParsingException(st.lineno(), rb.getString("expected keystore type"));
        }
    }
    
    private void writeKeyStoreEntry(PrintWriter out) {
        out.print("keystore \"");
        out.print(keyStoreUrlString);
        out.print('\"');
        if (keyStoreType != null && keyStoreType.length() > 0) out.print(", \"" + keyStoreType + "\"");
        out.println(";");
        out.println();
    }
    
    private PolicyParser$GrantEntry parseGrantEntry() throws PolicyParser$ParsingException, IOException {
        PolicyParser$GrantEntry e = new PolicyParser$GrantEntry();
        LinkedList principals = null;
        boolean ignoreEntry = false;
        match("grant");
        while (!peek("{")) {
            if (peekAndMatch("Codebase")) {
                e.codeBase = match("quoted string");
                peekAndMatch(",");
            } else if (peekAndMatch("SignedBy")) {
                e.signedBy = match("quoted string");
                peekAndMatch(",");
            } else if (peekAndMatch("Principal")) {
                if (principals == null) {
                    principals = new LinkedList();
                }
                String principalClass;
                if (peek("*")) {
                    match("*");
                    principalClass = PolicyParser$PrincipalEntry.WILDCARD_CLASS;
                } else {
                    principalClass = match("principal type");
                }
                String principalName;
                if (peek("*")) {
                    match("*");
                    principalName = PolicyParser$PrincipalEntry.WILDCARD_NAME;
                } else {
                    principalName = match("quoted string");
                }
                if (principalClass.equals(PolicyParser$PrincipalEntry.WILDCARD_CLASS) && !principalName.equals(PolicyParser$PrincipalEntry.WILDCARD_NAME)) {
                    if (debug != null) debug.println("disallowing principal that has WILDCARD class but no WILDCARD name");
                    throw new PolicyParser$ParsingException(st.lineno(), rb.getString("can not specify Principal with a ") + rb.getString("wildcard class without a wildcard name"));
                }
                try {
                    principalName = expand(principalName);
                    principals.add(new PolicyParser$PrincipalEntry(principalClass, principalName));
                } catch (PropertyExpander$ExpandException peee) {
                    if (debug != null) debug.println("principal name expansion failed: " + principalName);
                    ignoreEntry = true;
                }
                peekAndMatch(",");
            } else {
                throw new PolicyParser$ParsingException(st.lineno(), rb.getString("expected codeBase or SignedBy"));
            }
        }
        if (principals == null) {
            throw new PolicyParser$ParsingException(st.lineno(), rb.getString("only Principal-based grant entries permitted"));
        }
        e.principals = principals;
        match("{");
        while (!peek("}")) {
            if (peek("Permission")) {
                try {
                    PolicyParser$PermissionEntry pe = parsePermissionEntry();
                    e.add(pe);
                } catch (PropertyExpander$ExpandException peee) {
                    skipEntry();
                }
                match(";");
            } else {
                throw new PolicyParser$ParsingException(st.lineno(), rb.getString("expected permission entry"));
            }
        }
        match("}");
        try {
            if (e.codeBase != null) e.codeBase = expand(e.codeBase).replace(File.separatorChar, '/');
            e.signedBy = expand(e.signedBy);
        } catch (PropertyExpander$ExpandException peee) {
            return null;
        }
        return (ignoreEntry == true) ? null : e;
    }
    
    private PolicyParser$PermissionEntry parsePermissionEntry() throws PolicyParser$ParsingException, IOException, PropertyExpander$ExpandException {
        PolicyParser$PermissionEntry e = new PolicyParser$PermissionEntry();
        match("Permission");
        e.permission = match("permission type");
        if (peek("\"")) {
            e.name = expand(match("quoted string"));
        }
        if (!peek(",")) {
            return e;
        }
        match(",");
        if (peek("\"")) {
            e.action = expand(match("quoted string"));
            if (!peek(",")) {
                return e;
            }
            match(",");
        }
        if (peekAndMatch("SignedBy")) {
            e.signedBy = expand(match("quoted string"));
        }
        return e;
    }
    
    private boolean peekAndMatch(String expect) throws PolicyParser$ParsingException, IOException {
        if (peek(expect)) {
            match(expect);
            return true;
        } else {
            return false;
        }
    }
    
    private boolean peek(String expect) {
        boolean found = false;
        switch (lookahead) {
        case StreamTokenizer.TT_WORD: 
            if (expect.equalsIgnoreCase(st.sval)) found = true;
            break;
        
        case ',': 
            if (expect.equalsIgnoreCase(",")) found = true;
            break;
        
        case '{': 
            if (expect.equalsIgnoreCase("{")) found = true;
            break;
        
        case '}': 
            if (expect.equalsIgnoreCase("}")) found = true;
            break;
        
        case '\"': 
            if (expect.equalsIgnoreCase("\"")) found = true;
            break;
        
        case '*': 
            if (expect.equalsIgnoreCase("*")) found = true;
            break;
        
        default: 
        
        }
        return found;
    }
    
    private String match(String expect) throws PolicyParser$ParsingException, IOException {
        String value = null;
        switch (lookahead) {
        case StreamTokenizer.TT_NUMBER: 
            throw new PolicyParser$ParsingException(st.lineno(), expect, rb.getString("number ") + String.valueOf(st.nval));
        
        case StreamTokenizer.TT_EOF: 
            throw new PolicyParser$ParsingException(rb.getString("expected ") + expect + rb.getString(", read end of file"));
        
        case StreamTokenizer.TT_WORD: 
            if (expect.equalsIgnoreCase(st.sval)) {
                lookahead = st.nextToken();
            } else if (expect.equalsIgnoreCase("permission type")) {
                value = st.sval;
                lookahead = st.nextToken();
            } else if (expect.equalsIgnoreCase("principal type")) {
                value = st.sval;
                lookahead = st.nextToken();
            } else {
                throw new PolicyParser$ParsingException(st.lineno(), expect, st.sval);
            }
            break;
        
        case '\"': 
            if (expect.equalsIgnoreCase("quoted string")) {
                value = st.sval;
                lookahead = st.nextToken();
            } else if (expect.equalsIgnoreCase("permission type")) {
                value = st.sval;
                lookahead = st.nextToken();
            } else if (expect.equalsIgnoreCase("principal type")) {
                value = st.sval;
                lookahead = st.nextToken();
            } else {
                throw new PolicyParser$ParsingException(st.lineno(), expect, st.sval);
            }
            break;
        
        case ',': 
            if (expect.equalsIgnoreCase(",")) lookahead = st.nextToken(); else throw new PolicyParser$ParsingException(st.lineno(), expect, ",");
            break;
        
        case '{': 
            if (expect.equalsIgnoreCase("{")) lookahead = st.nextToken(); else throw new PolicyParser$ParsingException(st.lineno(), expect, "{");
            break;
        
        case '}': 
            if (expect.equalsIgnoreCase("}")) lookahead = st.nextToken(); else throw new PolicyParser$ParsingException(st.lineno(), expect, "}");
            break;
        
        case ';': 
            if (expect.equalsIgnoreCase(";")) lookahead = st.nextToken(); else throw new PolicyParser$ParsingException(st.lineno(), expect, ";");
            break;
        
        case '*': 
            if (expect.equalsIgnoreCase("*")) lookahead = st.nextToken(); else throw new PolicyParser$ParsingException(st.lineno(), expect, "*");
            break;
        
        default: 
            throw new PolicyParser$ParsingException(st.lineno(), expect, new String(new char[]{(char)lookahead}));
        
        }
        return value;
    }
    
    private void skipEntry() throws PolicyParser$ParsingException, IOException {
        while (lookahead != ';') {
            switch (lookahead) {
            case StreamTokenizer.TT_NUMBER: 
                throw new PolicyParser$ParsingException(st.lineno(), ";", rb.getString("number ") + String.valueOf(st.nval));
            
            case StreamTokenizer.TT_EOF: 
                throw new PolicyParser$ParsingException(rb.getString("expected \';\', read end of file"));
            
            default: 
                lookahead = st.nextToken();
            
            }
        }
    }
    {
    }
    {
    }
    {
    }
    {
    }
    
    public static void main(String[] arg) throws Exception {
        PolicyParser pp = new PolicyParser(true);
        pp.read(new FileReader(arg[0]));
        FileWriter fr = new FileWriter(arg[1]);
        pp.write(fr);
        fr.close();
    }
}
