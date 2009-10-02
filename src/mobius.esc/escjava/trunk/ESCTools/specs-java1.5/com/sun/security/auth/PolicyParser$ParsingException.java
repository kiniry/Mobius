package com.sun.security.auth;

import java.io.*;
import java.security.GeneralSecurityException;

class PolicyParser$ParsingException extends GeneralSecurityException {
    private static final long serialVersionUID = 8240970523155877400L;
    
    public PolicyParser$ParsingException(String msg) {
        super(msg);
    }
    
    public PolicyParser$ParsingException(int line, String msg) {
        super(PolicyParser.access$000().getString("line ") + line + PolicyParser.access$000().getString(": ") + msg);
    }
    
    public PolicyParser$ParsingException(int line, String expect, String actual) {
        super(PolicyParser.access$000().getString("line ") + line + PolicyParser.access$000().getString(": expected \'") + expect + PolicyParser.access$000().getString("\', found \'") + actual + PolicyParser.access$000().getString("\'"));
    }
}
