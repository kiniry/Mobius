package com.sun.security.auth;

import java.io.*;
import java.lang.reflect.*;
import java.util.*;
import java.security.CodeSource;
import java.security.Permissions;
import javax.security.auth.Subject;

class PolicyFile$3 implements java.security.PrivilegedAction {
    /*synthetic*/ final PolicyFile this$0;
    /*synthetic*/ final CodeSource val$codesource;
    /*synthetic*/ final Subject val$subject;
    
    PolicyFile$3(/*synthetic*/ final PolicyFile this$0, /*synthetic*/ final Subject val$subject, /*synthetic*/ final CodeSource val$codesource) {
        this.this$0 = this$0;
        this.val$subject = val$subject;
        this.val$codesource = val$codesource;
        
    }
    
    public Object run() {
        SubjectCodeSource scs = new SubjectCodeSource(val$subject, null, val$codesource == null ? null : val$codesource.getLocation(), val$codesource == null ? null : val$codesource.getCertificates());
        if (PolicyFile.access$100(this$0)) return this$0.getPermissions(new Permissions(), scs); else return new PolicyPermissions(this$0, scs);
    }
}
