/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.ast;

import javafe.ast.Identifier;
import javafe.util.Assert;


public class TagConstants
    extends javafe.tc.TagConstants
    implements GeneratedTags
{
		
    //// keywords
    public static final int FIRSTRCCKEYWORDTAG = rcc.ast.GeneratedTags.LAST_TAG + 1;
    public static final int GUARDED_BY = FIRSTRCCKEYWORDTAG; 
    public static final int REQUIRES = GUARDED_BY + 1; 
    public static final int HOLDS = REQUIRES + 1;
    public static final int NOWARN = HOLDS + 1;
    public static final int ELEMS_GUARDED_BY = NOWARN + 1;
    public static final int THREAD_LOCAL = ELEMS_GUARDED_BY + 1;
    public static final int THREAD_SHARED = THREAD_LOCAL + 1;
    public static final int READONLY = THREAD_SHARED + 1;
    public static final int GHOST = READONLY + 1;
    public static final int LASTRCCKEYWORDTAG = ELEMS_GUARDED_BY;
    
    //// Tags for RCC/Java checks
    public static final int FIRSTRCCCHECKTAG = LASTRCCKEYWORDTAG + 1;
    public static final int CHKBADCAST = FIRSTRCCCHECKTAG;
    public static final int CHKCONSTANTLOCKS = CHKBADCAST + 1;
    public static final int CHKMODIFIERS = CHKCONSTANTLOCKS + 1;
    public static final int CHKSUPER = CHKMODIFIERS + 1;
    public static final int CHKRACE = CHKSUPER + 1;
    public static final int CHKLOCAL = CHKRACE + 1;
    public static final int CHKOVERRIDE = CHKLOCAL + 1;
    public static final int CHKMSG = CHKOVERRIDE + 1;
    public static final int CHKREADONLY = CHKMSG + 1;
    public static final int CHKSTATICFIELD = CHKREADONLY + 1;
    public static final int CHKSHAREDFIELD = CHKSTATICFIELD + 1;
    public static final int CHKSHAREDARRAY = CHKSHAREDFIELD + 1;
    public static final int LASTRCCCHECKTAG = CHKSHAREDARRAY + 1;
    
    
    // Constants used in deciding how to translate CHKs
    public static final int CHK_AS_ASSUME = LASTRCCCHECKTAG + 1;
    public static final int CHK_AS_ASSERT = CHK_AS_ASSUME + 1;
    public static final int CHK_AS_SKIP = CHK_AS_ASSERT + 1;
    public static final int LAST_TAG = CHK_AS_SKIP + 1;
    
    //// Helper functions
    
    public static String toString(int tag) {
	switch(tag) {
	case CHK_AS_ASSUME:
	    return "CHK_AS_ASSUME";
	case CHK_AS_ASSERT:
	    return "CHK_AS_ASSERT";
	case CHK_AS_SKIP:
	    return "CHK_AS_SKIP";
	default:
	    if (FIRSTRCCKEYWORDTAG <= tag && tag <= LASTRCCKEYWORDTAG)
		return rcckeywords[tag - FIRSTRCCKEYWORDTAG].toString();
	    else if (FIRSTRCCCHECKTAG <= tag && tag < LASTRCCCHECKTAG)
		return rccchecks[tag - FIRSTRCCCHECKTAG];
	    else if (tag < javafe.tc.TagConstants.LAST_TAG + 1)
		return javafe.tc.TagConstants.toString(tag);
	    else
		return "Unknown RCC tag <" + tag
		    + " (+" + (tag-javafe.tc.TagConstants.LAST_TAG) + ") >";
	}
    }
    
    public static int fromIdentifier(Identifier rcckeyword) {
	for(int i = 0; i < rcckeywords.length; i++)
	    if (rcckeyword == rcckeywords[i]) return i + GUARDED_BY;
	return NULL;
    }
    
    public static int checkFromString(String s) {
	for (int i = FIRSTRCCCHECKTAG; i <= LASTRCCCHECKTAG; i++) {
	    if (s.equals(rccchecks[i - FIRSTRCCCHECKTAG]))
		return i;
	}
				//@ unreachable
	Assert.fail("unrecognized check string: \"" + s + "\"");
	return -1;
    }
    
    private static Identifier[] rcckeywords = {
	Identifier.intern("guarded_by"),
	Identifier.intern("requires"),
	Identifier.intern("holds"),
	Identifier.intern("no_warn"),
	Identifier.intern("elems_guarded_by"),
	Identifier.intern("thread_local"),
	Identifier.intern("thread_shared"),
	Identifier.intern("readonly"),
	Identifier.intern("ghost")
    };
    
    private static String[] rccchecks = {
	"BadCast", 
	"ConstantLocks",
	"Modifiers",
	"Super",
	"Race",
	"ThreadLocal",
	"Override",
	"Message",
	"ReadOnly",
	"StaticField",
	"SharedField",
	"SharedArray"
    };
    
    
    static {
				
    }
    
    
    
    public static void main(String[] args) {
	for(int i= 0; i< LAST_TAG; i++ )
	    System.out.println(i+" "+toString(i));
    }
}














