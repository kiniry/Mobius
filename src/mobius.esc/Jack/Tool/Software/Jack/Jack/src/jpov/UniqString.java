//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: UniqString
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jpov;

import java.util.HashMap;

/**
 * This class provides facilities to manage strings that appears during the view
 * phases. Strings are strored into an hashtable in manner to have an uniq 
 * instance even if it appears many times mainly in the JPO file.
 * @author L. Burdy
 */
public class UniqString {

    /**
     * The hash table containing the strings
     **/
    private static HashMap map = new HashMap();
    
    /**
     * Returns the instance of a string stored in the table.
     * @param s The searched string
     * @return <code>s</code> if it is the first occurence of this string or 
     * the already stored instance if not.
     **/
    /*@
      @ ensures \result != null;
      @*/
    public static String getUniqString(String s) {
        if (map.containsKey(s))
            return (String) map.get(s);
        else {
            map.put(s,s);
            return s;
        }
    }   

}
