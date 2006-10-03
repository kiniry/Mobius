//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Util.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.util;

import java.util.StringTokenizer;

/**
 * Class containing utility functions.
 * 
 * @author A. Requet
 */
public class Util extends Profiler {

    /**
     * Returns a string array corresponding to parts of a given string 
     * @param string_list The given string
     * @param delim The delimiter
     **/
	public static String[] tokenize(String string_list, String delim) {
		if (string_list == null)
			return new String[0];
		StringTokenizer tok = new StringTokenizer(string_list, delim);
		int token_count = tok.countTokens();
		String[] result = new String[token_count];

		for (int i = 0; i < token_count; ++i) {
			result[i] = tok.nextToken();
		}

		return result;
	}

    /**
     * Returns the number of parts into a given string 
     * @param string_list The given string
     * @param delim The delimiter
     **/
	public static int countTokens(String string_list, String delim) {
		if (string_list == null)
			return 0;
		StringTokenizer tok = new StringTokenizer(string_list, delim);
		return tok.countTokens();
	}

    /**
     * Returns a string contained from an array of string and a delimiter
     * @param list The string array
     * @param delim The delimiter
     **/
	public static String untokenize(String[] list, String delim) {
		if (list.length <= 0) {
			return "";
		}

		String result = list[0];
		for (int i = 1; i < list.length; ++i) {
			result += delim + list[i];
		}
		return result;
	}

}
