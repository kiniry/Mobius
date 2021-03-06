// @(#)$Id$

// Copyright (C) 2000 Iowa State University

// This file is part of JML

// JML is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2, or (at your option)
// any later version.

// JML is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with JML; see the file COPYING.  If not, write to
// the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.

package java.lang;

import java.io.UnsupportedEncodingException;
import java.util.Locale;
import java.util.regex.Pattern;
import java.util.Comparator;

//@ model import org.jmlspecs.models.*;

/** JML's specification of java.lang.String.
 * @version $Revision$
 * @author Gary T. Leavens
 */
public final class String
    implements java.io.Serializable, Comparable, CharSequence
{
    //+@ public model JMLValueSequence stringSeq;

    //+@ public initially stringSeq != null && stringSeq.isEmpty() ;

    //+@ public invariant stringSeq != null;
    /*+@ public invariant
      @     (\forall int i; 0 <= i && i < stringSeq.length();
      @                     stringSeq.itemAt(i) instanceof JMLChar);
      @+*/

    public static final Comparator CASE_INSENSITIVE_ORDER;

    //---------------------------------------------------------------------
    // Constructors (and their helpers)
    //---------------------------------------------------------------------

    /*+@  public normal_behavior
      @      assignable stringSeq;
      @      ensures stringSeq.equals(new JMLValueSequence());
      @+*/
    public /*@ pure @*/ String();

    /*+@  public normal_behavior
      @   requires original != null;
      @   assignable stringSeq;
      @   ensures stringSeq.equals(original.stringSeq);
      @+*/
    public /*@ pure @*/ String(String original);

    /*+@  public normal_behavior
      @   requires value != null;
      @   assignable stringSeq;
      @   ensures (\forall int i; 0 <= i && i < value.length;
      @              ((JMLChar)(stringSeq.itemAt(i))).charValue() == value[i]);
      @   ensures_redundantly 
      @       stringSeq.equals(new String(value, 0, value.length).stringSeq);
      @+*/
    public /*@ pure @*/ String(/*@ non_null @*/ char value[]);

    /*+@  public normal_behavior
      @   requires value != null
      @             && 0 <= offset 
      @             && (offset + count) < value.length
      @             && 0 <= count;
      @   assignable stringSeq;
      @   ensures (\forall int i; offset <= i && i < offset + count;
      @                  ((JMLChar)(stringSeq.itemAt((int)(i - offset)))).charValue()
      @                    == value[i]);
      @ also
      @  public exceptional_behavior
      @   requires value != null
      @             && (offset < 0
      @                 || (offset + count) < value.length
      @                 || count < 0);
      @   signals (StringIndexOutOfBoundsException);
      @+*/
    //+@ implies_that
    //@    requires 0 <= offset && 0 <= count && offset + count < value.length;
    public /*@ pure @*/ String(/*@ non_null @*/ char value[],
                                 int offset, int count)
        throws StringIndexOutOfBoundsException;

    /*+@  public normal_behavior
      @   ensures \result == (char) (((hibyte & 0xff) << 8) | (ascii & 0xff));
    public pure model char byteToChar(int hibyte, byte ascii); @+*/

    /** @deprecated as of 1.1 */
    /*+@  public normal_behavior
      @   requires ascii != null
      @             && 0 <= offset 
      @             && (offset + count) < ascii.length
      @             && 0 <= count;
      @   assignable stringSeq;
      @   ensures (\forall int i; offset <= i && i < offset + count;
      @               ((JMLChar)(stringSeq.itemAt((int)(i - offset)))).charValue()
      @               == byteToChar(hibyte, ascii[i]));
      @ also
      @  public exceptional_behavior
      @   requires ascii != null
      @             && (offset < 0
      @                 || (offset + count) < ascii.length
      @                 || count < 0);
      @   signals (StringIndexOutOfBoundsException);
      @+*/
    //+@ implies_that
    //@    requires 0 <= offset && 0 <= count && offset + count < ascii.length;
    public /*@ pure @*/ String(/*@ non_null @*/ byte ascii[], int hibyte,
                  int offset, int count)
        throws StringIndexOutOfBoundsException;
  
    /** @deprecated as of 1.1 */
    /*+@  public normal_behavior
      @   requires ascii != null;
      @   assignable stringSeq;
      @   ensures (\forall int i;  0 <= i && i < ascii.length;
      @                  ((JMLChar)(stringSeq.itemAt(i))).charValue()
      @                  == byteToChar(hibyte, ascii[i]));
      @+*/
    public /*@ pure @*/ String(/*@ non_null @*/ byte ascii[], int hibyte);

    /*+@ public behavior
      @  requires bytes != null && charsetName != null
      @             && 0 <= offset 
      @             && (offset + length) < bytes.length
      @             && 0 <= length;
      @  {|
      @     requires (* charsetName is the name of a supporting encoding *);
      @     assignable stringSeq;
      @     ensures stringSeq.length() <= length
      @           && (\forall int i; 0 <= i && i < stringSeq.length();
      @                  (* stringSeq.itemAt(i).charValue() == 
      @                     char at position i of the conversion of subarray
      @                     of bytes using the encoding charsetName *));
      @     signals (Exception) false;
      @   also
      @     requires (* !(charsetName is the name of a supporting encoding) *);
      @     ensures false;
      @     signals (UnsupportedEncodingException);
      @  |}
      @+*/
    //+@ implies_that
    //@    requires 0 <= offset && 0 <= length;
    //@    requires offset + length < bytes.length;
    public /*@ pure @*/ String(/*@ non_null @*/ byte bytes[],
                                 int offset, int length,
                                 /*@ non_null @*/ String charsetName)
        throws UnsupportedEncodingException;

    /*+@  public normal_behavior
      @   requires bytes != null && charsetName != null
      @            && (* charsetName is the name of a supporting encoding *);
      @   assignable stringSeq;
      @   ensures stringSeq.equals(new String(bytes, 0, bytes.length, charsetName));
      @ also
      @  public exceptional_behavior
      @   requires bytes != null && charsetName != null
      @            && (* !(charsetName is the name of a supporting encoding) *);
      @   signals (UnsupportedEncodingException);
      @+*/
    public /*@ pure @*/ String(/*@ non_null @*/ byte bytes[],
                                 /*@ non_null @*/ String charsetName)
        throws UnsupportedEncodingException;

    /*+@  public normal_behavior
      @   requires bytes != null
      @             && 0 <= offset 
      @             && (offset + length) < bytes.length
      @             && 0 <= length;
      @   assignable stringSeq;
      @   ensures stringSeq.equals(
      @                new String(bytes, offset, length,
      @                          System.getProperty("file.encoding")));
      @+*/
    //+@ implies_that
    //@    requires 0 <= offset && 0 <= length;
    //@    requires offset + length < bytes.length;
    public /*@ pure @*/ String(/*@ non_null @*/ byte bytes[],
                                 int offset, int length);

    /*+@  public normal_behavior
      @   requires bytes != null;
      @   assignable stringSeq;
      @   ensures stringSeq.equals(
      @                new String(bytes, 0, bytes.length,
      @                           System.getProperty("file.encoding")));
      @+*/
    public /*@ pure @*/ String(/*@ non_null @*/ byte bytes[]);

    /*+@  public normal_behavior
      @  requires buffer != null;
      @  assignable stringSeq;
      @  ensures stringSeq != null 
      @           && stringSeq.equals(buffer.toString().stringSeq);
      @+*/
    public /*@ pure @*/ String (/*@ non_null @*/ StringBuffer buffer);

    String(int offset, int count, char[] value);

    /*+@  protected normal_behavior
      @   requires seq != null;
      @   assignable stringSeq;
      @   ensures stringSeq.equals(seq);
      protected model String(JMLValueSequence seq); @+*/

    //---------------------------------------------------------------------
    // Methods
    //---------------------------------------------------------------------

    //@ also
    /*+@ public normal_behavior
      @  ensures \result == stringSeq.length();
      @+*/
    //+@ implies_that
    //@    ensures \result >= 0;
    public /*@ pure @*/ int length();

    /*+@
      @ also
      @  public normal_behavior
      @   requires 0 <= index && index < length();
      @   ensures \result == ((JMLChar)(stringSeq.itemAt(index))).charValue();
      @ also
      @  public exceptional_behavior
      @   requires index < 0 || index >= length();
      @   signals (StringIndexOutOfBoundsException);
      @+*/
    public /*@ pure @*/ char charAt(int index)
        throws StringIndexOutOfBoundsException;

    /*+@  public normal_behavior
      @   requires srcBegin >= 0
      @             && srcEnd < length()
      @             && srcBegin < srcEnd
      @             && dst != null
      @             && dst.length >= dstBegin + (srcEnd - srcBegin) + 1;
      @   ensures (\forall int i; srcBegin <= i && i < srcEnd;
      @                           dst[(int)(dstBegin + i - srcBegin)] == charAt(i));
      @ also
      @  public exceptional_behavior
      @   requires (srcBegin <= 0
      @              || srcEnd > length()
      @              || srcBegin >= srcEnd)
      @             && dst != null
      @             && dst.length >= dstBegin + (srcEnd - srcBegin) + 1;
      @   signals (StringIndexOutOfBoundsException);
      @+*/
    public /*@ pure @*/ void getChars(int srcBegin, int srcEnd,
                                        char dst[], int dstBegin)
      throws StringIndexOutOfBoundsException;

    /** @deprecated as of 1.1, use getBytes() */
    /*+@  public normal_behavior
      @   requires srcBegin >= 0
      @             && srcEnd < length()
      @             && srcBegin < srcEnd
      @             && dst != null
      @             && dst.length >= dstBegin + (srcEnd - srcBegin) + 1;
      @   ensures (\forall int i; i >= srcBegin && i < srcEnd;
      @                            dst[(int)(dstBegin + i - srcBegin)]
      @                            == (byte) (charAt(i) & 0xff));
      @ also
      @  public exceptional_behavior
      @   requires (srcBegin <= 0
      @              || srcEnd > length()
      @              || srcBegin >= srcEnd)
      @             && dst != null
      @             && dst.length >= dstBegin + (srcEnd - srcBegin) + 1;
      @   signals (StringIndexOutOfBoundsException);
      @+*/
    public /*@ pure @*/ void getBytes(int srcBegin, int srcEnd,
                                        byte dst[], int dstBegin)
      throws StringIndexOutOfBoundsException;

    /*+@  public normal_behavior
      @   ensures \result == (a.length == b.length)
      @                       && (\forall int i; 0 <= i && i < a.length;
                                                 a[i] == b[i]);
    public pure model boolean byteArraysEqual(byte[] a, byte[] b);   @+*/

    /*+@  public normal_behavior
      @   requires charsetName != null 
      @             && (* charsetName is the name of a supporting encoding *);
      @   ensures \result != null 
      @            && (\forall int i; 0 <= i && i < \result.length;
      @                    (* \result[i] is the byte at position i of the 
      @                       conversion of this string's chars using charsetName *));
      @ also
      @  public exceptional_behavior
      @   requires charsetName != null 
      @             && (* !(charsetName is the name of a supporting encoding) *);
      @   signals (UnsupportedEncodingException);
      @+*/
    public /*@ pure @*/ /*@ non_null @*/ byte[] getBytes(String charsetName)
      throws UnsupportedEncodingException;

    /*+@  public normal_behavior
      @  ensures \result != null 
      @           && byteArraysEqual(\result, 
      @                       getBytes(System.getProperty("file.encoding")));
      @+*/
    public /*@ pure @*/ /*@ non_null @*/ byte[] getBytes();

    /*+@ also  public normal_behavior
      @   requires anObject != null && (anObject instanceof String);
      @   ensures \result == (stringSeq.equals(((String)anObject).stringSeq));
      @ also
      @   requires anObject == null || !(anObject instanceof String);
      @   ensures !\result;
      @+*/
    public /*@ pure @*/ boolean equals(Object anObject);

    /*+@ public normal_behavior
      @   requires sb != null;
      @   ensures \result <==> length() == sb.length()
      @        && (\forall int i; 0 <= i && i < length();
      @               charAt(i) == sb.charAt(i));
      @+*/
    public /*@ pure @*/ boolean contentEquals(StringBuffer sb);

    /*+@  public normal_behavior
      @    ensures \result <==> (c1 == c2)
      @                        || (Character.toUpperCase(c1) 
      @                            == Character.toUpperCase(c2))
      @                        || (Character.toLowerCase(c1) 
      @                            == Character.toLowerCase(c2));
      public static pure model
          boolean charEqualsIgnoreCase(char c1, char c2); @+*/

    /*+@  public normal_behavior
      @   requires anotherString != null;
      @   ensures \result <==> (length() == anotherString.length())
      @                        && (\forall int i;
      @                             0 <= i && i < this.length();
      @                              charEqualsIgnoreCase(
      @                                   charAt(i),
      @                                   anotherString.charAt(i)));
      @ also
      @   requires anotherString == null;
      @   ensures !\result;
      @+*/
    public /*@ pure @*/ boolean equalsIgnoreCase(String anotherString);

    /*+@  public normal_behavior
      @   requires s1 != null && s2 != null
      @             && (\forall int i; 0 <= i && i < s1.length();
      @                   (s1.itemAt(i) instanceof JMLChar))
      @             && (\forall int i; 0 <= i && i < s2.length();
      @                   (s2.itemAt(i) instanceof JMLChar));
      @   {|
      @     requires s2.isEmpty() && s1.isEmpty();
      @     ensures !\result;
      @   also
      @     requires s1.isEmpty() && !s2.isEmpty();
      @     ensures \result;
      @   also
      @     requires !s1.isEmpty() && s2.isEmpty();
      @     ensures !\result;
      @   also
      @     requires ((JMLChar)s1.first()).charValue()
      @                 < ((JMLChar)s2.first()).charValue();
      @     ensures \result;
      @   also
      @     requires ((JMLChar)s1.first()).charValue()
      @                 > ((JMLChar)s2.first()).charValue();
      @     ensures !\result;
      @   also
      @     requires ((JMLChar)s1.first()).charValue()
      @                 == ((JMLChar)s2.first()).charValue();
      @     ensures \result == lessThan(s1.trailer(), s2.trailer());
      @   |}
      @ also
      @   code_contract
      @     measured_by Math.min(s1.length(), s2.length());
    public static pure model boolean lessThan(JMLValueSequence s1,
                                              JMLValueSequence s2);  @+*/

    /*+@  public normal_behavior
      @   requires anotherString != null;
      @   {|
      @       requires stringSeq.equals(anotherString.stringSeq);
      @       ensures \result == 0;
      @     also
      @       requires lessThan(stringSeq, anotherString.stringSeq);
      @       ensures \result < 0;
      @     also
      @       requires !lessThan(stringSeq, anotherString.stringSeq)
      @                 && !stringSeq.equals(anotherString.stringSeq);
      @       ensures \result > 0;
      @   |}
      @+*/
    public /*@ pure @*/ int compareTo(String anotherString);

    /*+@ also
      @   public normal_behavior
      @     requires o != null && (o instanceof String);
      @     ensures \result == compareTo((String) o);
      @ also
      @   public exceptional_behavior
      @     requires o == null && !(o instanceof String);
      @     signals (Exception e) e instanceof ClassCastException;
      @+*/
    public /*+@ pure @+*/ int compareTo(Object o);

    /*+@ public normal_behavior
      @   forall JMLValueSequence s1up, s2up, s1down, s2down;
      @   requires s1 != null && s2 != null;
      @   requires s1up != null && s2up != null
      @            && s1down != null && s2down != null
      @            && s1up.length() == s1.length()
      @            && s1down.length() == s1.length()
      @            && s2up.length() == s2.length()
      @            && s2down.length() == s2.length();
      @   requires (\forall int i; 0 <= i && i < s1.length();
      @                   (s1.itemAt(i) instanceof JMLChar)
      @                && (s1up.itemAt(i) instanceof JMLChar)
      @                && (s1down.itemAt(i) instanceof JMLChar)
      @                && Character.toUpperCase(
      @                       ((JMLChar)(s1.itemAt(i))).charValue())
      @                   == ((JMLChar)(s1up.itemAt(i))).charValue()
      @                && Character.toLowerCase(
      @                       ((JMLChar)(s1.itemAt(i))).charValue())
      @                   == ((JMLChar)(s1down.itemAt(i))).charValue())
      @             && (\forall int i; 0 <= i && i < s2.length();
      @                   (s2.itemAt(i) instanceof JMLChar)
      @                && (s2up.itemAt(i) instanceof JMLChar)
      @                && (s2down.itemAt(i) instanceof JMLChar)
      @                && Character.toUpperCase(
      @                       ((JMLChar)(s2.itemAt(i))).charValue())
      @                   == ((JMLChar)(s2up.itemAt(i))).charValue()
      @                && Character.toLowerCase(
      @                       ((JMLChar)(s2.itemAt(i))).charValue())
      @                   == ((JMLChar)(s2down.itemAt(i))).charValue());
      @   ensures \result <==> lessThan(s1, s2) || lessThan(s1up, s2up)
      @                        || lessThan(s1down, s2down);
    public static pure model boolean lessThanIgnoreCase(JMLValueSequence s1,
                                                        JMLValueSequence s2);
                                                        @+*/

    /*+@  public normal_behavior
      @   requires str != null;
      @   {|
      @       requires equalsIgnoreCase(str);
      @       ensures \result == 0;
      @     also
      @       requires lessThanIgnoreCase(stringSeq, str.stringSeq);
      @       ensures \result < 0;
      @     also
      @       requires !lessThanIgnoreCase(stringSeq, str.stringSeq)
      @                 && !stringSeq.equals(str.stringSeq);
      @       ensures \result > 0;
      @   |}
      @+*/
    public /*@ pure @*/ int compareToIgnoreCase(String str);

    /*+@  public normal_behavior
      @   requires other != null;
      @   ensures \result == regionMatches(false,toffset,other,ooffset,len);
      @+*/
    public /*@ pure @*/ boolean regionMatches(int toffset, String other, 
                                 int ooffset, int len);

    /*+@ public normal_behavior
      @  requires other != null;
      @  {|
      @   requires (0 <= toffset && (toffset + len) <= length())
      @             && (0 <= ooffset && (ooffset + len) < other.length())
      @             && ignoreCase;
      @   ensures \result == substring(toffset, (int)(toffset + len)).equalsIgnoreCase(
      @                        other.substring(ooffset, (int)(ooffset + len)));
      @  also
      @   requires (0 <= toffset && (toffset + len) <= length())
      @             && (0 <= ooffset && (ooffset + len) < other.length())
      @             && !ignoreCase;
      @   ensures \result == substring(toffset, (int)(toffset + len))
      @                        .equals(other.substring(ooffset, (int)(ooffset + len)));
      @  also
      @   requires (toffset < 0 || (toffset + len) > length())
      @             || (toffset < 0 || (ooffset + len) > other.length());
      @   ensures !\result;
      @  |}
      @+*/
    public /*@ pure @*/ boolean regionMatches(boolean ignoreCase,
                                                int toffset, String other, 
                                                int ooffset, int len);

    /*+@  public normal_behavior
      @   requires prefix != null && toffset < length();
      @   ensures \result == 
      @              substring(toffset).stringSeq.isPrefix(prefix.stringSeq);
      @  also
      @   requires prefix != null && toffset >= length();
      @   ensures !\result;
      @+*/
    public /*@ pure @*/ boolean startsWith(String prefix, int toffset);

    /*+@  public normal_behavior
      @   requires prefix != null;
      @   ensures \result == startsWith(prefix, 0);
      @+*/
    public /*@ pure @*/ boolean startsWith(String prefix);

    /*+@  public normal_behavior
      @   requires suffix != null && suffix.length() <= length();
      @   ensures \result == substring((int)(length() - suffix.length()))
      @                        .equals(suffix);
      @  also
      @   requires suffix != null && suffix.length() > length();
      @   ensures !\result;
      @+*/
    public /*@ pure @*/ boolean endsWith(String suffix);

    // specification is inherited, this method does have side effects!
    public int hashCode();

    /*+@  public normal_behavior
      @   ensures \result == indexOf(ch, 0);
      @+*/
    public /*@ pure @*/ int indexOf(int ch);

    // behavior is not described if fromIndex >= length() but this
    // specification reflects the implementation
    /*+@  public normal_behavior
      @   requires fromIndex >= length();
      @   ensures \result == -1;
      @  also
      @   requires fromIndex < 0;
      @   ensures \result == indexOf(ch, 0);
      @  also
      @   requires 0 <= fromIndex && fromIndex < length();
      @   {|
      @     requires charAt(fromIndex) == ch;
      @     ensures \result == fromIndex;
      @   also
      @     requires charAt(fromIndex) != ch;
      @     ensures \result == indexOf(ch, (int)(fromIndex + 1));
      @   |}
      @+*/
    public /*@ pure @*/ int indexOf(int ch, int fromIndex);

    /*+@  public normal_behavior
      @   ensures \result == lastIndexOf(ch, (int)(length() - 1));
      @+*/
    public /*@ pure @*/ int lastIndexOf(int ch);

    // behavior is not described if fromIndex >= length() but this
    // specification reflects the implementation
    /*+@ public normal_behavior
      @ {|
      @   requires fromIndex >= length();
      @   ensures \result == lastIndexOf(ch, (int)(length() - 1));
      @ also
      @   requires fromIndex < 0;
      @   ensures \result == -1;
      @ also
      @   requires 0 <= fromIndex && fromIndex < length();
      @   {|
      @     requires charAt(fromIndex) == ch;
      @     ensures \result == fromIndex;
      @   also
      @     requires charAt(fromIndex) != ch;
      @     ensures \result == lastIndexOf(ch, (int)(fromIndex - 1));
      @   |}
      @ |}
      @+*/
    public /*@ pure @*/ int lastIndexOf(int ch, int fromIndex);

    /*+@ public normal_behavior
      @  requires str != null;
      @  ensures \result == indexOf(str, 0);
      @+*/
    public /*@ pure @*/ int indexOf(String str);

    // behavior is not described if fromIndex >= length() but this
    // specification reflects the implementation
    /*+@  public normal_behavior
      @   requires str != null;
      @   {|
      @     requires fromIndex >= length();
      @     ensures \result == -1;
      @   also
      @     requires fromIndex < 0;
      @     ensures \result == indexOf(str, 0);
      @   also
      @     requires 0 <= fromIndex && fromIndex < length();
      @     {|
      @       requires stringSeq.removePrefix(fromIndex)
      @                     .isPrefix(str.stringSeq);
      @       ensures \result == fromIndex;
      @     also
      @       requires !stringSeq.removePrefix(fromIndex)
      @                     .isPrefix(str.stringSeq);
      @       ensures \result == indexOf(str, (int)(fromIndex + 1));
      @     |}
      @   |}
      @+*/
    public /*@ pure @*/ int indexOf(String str, int fromIndex);

    static /*@ pure @*/
        int indexOf(char[] source, int sourceOffset, int sourceCount,
                    char[] target, int targetOffset, int targetCount,
                    int fromIndex);
      
    /*+@  public normal_behavior
      @   requires str != null;
      @   ensures \result == lastIndexOf(str, (int)(length() - 1));
      @+*/
    public /*@ pure @*/ int lastIndexOf(String str);

    // behavior is not described if fromIndex >= length() but this
    // specification reflects the implementation
    /*+@  public normal_behavior
      @   requires str != null;
      @   {|
      @     requires fromIndex >= length();
      @     ensures \result == lastIndexOf(str, (int)(length() - 1));
      @   also
      @     requires fromIndex < 0;
      @     ensures \result == -1;
      @   also
      @     requires 0 <= fromIndex && fromIndex < length();
      @     {|
      @       requires stringSeq.removePrefix(fromIndex)
      @                     .isPrefix(str.stringSeq);
      @       ensures \result == fromIndex;
      @     also
      @       requires !stringSeq.removePrefix(fromIndex)
      @                     .isPrefix(str.stringSeq);
      @       ensures \result == indexOf(str, (int)(fromIndex - 1));
      @     |}
      @   |}
      @+*/
    public /*@ pure @*/ int lastIndexOf(String str, int fromIndex);
      
    static /*@ pure @*/
        int lastIndexOf(char[] source, int sourceOffset, int sourceCount,
                        char[] target, int targetOffset, int targetCount,
                        int fromIndex);

    /*+@  public normal_behavior
      @   requires beginIndex < length();
      @   ensures \result == substring(beginIndex, length());
      @ also
      @  public exceptional_behavior
      @   requires beginIndex >= length();
      @   signals (StringIndexOutOfBoundsException);
      @+*/
    public /*@ pure @*/ /*@ non_null @*/ String substring(int beginIndex)
      throws StringIndexOutOfBoundsException;

    /*+@  public normal_behavior
      @   requires 0 <= beginIndex
      @             && beginIndex < endIndex
      @             && (endIndex <= length());
      @   ensures \result != null
      @            && \result.stringSeq.equals(
      @                    stringSeq.subsequence(beginIndex, endIndex));
      @ also
      @  public exceptional_behavior
      @   requires 0 > beginIndex
      @             || beginIndex >= endIndex
      @             || (endIndex > length());
      @   signals (StringIndexOutOfBoundsException);
      @+*/
    public /*@ pure @*/ /*@ non_null @*/ String substring(int beginIndex,
                                                            int endIndex)
      throws StringIndexOutOfBoundsException;

    public /*@ pure @*/ CharSequence subSequence(int beginIndex,
                                                   int endIndex);

    /*+@  public normal_behavior
      @   requires str != null;
      @   ensures \result != null
      @            && \result.stringSeq.equals(stringSeq.concat(str.stringSeq));
      @+*/
    public /*@ pure @*/ /*@ non_null @*/
        String concat(/*@ non_null @*/ String str);

    /*+@  public normal_behavior
      @   ensures \result != null
      @            && \result.length() == length()
      @            && (\forall int i; 0 <= i && i < length();
      @                  \result.charAt(i) 
      @                     == ((charAt(i) == oldChar) ? newChar : charAt(i)));
      @+*/
    public /*@ pure @*/ /*@ non_null @*/ String replace(char oldChar,
                                                          char newChar);

    /*+@ public normal_behavior
      @     requires regex != null;
      @     assignable \nothing;
      @     ensures \result <==> Pattern.matches(regex, this);
      @+*/
    public /*@ pure @*/ boolean matches(/*@ non_null @*/ String regex);

    /*+@ public normal_behavior
      @     requires regex != null && replacement != null;
      @     assignable \nothing;
      @     ensures \result.equals(
      @               Pattern.compile(regex).matcher(this)
      @                      .replaceFirst(replacement));
      @+*/
    public /*@ pure @*/ /*@ non_null @*/
        String replaceFirst(/*@ non_null @*/ String regex,
                            /*@ non_null @*/ String replacement);

    /*+@ public normal_behavior
      @     requires regex != null && replacement != null;
      @     assignable \nothing;
      @     ensures \result.equals(
      @               Pattern.compile(regex).matcher(this)
      @                      .replaceAll(replacement));
      @+*/
    public /*@ pure @*/ /*@ non_null @*/
        String replaceAll(/*@ non_null @*/ String regex,
                          /*@ non_null @*/ String replacement);

    /*+@ public normal_behavior
      @     requires regex != null;
      @     assignable \nothing;
      @     ensures \result.equals(Pattern.compile(regex).split(this, limit));
      @+*/
    public /*@ pure @*/ /*@ non_null @*/
        String[] split(/*@ non_null @*/ String regex, int limit);

    /*+@ public normal_behavior
      @     requires regex != null;
      @     assignable \nothing;
      @     ensures \result.equals(split(regex,0));
      @+*/
    public /*@ pure @*/ /*@ non_null @*/
        String[] split(/*@ non_null @*/ String regex);

    /*+@  public normal_behavior
      @   requires locale != null;
      @   ensures (* \result == a lower case conversion of this using the 
      @                          rules of the given locale *);
      @+*/
    public /*@ pure @*/ /*@ non_null @*/
        String toLowerCase(/*@ non_null @*/ Locale locale);

    /*+@  public normal_behavior
      @   ensures \result != null
      @            && \result.equals(toLowerCase(Locale.getDefault()));
      @+*/
    public /*@ pure @*/ /*@ non_null @*/ String toLowerCase();

    /*+@  public normal_behavior
      @   requires locale != null;
      @   ensures (* \result == an upper case conversion of this using the 
      @                          rules of the given locale *);
      @+*/
    public /*@ pure @*/ /*@ non_null @*/
        String toUpperCase(/*@ non_null @*/ Locale locale);

    /*+@  public normal_behavior
      @   ensures \result != null
      @            && \result.equals(toUpperCase(Locale.getDefault()));
      @+*/
    public /*@ pure @*/ /*@ non_null @*/ String toUpperCase();

    /*+@  public normal_behavior
      @   ensures \result != null
      @            && \result.length() <= length()
      @            && \result.charAt(0) > ' '
      @            && \result.charAt((int)(\result.length() - 1)) > ' ';
      @+*/
    public /*@ pure @*/ /*@ non_null @*/ String trim();

    /*+@ also
      @  public normal_behavior
      @    ensures \result != null && \result == this;
      @+*/
    public /*@ pure @*/ /*@ non_null @*/ String toString();
    
    /*+@  public normal_behavior
      @    ensures \result != null
      @          && \result.length == length()
      @          && (\forall int i; 0 <= i && i < length();
      @                             \result[i] == charAt(i));
      @+*/
    public /*@ pure @*/ /*@ non_null @*/ char[] toCharArray();

    /*+@  public normal_behavior
      @  {|
      @    requires obj == null;
      @    ensures \result != null && \result.equals("null");
      @  also
      @    requires obj != null;
      @    ensures \result != null;
      @  |}
      @  also
      @    public model_program {
      @       assume obj != null;
      @       return obj.toString();
      @    }
      @+*/
    public static /*@ pure @*/ /*@ non_null @*/ String valueOf(Object obj);

    /*+@  public normal_behavior
      @  requires data != null;
      @   ensures \result != null && \result.equals(new String(data));
      @+*/
    public static /*@ pure @*/
        /*@ non_null @*/ String valueOf(/*@ non_null @*/ char data[]);

    /*+@  public normal_behavior
      @  requires data != null && offset >= 0 && count >= 0
      @       && offset + count < data.length;
      @   ensures \result != null 
      @            && \result.equals(new String(data, offset, count));
      @+*/
    public static /*@ pure @*/
        /*@ non_null @*/ String valueOf(/*@ non_null @*/ char data[],
                                        int offset, int count);

    /*+@  public normal_behavior
      @  requires data != null;
      @   ensures \result != null 
      @            && \result.equals(new String(data, offset, count));
      @+*/
    public static /*@ pure @*/
        /*@ non_null @*/ String copyValueOf(/*@ non_null @*/ char data[],
                                            int offset, int count);

    /*+@  public normal_behavior
      @  requires data != null;
      @  ensures \result != null && \result.equals(new String(data));
      @+*/
    public static /*@ pure @*/
        /*@ non_null @*/ String copyValueOf(/*@ non_null @*/ char data[]);
        
    /*+@  public normal_behavior
      @   ensures \result != null
      @            && (b ==> \result.equals("true")
      @                || !b ==> \result.equals("false"));
      @+*/
    public static /*@ pure @*/ /*@ non_null @*/ String valueOf(boolean b);

    /*+@  public normal_behavior
      @   ensures \result != null
      @            && \result.length() == 1
      @            && \result.charAt(0) == c;
      @+*/
    public static /*@ pure @*/ /*@ non_null @*/ String valueOf(char c);

    /*+@  public normal_behavior
      @   ensures \result != null && \result.equals(Integer.toString(i));
      @+*/
    public static /*@ pure @*/ /*@ non_null @*/ String valueOf(int i);
    
    /*+@  public normal_behavior
      @   ensures \result != null && \result.equals(Long.toString(l));
      @+*/
    public static /*@ pure @*/ /*@ non_null @*/ String valueOf(long l);
    
    /*+@  public normal_behavior
      @   ensures \result != null && \result.equals(Float.toString(f));
      @+*/
    public static /*@ pure @*/ /*@ non_null @*/ String valueOf(float f);
    
    /*+@  public normal_behavior
      @   ensures \result != null && \result.equals(Double.toString(d));
      @+*/
    public static /*@ pure @*/ /*@ non_null @*/ String valueOf(double d);
    
    //+@ public model non_null JMLDataGroup stringPool;

    /*+@  public normal_behavior
      @   assignable stringPool;
      @   ensures_redundantly (* \result is a canonical representation 
      @                           for this *);
      @+*/
    public native /*@ non_null @*/ String intern();

}
