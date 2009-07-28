/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

/**

<TT>Tags</TT> is a class defining a partially-opaque type for tags
used in the AST.  "Partially opaque" means that the representation of
this type is known -- it's an <code>int</code> -- but code should not
depend on the detailed mapping of operator tags to integers.

<p> ...say something about <code>OperatorTags</code> and
<code>GeneratedTags</code>...

*/


public class TagConstants extends OperatorTags
{
  /** Used to indicate that no tag applies, for example, when looking
    up the tag associated with a string. */
  public static final int NULL = -1;


  public static final int IDENT = javafe.ast.OperatorTags.LAST_TAG + 1;

  public static final int BOOLEANTYPE = IDENT + 1;
  public static final int INTTYPE = BOOLEANTYPE + 1;
  public static final int LONGTYPE = INTTYPE + 1;
  public static final int CHARTYPE = LONGTYPE + 1;
  public static final int FLOATTYPE = CHARTYPE + 1;
  public static final int DOUBLETYPE = FLOATTYPE + 1;
  public static final int VOIDTYPE = DOUBLETYPE + 1;
  public static final int NULLTYPE = VOIDTYPE + 1;
  public static final int BYTETYPE = NULLTYPE + 1;
  public static final int SHORTTYPE = BYTETYPE + 1;

  public static final int BOOLEANLIT = SHORTTYPE+1;
  public static final int INTLIT = BOOLEANLIT + 1;
  public static final int LONGLIT = INTLIT + 1;
  public static final int CHARLIT = LONGLIT + 1;
  public static final int FLOATLIT = CHARLIT + 1;
  public static final int DOUBLELIT = FLOATLIT + 1;
  public static final int STRINGLIT = DOUBLELIT + 1;
  public static final int NULLLIT = STRINGLIT + 1;

  public static final int LAST_TAG = NULLLIT;

  private static final String[] tags = { "IDENT",
	"BOOLEANTYPE", "INTTYPE", "LONGTYPE", "CHARTYPE",
	"FLOATTYPE", "DOUBLETYPE", "VOIDTYPE", "NULLTYPE",
	"BYTETYPE", "SHORTTYPE", 
	"BOOLEANLIT", "INTLIT", "LONGLIT", "CHARLIT",
	"FLOATLIT", "DOUBLELIT", "STRINGLIT", "NULLLIT" };

    public static String toString(int tag) {
	if (IDENT<=tag && tag<=LAST_TAG)
	    return tags[tag-IDENT];

	return OperatorTags.toString(tag);
    }
}
