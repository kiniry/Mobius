// @(#)$Id: JmlLiteralsTable.java,v 1.65 2001/08/02 18:36:19 leavens Exp $

// Copyright (C) 1998, 1999 Iowa State University

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


package jml;

import java.util.Hashtable;
import java.util.BitSet;
import antlr.ANTLRStringBuffer;

public class JmlLiteralsTable {
    protected Hashtable jmlKeywords;
    protected Hashtable jmlBackslashKeywords;
    protected BitSet jmlSpecialTokenTypes;
    protected BitSet jmlQuantifiers;

    /**
     * This interface contains the special Java token types,
     * the token types from JavaTokenTypes that do NOT switch modes.
     * There are two modes depending on whether the lexer is
     * recognizing JML keywords or not.
     */
    // This interface is "protected" instead of "private"
    // so that it will compile under JDK 1.1.
    protected interface SpecialJMLTokenTypes extends JavaTokenTypes {
      int[] tokens = {
        ABRUPT_BEHAVIOR,
	ALSO,
	AND,
	BEHAVIOR,
	CHOOSE,
	CHOOSE_IF,
	EXAMPLE,
	EXCEPTIONAL_BEHAVIOR,
	EXCEPTIONAL_EXAMPLE,
	FORALL,
	FOR_EXAMPLE,
	GHOST,
	IMPLIES_THAT,
	INITIALIZER,
	INSTANCE,
	LET,
	MODEL,
	MODEL_PROGRAM,
	MONITORED,
        NON_NULL,
	NORMAL_BEHAVIOR,
	NORMAL_EXAMPLE,
        OLD,
	OR,
	PURE,
	SPEC_PROTECTED,
	SPEC_PUBLIC,
	STATIC_INITIALIZER,
	SUBCLASSING_CONTRACT,
	UNINITIALIZED,
	WEAKLY
      };
    }

    public boolean isFollowedBySpecExpr(int tokenType) {
	return (!jmlSpecialTokenTypes.get(tokenType));
    }

    /**
     * This interface contains the quantifier token types.
     */
    // This interface is "protected" instead of "private"
    // so that it will compile under JDK 1.1.
    protected interface JmlQuantifierTokenTypes extends JavaTokenTypes {
      int[] tokens = {
          T_FORALL,
	  T_EXISTS,
          T_MAX,
          T_MIN,
          T_NUM_OF,
          T_PRODUCT,
          T_SUM
      };
    }

    public boolean isQuantifier(int tokenType) {
	return (jmlQuantifiers.get(tokenType));
    }


    /**
     * Build a BitSet from a list of bits. The list of bits is provided
     * as an int[].
     */
    public static BitSet buildFrom(int[] bits) {
	BitSet b = new BitSet();
	for (int i = 0; i < bits.length; i++) {
		b.set(bits[i]);
	}
	return b;
    }

    /**
     * Build a Hashtable of (String, Integer). The keys are the literals,
     * and the values are their (wrapped) integer token types. This is done
     * by specifying the Class where the fields come from, the list of field
     * names, and the translator. The given list of field must be a valid
     * list in the given Class, and the field must be of type int (or actually
     * java.lang.Integer is fine). The translator will translate the field
     * names to their literal counterpart (most of the times this is a simple
     * translation).
     */
    public static Hashtable buildFrom(Class c, String[] fields, FieldToLiteralTranslator t) throws Exception {
	Hashtable table = new Hashtable();
	for (int i = 0; i < fields.length; i++) {
		String literal = t.translate(fields[i]);
		Integer tokenType = (Integer) c.getField(fields[i]).get(c);
		table.put(literal, tokenType);
	}
	return table;
    }

    /**
     * The interface for objects translating a field name to a literal.
     * Used by Hashtable buildFrom(...).
     */
    private interface FieldToLiteralTranslator {
	String translate(String field);
    }

    public JmlLiteralsTable() {
	try {
		String[] fields;
		FieldToLiteralTranslator translator;

		fields = new String[] {
                        "ABRUPT_BEHAVIOR",
			"ACCESSIBLE",
			"ACCESSIBLE_REDUNDANTLY",
			"ALSO",
			"AND",
			"ASSIGNABLE",
			"ASSIGNABLE_REDUNDANTLY",
                        "ASSERT", // included so lexer will switch modes after
			"ASSERT_REDUNDANTLY",
			"ASSUME",
			"ASSUME_REDUNDANTLY",
			"AXIOM",
			"BEHAVIOR",
			"BREAKS",
			"BREAKS_REDUNDANTLY",
			"CALLABLE",
			"CALLABLE_REDUNDANTLY",
			"CHOOSE",
			"CHOOSE_IF",
			"CONSTRAINT",
			"CONSTRAINT_REDUNDANTLY",
			"CONTINUES",
			"CONTINUES_REDUNDANTLY",
			"DECREASES",
			"DECREASES_REDUNDANTLY",
			"DECREASING",
			"DECREASING_REDUNDANTLY",
			"DEPENDS",
			"DEPENDS_REDUNDANTLY",
			"DIVERGES",
			"DIVERGES_REDUNDANTLY",
			"ENSURES",
			"ENSURES_REDUNDANTLY",
			"EXAMPLE",
			"EXCEPTIONAL_BEHAVIOR",
			"EXCEPTIONAL_EXAMPLE",
			"EXSURES",
			"LABEL", //LB
			"LOOP_EXSURES", // LB
			"EXSURES_REDUNDANTLY",
			"FORALL",
			"FOR_EXAMPLE",
			"GHOST",
			"HENCE_BY",
			"HENCE_BY_REDUNDANTLY",
			"IMPLIES_THAT",
			"INITIALIZER",
			"INITIALLY",
			"INSTANCE",
			"INVARIANT",
			"INVARIANT_REDUNDANTLY",
			"LET",
			"LOOP_INVARIANT",
			"LOOP_INVARIANT_REDUNDANTLY",
			"MAINTAINING",
			"MAINTAINING_REDUNDANTLY",
			"MEASURED_BY",
			"MEASURED_BY_REDUNDANTLY",
			"MODEL",
			"MODEL_PROGRAM",
			"MODIFIABLE",
			"MODIFIABLE_REDUNDANTLY",
			"MODIFIES",
			"LOOP_MODIFIES", // LB
			"MODIFIES_REDUNDANTLY",
			"MONITORED",
			"MONITORED_BY",
			"NON_NULL",
			"NORMAL_BEHAVIOR",
			"NORMAL_EXAMPLE",
                        "OLD",
			"OR",
			"POST",
			"PRE",
			"PURE",
			"READABLE_IF",
			"REFINE",
			"REPRESENTS",
			"REPRESENTS_REDUNDANTLY",
			"REQUIRES",
			"REQUIRES_REDUNDANTLY",
			"RETURNS",
			"RETURNS_REDUNDANTLY",
			"SET",
			"SIGNALS",
			"SIGNALS_REDUNDANTLY",
			"SPEC_PROTECTED",
			"SPEC_PUBLIC",
			"STATIC_INITIALIZER",
			"SUBCLASSING_CONTRACT",
			"UNINITIALIZED",
			"UNREACHABLE",
			"WEAKLY",
			"WHEN",
			"WHEN_REDUNDANTLY"
		};
		translator = new FieldToLiteralTranslator() {
			public String translate(String field) {
				return field.toLowerCase();
			}
		};
	
		jmlKeywords = buildFrom(JavaTokenTypes.class, fields, translator);

		fields = new String[] {
			"T_ELEMTYPE",
			"T_EVERYTHING",
			"T_EXISTS",
			"T_FIELDS_OF",
			"T_FORALL",
			"T_FRESH",
                        "T_INVARIANT_FOR",
                        "T_IS_INITIALIZED",
			"T_LBLNEG",
			"T_LBLPOS",
			"T_LOCKSET",
                        "T_MAX",
                        "T_MIN",
			"T_NONNULLELEMENTS",
			"T_NOTHING",
                        "T_NUM_OF",
			"T_NOT_MODIFIED",
			"T_NOT_SPECIFIED",
			"T_OLD",
			"T_OTHER",
                        "T_PRODUCT",
			"T_REACH",
			"T_RESULT",
			"T_SUCH_THAT",
                        "T_SUM",
			"T_TYPE",
			"T_TYPEOF",
			"T_TYPEOFALLTYPES"
		};
		translator = new FieldToLiteralTranslator() {
			public String translate(String field) {
				return field.equals("T_TYPEOFALLTYPES")
                                    ? "\\TYPE"
                                    : "\\" + field.substring(2).toLowerCase();
			}
		};

		jmlBackslashKeywords = buildFrom(JavaTokenTypes.class, fields, translator);

		jmlSpecialTokenTypes = buildFrom(SpecialJMLTokenTypes.tokens);

		jmlQuantifiers = buildFrom(JmlQuantifierTokenTypes.tokens);

	} catch (Exception e) {
		throw new RuntimeException("Unexpected exception here: " + e);
	}
    }

  public int lookup(ANTLRStringBuffer text, int defaultType) {
	return lookup(jmlKeywords, text.toString(), defaultType);
  }

  public int backslash_lookup(ANTLRStringBuffer text, int defaultType) {
	return lookup(jmlBackslashKeywords, text.toString(), defaultType);
  }

  /**
   * Look up into a Hashtable of (String, Integer), with default value.
   */
  private static int lookup(Hashtable table, String key, int defaultValue) {
	Integer realValue = (Integer)table.get(key);
	return (realValue == null ? defaultValue : realValue.intValue());
  }

};

