--
-- The Extended BON Tool Suite: BON Scanner Unit Tests
-- Copyright (C) 2001-2002 Joseph Kiniry
-- All Rights Reserved
--

--
-- $Id: test_free_operators.e,v 1.1 2005/05/02 23:17:08 kiniry Exp $
--

indexing
   description: "Unit tests for the BON scanner."
   project:     "The Extended BON Tool Suite"
   author:      "Joseph R. Kiniry <kiniry@acm.org>"
   copyright:   "Copyright (C) 2001-2002 Joseph R. Kiniry"
   version:     "$Id: test_free_operators.e,v 1.1 2005/05/02 23:17:08 kiniry Exp $"
   license:     "Eiffel Forum Freeware License v1 (see forum.txt)"

deferred class TEST_FREE_OPERATORS
   -- A set of unit tests for the BON scanner focusing on scanning free operators.

inherit
   TS_TEST_CASE
      -- The base fixture class from getest.

   BON_TOKENS
      -- The set of BON tokens.

   UT_CHARACTER_CODES
      -- Used to specify character codes for single-character
      -- terminals/tokens in a portable way.

feature -- Data

   free_operator_count: INTEGER is 29
         -- todo: figure out how to make this value non-hardcoded

   free_operator_tokens: ARRAY[INTEGER] is
         -- Note that the order of this array is identical to the order of
         -- the tokens in free_operator_list.  If this is not true, the
         -- unit tests will fail.
      local
         i: INTEGER
      do
         -- Need four times the space because each declaration requires 
         -- four tokens.
         !! Result.make(1, 4 * free_operator_count)
         i := 1
         Result.put(PREFIX_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1
         Result.put(FREE_OPERATOR_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1

         Result.put(INFIX_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1
         Result.put(FREE_OPERATOR_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1

         Result.put(PREFIX_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1
         Result.put(FREE_OPERATOR_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1

         Result.put(INFIX_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1
         Result.put(FREE_OPERATOR_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1

         -- Pre-defined prefix operators tests

         Result.put(PREFIX_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1
         Result.put(DELTA_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1

         Result.put(PREFIX_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1
         Result.put(OLD_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1

         Result.put(PREFIX_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1
         Result.put(NOT_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1

         Result.put(PREFIX_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1
         Result.put(Plus_code, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1

         Result.put(PREFIX_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1
         Result.put(Minus_code, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1

         -- Pre-defined infix operators tests

         Result.put(INFIX_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1
         Result.put(Plus_code, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1

         Result.put(INFIX_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1
         Result.put(Minus_code, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1

         Result.put(INFIX_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1
         Result.put(Star_code, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1

         Result.put(INFIX_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1
         Result.put(Slash_code, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1

         Result.put(INFIX_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1
         Result.put(Less_than_code, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1

         Result.put(INFIX_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1
         Result.put(Greater_than_code, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1

         Result.put(INFIX_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1
         Result.put(LESS_THAN_OR_EQUAL_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1

         Result.put(INFIX_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1
         Result.put(GREATER_THAN_OR_EQUAL_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1

         Result.put(INFIX_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1
         Result.put(Equal_code, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1

         Result.put(INFIX_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1
         Result.put(NOT_EQUAL_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1

         Result.put(INFIX_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1
         Result.put(DOUBLE_SLASH_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1

         Result.put(INFIX_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1
         Result.put(DOUBLE_BACKSLASH_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1

         Result.put(INFIX_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1
         Result.put(Caret_code, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1

         Result.put(INFIX_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1
         Result.put(OR_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1

         Result.put(INFIX_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1
         Result.put(XOR_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1

         Result.put(INFIX_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1
         Result.put(AND_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1

         Result.put(INFIX_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1
         Result.put(IMPLIES_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1

         Result.put(INFIX_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1
         Result.put(EQUIVALENT_TO_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1

         Result.put(INFIX_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1
         Result.put(MEMBER_OF_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1

         Result.put(INFIX_TOKEN, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1
         Result.put(Colon_code, i); i := i + 1
         Result.put(Double_quote_code, i); i := i + 1
      end

   free_operator_results: ARRAY[STRING] is
         -- Note that the order of this array is identical to the order of
         -- the comment strings in comment_input.  If this is not true, the
         -- unit tests will fail.
      local
         i: INTEGER
      do
         !! Result.make(1, free_operator_count)
         i := 1
         -- Miscellaneous tests
         Result.put("@pre", i); i := i + 1
         Result.put("cross", i); i := i + 1
         Result.put("  a prefix symbol  ", i); i := i + 1
         Result.put("product", i); i := i + 1
         -- Pre-defined prefix operators tests
         Result.put("delta", i); i := i + 1
         Result.put("old", i); i := i + 1
         Result.put("not", i); i := i + 1
         Result.put("+", i); i := i + 1
         Result.put("-", i); i := i + 1
         -- Pre-defined infix operators tests
         Result.put("+", i); i := i + 1
         Result.put("-", i); i := i + 1
         Result.put("*", i); i := i + 1
         Result.put("/", i); i := i + 1
         Result.put("<", i); i := i + 1
         Result.put(">", i); i := i + 1
         Result.put("<=", i); i := i + 1
         Result.put(">=", i); i := i + 1
         Result.put("=", i); i := i + 1
         Result.put("/=", i); i := i + 1
         Result.put("//", i); i := i + 1
         Result.put("\\", i); i := i + 1
         Result.put("^", i); i := i + 1
         Result.put("or", i); i := i + 1
         Result.put("xor", i); i := i + 1
         Result.put("and", i); i := i + 1
         Result.put("->", i); i := i + 1
         Result.put("<->", i); i := i + 1
         Result.put("member_of", i); i := i + 1
         Result.put(":", i)
      end

   free_operator_list: STRING is
         -- List of free operator declarations to test.  Make sure to 
         -- cover all pre-defined prefix and infix free operators.
      "%
      % prefix %"@pre%" %N %
      % infix %"cross%" %N %
      %             prefix        %"  a prefix symbol  %"        %N %
      %       infix      %"product%"  %N %
      % prefix %"delta%"   %N %
      % prefix %"old%"     %N %
      % prefix %"not%"     %N %
      % prefix %"+%"       %N %
      % prefix %"-%"       %N %
      % infix %"+%"        %N %
      % infix %"-%"        %N %
      % infix %"*%"        %N %
      % infix %"/%"        %N %
      % infix %"<%"        %N %
      % infix %">%"        %N %
      % infix %"<=%"       %N %
      % infix %">=%"       %N %
      % infix %"=%"        %N %
      % infix %"/=%"       %N %
      % infix %"//%"       %N %
      % infix %"\\%"       %N %
      % infix %"^%"        %N %
      % infix %"or%"       %N %
      % infix %"xor%"      %N %
      % infix %"and%"      %N %
      % infix %"->%"       %N %
      % infix %"<->%"      %N %
      % infix %"member_of%"   %N%
      % infix %":%"        %N %
      % "
        
feature -- Test

   test_free_operator_declarations is
         -- Tests the declaration of free operators
      local
         scanner: BON_SCANNER
         i, j: INTEGER
      do
         !! scanner.make_scanner
         scanner.scan_string(free_operator_list)
         from
            i := 1; j := 1
         invariant 
            1 <= i and i <= 4 * free_operator_count + 1
         variant 
            4 * free_operator_count + 1 - i
         until 
            i >= 4 * free_operator_count
         loop
            -- scan in free operator declaration keyword
            scanner.read_token
            assert("free operator declaration keyword scan successful", 
                   not scanner.scanning_error)
            assert_equal("free operator identification",
                         token_name(free_operator_tokens @ i),
                         token_name(scanner.last_token))
            i := i + 1

            -- scan in delimiter
            scanner.read_token
            assert("free operator delimiter scan successful", 
                   not scanner.scanning_error)
            assert_equal("free operator delimiter",
                         token_name(free_operator_tokens @ i),
                         token_name(scanner.last_token))
            i := i + 1

            -- scan in free operator
            scanner.read_token
            assert("free operator identifier scan successful", 
                   not scanner.scanning_error)
            assert_equal("free operator identifier value",
                         free_operator_results @ j,
                         scanner.last_free_operator)
            i := i + 1; j := j + 1

            -- scan in delimiter
            scanner.read_token
            assert("free operator delimiter scan successful", 
                   not scanner.scanning_error)
            assert_equal("free operator delimiter",
                         token_name(free_operator_tokens @ i),
                         token_name(scanner.last_token))
            i := i + 1
         end
      end

end -- class TEST_FREE_OPERATORS

-- Local Variables:
-- mode:eiffel
-- End:
