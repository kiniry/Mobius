--
-- The Extended BON Tool Suite: BON Scanner Unit Tests
-- Copyright (C) 2001-2002 Joseph Kiniry
-- All Rights Reserved
--

--
-- $Id: test_special_symbols.e,v 1.1 2005/05/02 23:17:08 kiniry Exp $
--

indexing
   description: "Unit tests for the BON scanner."
   project:     "The Extended BON Tool Suite"
   author:      "Joseph R. Kiniry <kiniry@acm.org>"
   copyright:   "Copyright (C) 2001-2002 Joseph R. Kiniry"
   version:     "$Id: test_special_symbols.e,v 1.1 2005/05/02 23:17:08 kiniry Exp $"
   license:     "Eiffel Forum Freeware License v1 (see forum.txt)"

deferred class TEST_SPECIAL_SYMBOLS
   -- A set of unit tests for the BON scanner focusing on scanning special symbols.

inherit
   TS_TEST_CASE
      -- The base fixture class from getest.
   
   BON_TOKENS
      -- The set of BON tokens.

   UT_CHARACTER_CODES
      -- Used to specify character codes for single-character
      -- terminals/tokens in a portable way.

feature -- Data

   special_symbols_count: INTEGER is 28

   special_symbols_list: STRING is
         -- list of all pre-defined special symbols in BON grammar.
      ", ; ( ) [ ] { } + - * / // \\ ^ < > = <= >= /= -> <-> . .. : :{ ..."
      --                 ^                      ^                      ^
      --                 10                     20                     28

   special_symbols_tokens: ARRAY[INTEGER] is
         -- Note that the order of this array is identical to the order of 
         -- the symbols in special_symbol_list.  If this is not true, the unit 
         -- tests will fail.
      local
         i: INTEGER
      do
         i := 1
         !! Result.make(1, special_symbols_count)
         Result.put(Comma_code, i); i := i + 1
         Result.put(Semicolon_code, i); i := i + 1
         Result.put(Left_parenthesis_code, i); i := i + 1
         Result.put(Right_parenthesis_code, i); i := i + 1
         Result.put(Left_bracket_code, i); i := i + 1
         Result.put(Right_bracket_code, i); i := i + 1
         Result.put(Left_brace_code, i); i := i + 1
         Result.put(Right_brace_code, i); i := i + 1
         Result.put(Plus_code, i); i := i + 1
         Result.put(Minus_code, i); i := i + 1
         Result.put(Star_code, i); i := i + 1
         Result.put(Slash_code, i); i := i + 1
         Result.put(DOUBLE_SLASH_TOKEN, i); i := i + 1
         Result.put(DOUBLE_BACKSLASH_TOKEN, i); i := i + 1
         Result.put(Caret_code, i); i := i + 1
         Result.put(Less_than_code, i); i := i + 1
         Result.put(Greater_than_code, i); i := i + 1
         Result.put(Equal_code, i); i := i + 1
         Result.put(LESS_THAN_OR_EQUAL_TOKEN, i); i := i + 1
         Result.put(GREATER_THAN_OR_EQUAL_TOKEN, i); i := i + 1
         Result.put(NOT_EQUAL_TOKEN, i); i := i + 1
         Result.put(IMPLIES_TOKEN, i); i := i + 1
         Result.put(EQUIVALENT_TO_TOKEN, i); i := i + 1
         Result.put(Dot_code, i); i := i + 1
         Result.put(DOUBLE_DOT_TOKEN, i); i := i + 1
         Result.put(Colon_code, i); i := i + 1
         Result.put(AGGREGATE_MARK_TOKEN, i); i := i + 1
         Result.put(ELLIPSES_TOKEN, i)
      end

feature -- Test

   test_special_symbols is
         -- Scan all special symbols.
      local
         scanner: BON_SCANNER
         i: INTEGER
      do
         !! scanner.make_scanner
         scanner.scan_string(special_symbols_list)
         from
            i := 1
         invariant 
            1 <= i and i <= special_symbols_count
         variant 
            special_symbols_count - i
         until 
            i = special_symbols_count
         loop
            scanner.read_token
            assert("symbol scan successful", not scanner.scanning_error)
            assert_equal("special symbol identification",
                         token_name(special_symbols_tokens @ i),
                         token_name(scanner.last_token))
            i := i + 1
         end
      end

end -- class TEST_SPECIAL_SYMBOLS

-- Local Variables:
-- mode:eiffel
-- End:
