--
-- The Extended BON Tool Suite: BON Scanner Unit Tests
-- Copyright (C) 2001-2002 Joseph Kiniry
-- All Rights Reserved
--

--
-- $Id: test_strings.e,v 1.1 2005/05/02 23:17:08 kiniry Exp $
--

indexing
   description: "Unit tests for the BON scanner."
   project:     "The Extended BON Tool Suite"
   author:      "Joseph R. Kiniry <kiniry@acm.org>"
   copyright:   "Copyright (C) 2001-2002 Joseph R. Kiniry"
   version:     "$Id: test_strings.e,v 1.1 2005/05/02 23:17:08 kiniry Exp $"
   license:     "Eiffel Forum Freeware License v1 (see forum.txt)"

deferred class TEST_STRINGS
   -- A set of unit tests for the BON scanner focusing on scanning strings.

inherit
   TS_TEST_CASE
      -- The base fixture class from getest.

   BON_TOKENS
      -- The set of BON tokens.

   UT_CHARACTER_CODES
      -- Used to specify character codes for single-character
      -- terminals/tokens in a portable way.

feature -- Data

   -- Recall that BON does not used escaped character sequences in strings
   -- like Eiffel or C.  Instead, the string delimiters can be changed
   -- using the string_marks keyword which is tested in
   -- test_notational_tuning.e.  Note also that Manifest_textblocks are not
   -- scanned but parsed, thus are tested by unit tests in the test_parser
   -- cluster.

   string_input: STRING is
         -- In order:
         --  simple string
         --  zero length string
         --  complex string
         --  embedded butting single quotes
         --  embedded single char single quotes
         --  embedded multi-char single quotes
         --  embedded control codes
         --  concatenation/continuation characters
      "%
      %  %"simple string%"       %
      %  %"ab13 #$*+%"           %
      %  %"abc''123%"            %
      %  %"321'-'xyz%"           %
      %  %"poiuy'trewq'=-09%"    %
      %  %"abc%%N%%F%N%N%"       %
      %  %"a quick brown fox\%N  %
      %      \ jumped over \%N%N %
      %     \the lazy dog.%"     %
      % "

   string_input_results: ARRAY[STRING] is
         -- Note that the order of this array is identical to the order of
         -- the comment strings in comment_input.  If this is not true, the
         -- unit tests will fail.
      local
         i: INTEGER
      do
         !! Result.make(1, string_input_count)
         i := 1
         Result.put("simple string", i); i := i + 1
         Result.put("ab13 #$*+", i); i := i + 1
         Result.put("abc''123", i); i := i + 1
         Result.put("321'-'xyz", i); i := i + 1
         Result.put("poiuy'trewq'=-09", i); i := i + 1
         Result.put("abc%%N%%F%N%N", i); i := i + 1
         Result.put("a quick brown fox jumped over the lazy dog.", i)
      end

   string_input_count: INTEGER is 7

feature -- Test

   test_strings is
         -- Test a variety of strings.
      local
         scanner: BON_SCANNER
         i: INTEGER
      do
         !! scanner.make_scanner
         scanner.scan_string(string_input)
         from
            i := 1
         invariant 
            1 <= i and i <= string_input_count
         variant 
            string_input_count - i
         until 
            i = string_input_count
         loop
            -- scan what should be a start-of-string delimiter
            scanner.read_token
            assert("start-of-string scan successful", 
                   not scanner.scanning_error)
            assert_equal("string delimiter found",
                         token_name(STRING_DELIMITER_TOKEN),
                         token_name(scanner.last_token))

            -- scan what should be the the string itself.
            scanner.read_token
            assert("string scan successful", 
                   not scanner.scanning_error)
            assert_equal("string found",
                         token_name(SIMPLE_STRING_TOKEN),
                         token_name(scanner.last_token))
            assert_equal("string value correct",
                         string_input_results @ i,
                         scanner.last_string_constant)
            
            -- scan what should be a end-of-string delimiter
            scanner.read_token
            assert("end-of-string scan successful", 
                   not scanner.scanning_error)
            assert_equal("string delimiter found",
                         token_name(STRING_DELIMITER_TOKEN),
                         token_name(scanner.last_token))

            i := i + 1
         end
      end

end -- class TEST_STRINGS

-- Local Variables:
-- mode:eiffel
-- End:
