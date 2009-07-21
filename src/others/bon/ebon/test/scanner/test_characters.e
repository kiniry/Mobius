--
-- The Extended BON Tool Suite: BON Scanner Unit Tests
-- Copyright (C) 2001-2002 Joseph Kiniry
-- All Rights Reserved
--

--
-- $Id: test_characters.e,v 1.1 2005/05/02 23:17:08 kiniry Exp $
--

indexing
   description: "Unit tests for the BON scanner."
   project:     "The Extended BON Tool Suite"
   author:      "Joseph R. Kiniry <kiniry@acm.org>"
   copyright:   "Copyright (C) 2001-2002 Joseph R. Kiniry"
   version:     "$Id: test_characters.e,v 1.1 2005/05/02 23:17:08 kiniry Exp $"
   license:     "Eiffel Forum Freeware License v1 (see forum.txt)"

deferred class TEST_CHARACTERS
   -- A set of unit tests for the BON scanner focusing on scanning characters.

inherit
   TS_TEST_CASE
      -- The base fixture class from getest.

   BON_TOKENS
      -- The set of BON tokens.

   UT_CHARACTER_CODES
      -- Used to specify character codes for single-character
      -- terminals/tokens in a portable way.

feature -- Data

   character_count: INTEGER is 5

   character_input: STRING is
      " 'a'     ' '    '%"'     '''     '_'     "

   character_results: STRING is "a %"'_"
         -- Note that the order of this array is identical to the order of
         -- the comment strings in comment_input.  If this is not true, the
         -- unit tests will fail.

feature -- Test

   test_characters is
         -- Tests for scanning characters.
      local
         scanner: BON_SCANNER
         i: INTEGER
      do
         !! scanner.make_scanner
         scanner.scan_string(character_input)
         from
            i := 1
         invariant 
            1 <= i and i <= character_count
         variant 
            character_count - i
         until 
            i = character_count
         loop
            -- scan what should be a start-of-character delimiter
            scanner.read_token
            assert("start-of-character scan successful", 
                   not scanner.scanning_error)
            assert_equal("character delimiter found",
                         Single_quote_code, scanner.last_token)

            -- scan what should be the the character itself.
            scanner.read_token
            assert("character scan successful", 
                   not scanner.scanning_error)
            assert_equal("character found",
                         token_name(CHARACTER_TOKEN),
                         token_name(scanner.last_token))
            assert_equal("character value correct",
                         character_results @ i,
                         scanner.last_character_constant)
            
            -- scan what should be a end-of-character delimiter
            scanner.read_token
            assert("end-of-character scan successful", 
                   not scanner.scanning_error)
            assert_equal("character delimiter found",
                         Single_quote_code, scanner.last_token)

            i := i + 1
         end
      end

end -- class TEST_CHARACTERS

-- Local Variables:
-- mode:eiffel
-- End:
