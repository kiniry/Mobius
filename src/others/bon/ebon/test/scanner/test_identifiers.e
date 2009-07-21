--
-- The Extended BON Tool Suite: BON Scanner Unit Tests
-- Copyright (C) 2001-2002 Joseph Kiniry
-- All Rights Reserved
--

--
-- $Id: test_identifiers.e,v 1.1 2005/05/02 23:17:08 kiniry Exp $
--

indexing
   description: "Unit tests for the BON scanner."
   project:     "The Extended BON Tool Suite"
   author:      "Joseph R. Kiniry <kiniry@acm.org>"
   copyright:   "Copyright (C) 2001-2002 Joseph R. Kiniry"
   version:     "$Id: test_identifiers.e,v 1.1 2005/05/02 23:17:08 kiniry Exp $"
   license:     "Eiffel Forum Freeware License v1 (see forum.txt)"

   todo: "Rewrite these tests to use the same method as the others (data %
         %and token inputs, etc.)  This class was written prior to the %
         %others when we had not yet learned the ropes of getest."

deferred class TEST_IDENTIFIERS
   -- A set of unit tests for the BON scanner focusing on scanning identifiers.

inherit
   TS_TEST_CASE
      -- The base fixture class from getest.

   BON_TOKENS
      -- The set of BON tokens.

feature -- Test

   -- The Identifier construct is defined as a sequence of alphanumeric
   -- characters including underscore. An identifier must begin with an
   -- alphanumeric character and must not end with an underscore (whose
   -- purpose really is to mimic word separation). Letter case is not
   -- significant, but using consistent style rules is important.

   test_single_character_identifiers is
         -- Scans various single-character identifiers.
      local
         scanner: BON_SCANNER
      do
         -- lowercase
         !! scanner.make_scanner
         scanner.scan_string("a")
         scanner.read_token
         assert("lowercase single character identifier", 
                not scanner.scanning_error)
         assert_equal("must scan `a' as an identifier", 
                      token_name(IDENTIFIER_TOKEN), 
                      token_name(scanner.last_token))
         assert_equal("token text valid", 
                      "a", scanner.text)

         -- uppercase
         !! scanner.make_scanner
         scanner.scan_string("Z")
         scanner.read_token
         assert("uppercase single character identifier", 
                not scanner.scanning_error)
         assert_equal("must scan `Z' as an identifier", 
                      token_name(ALL_CAPS_IDENTIFIER_TOKEN), 
                      token_name(scanner.last_token))
         assert_equal("token text valid", 
                      "Z", scanner.text)

         -- todo: upper charset ASCII?

         -- illegal (non-alphanumeric)
         !! scanner.make_scanner
         scanner.scan_string("#")
         scanner.read_token
         assert("not alphanumeric", not scanner.scanning_error)
         assert_not_equal("must not scan `#' as an identifier", 
                          token_name(IDENTIFIER_TOKEN), 
                          token_name(scanner.last_token))
      end

   test_alphanumeric_identifiers is
         -- Scans various alphanumeric identifiers.
      local
         scanner: BON_SCANNER
      do
         -- Alphanumeric means that identifiers can start with a numeric?
         !! scanner.make_scanner
         scanner.scan_string("1a")
         scanner.read_token
         assert("numeric initial character", not scanner.scanning_error)
         assert_equal("must scan `1a' as an identifier", 
                      token_name(IDENTIFIER_TOKEN), 
                      token_name(scanner.last_token))
         assert_equal("token text valid", 
                      "1a", scanner.text)

         -- Large mixed identifier.
         !! scanner.make_scanner
         scanner.scan_string("ALKjfs8valsf")
         scanner.read_token
         assert("large mixed identifier", not scanner.scanning_error)
         assert_equal("must scan `ALKjfs8valsf' as an identifier", 
                      token_name(IDENTIFIER_TOKEN), 
                      token_name(scanner.last_token))
         assert_equal("token text valid", 
                      "ALKjfs8valsf", scanner.text)

         -- Initial numeric.
         !! scanner.make_scanner
         scanner.scan_string("809jsldg8sghsdf")
         scanner.read_token
         assert("initial numeric", not scanner.scanning_error)
         assert_equal("must scan `809jsldg8sghsdf' as an identifier", 
                      token_name(IDENTIFIER_TOKEN), 
                      token_name(scanner.last_token))
         assert_equal("token text valid", 
                      "809jsldg8sghsdf", scanner.text)

         -- All numeric (is not an identifier).
         !! scanner.make_scanner
         scanner.scan_string("456")
         scanner.read_token
         assert("all numeric", not scanner.scanning_error)
         assert_not_equal("must not scan `456' as an identifier", 
                          token_name(IDENTIFIER_TOKEN), 
                          token_name(scanner.last_token))
      end

   test_underscores is
         -- Scans various uses of underscores.
      local
         scanner: BON_SCANNER
      do
         -- Standard use of underscores.
         !! scanner.make_scanner
         scanner.scan_string("this_is_a_test")
         scanner.read_token
         assert("legal standard use of underscores", not scanner.scanning_error)
         assert_equal("must scan `this_is_a_test' as an identifier", 
                      token_name(IDENTIFIER_TOKEN), 
                      token_name(scanner.last_token))
         assert_equal("token text valid", 
                      "this_is_a_test", scanner.text)

         -- A typical class name.
         !! scanner.make_scanner
         scanner.scan_string("THIS_IS_A_CLASS_NAME")
         scanner.read_token
         assert("legal typical class name", not scanner.scanning_error)
         assert_equal("must scan `THIS_IS_A_CLASS_NAME' as an identifier", 
                      token_name(ALL_CAPS_IDENTIFIER_TOKEN), 
                      token_name(scanner.last_token))
         assert_equal("token text valid", 
                      "THIS_IS_A_CLASS_NAME", scanner.text)

         -- A bag of everything.
         !! scanner.make_scanner
         scanner.scan_string("THIS_is_a_CLASS_NAME_666")
         scanner.read_token
         assert("bag of everything", not scanner.scanning_error)
         assert_equal("must scan `THIS_is_a_CLASS_NAME_666' as an identifier", 
                      token_name(IDENTIFIER_TOKEN), 
                      token_name(scanner.last_token))
         assert_equal("token text valid", 
                      "THIS_is_a_CLASS_NAME_666", scanner.text)

         -- Must not end with an underscore.
         !! scanner.make_scanner
         scanner.scan_string("A_B_C_")
         scanner.read_token
         assert("must not end with underscore", not scanner.scanning_error)
         assert_equal("must not scan `A_B_C_' as an identifier", 
                      token_name(ALL_CAPS_IDENTIFIER_TOKEN), 
                      token_name(scanner.last_token))
         -- final `_' is dropped but will cause next read_token to fail.
         assert_equal("token text valid", 
                      "A_B_C", scanner.text)
         scanner.read_token
      end

end -- class TEST_IDENTIFIERS

-- Local Variables:
-- mode:eiffel
-- End:
