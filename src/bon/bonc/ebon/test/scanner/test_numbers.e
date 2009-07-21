--
-- The Extended BON Tool Suite: BON Scanner Unit Tests
-- Copyright (C) 2001-2002 Joseph Kiniry
-- All Rights Reserved
--

--
-- $Id: test_numbers.e,v 1.1 2005/05/02 23:17:08 kiniry Exp $
--

indexing
   description: "Unit tests for the BON scanner."
   project:     "The Extended BON Tool Suite"
   author:      "Joseph R. Kiniry <kiniry@acm.org>"
   copyright:   "Copyright (C) 2001-2002 Joseph R. Kiniry"
   version:     "$Id: test_numbers.e,v 1.1 2005/05/02 23:17:08 kiniry Exp $"
   license:     "Eiffel Forum Freeware License v1 (see forum.txt)"

   todo: "Rewrite these tests to use the same method as the others (data %
         %and token inputs, etc.)  This class was written prior to the %
         %others when we had not yet learned the ropes of getest."

deferred class TEST_NUMBERS
   -- A set of unit tests for the BON scanner focusing on scanning numbers.

inherit
   TS_TEST_CASE
      -- The base fixture class from getest.

   BON_TOKENS
      -- The set of BON tokens.

feature -- Test

   -- todo: generate random integers and scan them?

   test_integers is
         -- Scans integers.
      local
         scanner: BON_SCANNER
      do
         -- positive numbers

         !! scanner.make_scanner
         scanner.scan_string("123")
         scanner.read_token
         assert("small integer: 123", 
                not scanner.scanning_error)
         assert_equal("must scan `123' as an integer", 
                      token_name(INTEGER_TOKEN), 
                      token_name(scanner.last_token))
         assert_equal("token text valid", 
                      "123", scanner.text)

         !! scanner.make_scanner
         scanner.scan_string("+42")
         scanner.read_token
         assert("small integer: +42", 
                not scanner.scanning_error)
         assert_equal("must scan `+42' as an integer", 
                      token_name(INTEGER_TOKEN), 
                      token_name(scanner.last_token))
         assert_equal("token text valid", 
                      "+42", scanner.text)

         -- note that scanned integers and reals are automatically converted 
         -- to their proper values, so these values must be legal (i.e. 
         -- not too large).

         !! scanner.make_scanner
         scanner.scan_string("1234567890")
         scanner.read_token
         assert("large integer: 1234567890", 
                not scanner.scanning_error)
         assert_equal("must scan `1234567890' as an integer", 
                      token_name(INTEGER_TOKEN), 
                      token_name(scanner.last_token))
         assert_equal("token text valid", 
                      "1234567890", scanner.text)

         -- negative numbers

         !! scanner.make_scanner
         scanner.scan_string("-1")
         scanner.read_token
         assert("small integer: -1", 
                not scanner.scanning_error)
         assert_equal("must scan `-1' as an integer", 
                      token_name(INTEGER_TOKEN), 
                      token_name(scanner.last_token))
         assert_equal("token text valid", 
                      "-1", scanner.text)

         !! scanner.make_scanner
         scanner.scan_string("-239827349")
         scanner.read_token
         assert("small integer: -239827349", 
                not scanner.scanning_error)
         assert_equal("must scan `-239827349' as an integer", 
                      token_name(INTEGER_TOKEN), 
                      token_name(scanner.last_token))
         assert_equal("token text valid", 
                      "-239827349", scanner.text)
      end

   test_reals is
         -- Scans real numbers.
      local
         scanner: BON_SCANNER
      do
         -- positive real numbers

         !! scanner.make_scanner
         scanner.scan_string("123.456")
         scanner.read_token
         assert("small real: 123.456", 
                not scanner.scanning_error)
         assert_equal("must scan `123.456' as a real", 
                      token_name(REAL_TOKEN), 
                      token_name(scanner.last_token))
         assert_equal("token text valid", 
                      "123.456", scanner.text)

         !! scanner.make_scanner
         scanner.scan_string("+42.001")
         scanner.read_token
         assert("small real: +42.001", 
                not scanner.scanning_error)
         assert_equal("must scan `+42.001' as a real", 
                      token_name(REAL_TOKEN), 
                      token_name(scanner.last_token))
         assert_equal("token text valid", 
                      "+42.001", scanner.text)

         !! scanner.make_scanner
         scanner.scan_string("1234567890123456789.012345678901234567890")
         scanner.read_token
         assert("large real: 1234567890123456789.012345678901234567890", 
                not scanner.scanning_error)
         assert_equal("must scan `1234567890123456789.012345678901234567890' as a real", 
                      token_name(REAL_TOKEN), 
                      token_name(scanner.last_token))
         assert_equal("token text valid", 
                      "1234567890123456789.012345678901234567890", scanner.text)

         !! scanner.make_scanner
         scanner.scan_string("-0001.0000")
         scanner.read_token
         assert("leading and trailing zeros real: -0001.0000", 
                not scanner.scanning_error)
         assert_equal("must scan `-0001.0000' as a real",
                      token_name(REAL_TOKEN), 
                      token_name(scanner.last_token))
         assert_equal("token text valid", 
                      "-0001.0000", scanner.text)
      end

   test_boundary_cases is
         -- Scans boundary case integers and reals.
      local
         scanner: BON_SCANNER
      do
         -- Zeros.

         !! scanner.make_scanner
         scanner.scan_string("+0")
         scanner.read_token
         assert("small integer: +0", 
                not scanner.scanning_error)
         assert_equal("must scan `+0' as an integer", 
                      token_name(INTEGER_TOKEN), 
                      token_name(scanner.last_token))
         assert_equal("token text valid", 
                      "+0", scanner.text)

         !! scanner.make_scanner
         scanner.scan_string("-0")
         scanner.read_token
         assert("small integer: -0", 
                not scanner.scanning_error)
         assert_equal("must scan `-0' as an integer", 
                      token_name(INTEGER_TOKEN), 
                      token_name(scanner.last_token))
         assert_equal("token text valid", 
                      "-0", scanner.text)

         !! scanner.make_scanner
         scanner.scan_string("+-0")
         scanner.read_token
         assert("illegal small integer: +-0", 
                not scanner.scanning_error)
         assert_not_equal("must not scan `+-0' as an integer", 
                          token_name(INTEGER_TOKEN), 
                          token_name(scanner.last_token))
         assert_equal("should just scan `+' sign", 
                      "+", scanner.text)

         !! scanner.make_scanner
         scanner.scan_string("-+123")
         scanner.read_token
         assert("illegal small integer: -+123", 
                not scanner.scanning_error)
         assert_not_equal("must not scan `-+123' as an integer", 
                          token_name(INTEGER_TOKEN), 
                          token_name(scanner.last_token))

         -- zero prefixed
         !! scanner.make_scanner
         scanner.scan_string("+000123")
         scanner.read_token
         assert("small integer: +000123", 
                not scanner.scanning_error)
         assert_equal("must scan `+000123' as an integer", 
                      token_name(INTEGER_TOKEN), 
                      token_name(scanner.last_token))
         assert_equal("token text valid", 
                      "+000123", scanner.text)

         -- zero suffixed
         !! scanner.make_scanner
         scanner.scan_string("-123000")
         scanner.read_token
         assert("small integer: -123000", 
                not scanner.scanning_error)
         assert_equal("must scan `-123000' as an integer", 
                      token_name(INTEGER_TOKEN), 
                      token_name(scanner.last_token))
         assert_equal("token text valid", 
                      "-123000", scanner.text)

         -- zeros at both ends
         !! scanner.make_scanner
         scanner.scan_string("-000123000")
         scanner.read_token
         assert("small integer: -000123000", 
                not scanner.scanning_error)
         assert_equal("must scan `-000123000' as an integer", 
                      token_name(INTEGER_TOKEN), 
                      token_name(scanner.last_token))
         assert_equal("token text valid", 
                      "-000123000", scanner.text)
      end

end -- class TEST_NUMBERS

-- Local Variables:
-- mode:eiffel
-- End:
