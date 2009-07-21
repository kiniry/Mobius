--
-- The Extended BON Tool Suite: BON Scanner Unit Tests
-- Copyright (C) 2001-2002 Joseph Kiniry
-- All Rights Reserved
--

--
-- $Id: test_misc.e,v 1.1 2005/05/02 23:17:08 kiniry Exp $
--

indexing
   description: "Unit tests for the BON scanner."
   project:     "The Extended BON Tool Suite"
   author:      "Joseph R. Kiniry <kiniry@acm.org>"
   copyright:   "Copyright (C) 2001-2002 Joseph R. Kiniry"
   version:     "$Id: test_misc.e,v 1.1 2005/05/02 23:17:08 kiniry Exp $"
   license:     "Eiffel Forum Freeware License v1 (see forum.txt)"

deferred class TEST_MISC
   -- A set of unit tests for the BON scanner.

inherit
   TS_TEST_CASE
      -- The base fixture class from getest.

feature -- Test

   test_boundary_cases is
         -- Test boundary cases on scanner.
      local
         scanner: BON_SCANNER
      do
         !! scanner.make_scanner
         scanner.scan_string("")
         assert("blank", not scanner.scanning_error)
      end

end -- class TEST_MISC

-- Local Variables:
-- mode:eiffel
-- End:
