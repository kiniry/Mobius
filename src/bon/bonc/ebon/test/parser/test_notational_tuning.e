--
-- The Extended BON Tool Suite: BON Scanner Unit Tests
-- Copyright (C) 2001-2002 Joseph Kiniry
-- All Rights Reserved
--

--
-- $Id: test_notational_tuning.e,v 1.1 2005/05/02 23:17:00 kiniry Exp $
--

indexing
   description: "Unit tests for the Extended BON parser."
   project:     "The Extended BON Tool Suite"
   author:      "Joseph R. Kiniry <kiniry@acm.org>"
   copyright:   "Copyright (C) 2001-2002 Joseph R. Kiniry"
   version:     "$Id: test_notational_tuning.e,v 1.1 2005/05/02 23:17:00 kiniry Exp $"
   license:     "Eiffel Forum Freeware License v1 (see forum.txt)"

deferred class TEST_NOTATIONAL_TUNING
   -- A set of unit tests for the BON parser.

inherit
   -- The base fixture class from getest.
   TS_TEST_CASE

feature -- Test

   test_notational_tuning is
         -- Test the notational tuning features of BON.
      do
         assert("Empty assertion to make parser testing not complain.", true)
      end

end -- class TEST_NOTATIONAL_TUNING

-- Local Variables:
-- mode:eiffel
-- End:
