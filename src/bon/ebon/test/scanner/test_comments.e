--
-- The Extended BON Tool Suite: BON Scanner Unit Tests
-- Copyright (C) 2001-2002 Joseph Kiniry
-- All Rights Reserved
--

--
-- $Id: test_comments.e,v 1.1 2005/05/02 23:17:08 kiniry Exp $
--

indexing
   description: "Unit tests for the BON scanner."
   project:     "The Extended BON Tool Suite"
   author:      "Joseph R. Kiniry <kiniry@acm.org>"
   copyright:   "Copyright (C) 2001-2002 Joseph R. Kiniry"
   version:     "$Id: test_comments.e,v 1.1 2005/05/02 23:17:08 kiniry Exp $"
   license:     "Eiffel Forum Freeware License v1 (see forum.txt)"
   
   todo: "Need to add tests for comments at the EOL."

deferred class TEST_COMMENTS
   -- A set of unit tests for the BON scanner focusing on scanning comments.

inherit
   TS_TEST_CASE
      -- The base fixture class from getest.

   BON_TOKENS
      -- The set of BON tokens.

feature -- Data

   comment_input: STRING is
      "%
      %-- %N%
      %   -- %N%
      %                     --                     %N%
      % -- -- --  %N%
      %----------------------------------%N%
      %---------------------                              %N%
      %                                                                 %
      %                                                                 %
      %                                                                 %
      %                                                                 %
      %                                                                 %
      %                                                                 %
      %                                                                 %
      %                                                                 %
      %                                                                 %
      %                                                                 %
      %                                                                 %
      %                                                                 %
      %                                                                 %
      %                                                                 %
      %                                                                 %
      %                                                                 %
      %                                                            -- %N%
      % -- and or not // \\ ^ %N%
      % "

   comment_input_results: ARRAY[STRING] is
         -- Note that the order of this array is identical to the order of
         -- the comment strings in comment_input.  If this is not true, the
         -- unit tests will fail.
      local
         i: INTEGER
      do
         !! Result.make(1, comment_input_count)
         i := 1
         Result.put(" ", i); i := i + 1
         Result.put(" ", i); i := i + 1
         Result.put("                     ", i); i := i + 1
         Result.put(" -- --  ", i); i := i + 1
         Result.put("--------------------------------", i); i := i + 1
         Result.put("-------------------                              ", i); i := i + 1
         Result.put(" ", i); i := i + 1
         Result.put(" and or not // \\ ^ ", i)
      end

   comment_input_count: INTEGER is 9

feature -- Test

   test_comments is
         -- Test the only form of comments that exist in BON.
      local
         scanner: BON_SCANNER
         i: INTEGER
      do
         !! scanner.make_scanner
         scanner.scan_string(comment_input)
         from
            i := 1
         invariant 
            1 <= i and i <= comment_input_count
         variant 
            comment_input_count - i
         until 
            i = comment_input_count
         loop
            -- scan what should be a start-of-comment (DOUBLE_DASH_TOKEN)
            scanner.read_token
            assert("start-of-comment scan successful", 
                   not scanner.scanning_error)
            assert_equal("start-of-comment found",
                         token_name(DOUBLE_DASH_TOKEN),
                         token_name(scanner.last_token))

            -- scan what should be the the comment itself.
            scanner.read_token
            assert("comment scan successful", 
                   not scanner.scanning_error)
            assert_equal("comment found",
                         token_name(SIMPLE_STRING_TOKEN),
                         token_name(scanner.last_token))
            assert_equal("comment value correct",
                         comment_input_results @ i,
                         scanner.text)
            
            i := i + 1
         end
      end

end -- class TEST_COMMENTS

-- Local Variables:
-- mode:eiffel
-- End:
