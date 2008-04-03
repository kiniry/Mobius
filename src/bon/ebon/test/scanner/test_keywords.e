--
-- The Extended BON Tool Suite: BON Scanner Unit Tests
-- Copyright (C) 2001-2002 Joseph Kiniry
-- All Rights Reserved
--

--
-- $Id: test_keywords.e,v 1.1 2005/05/02 23:17:08 kiniry Exp $
--

indexing
   description: "Unit tests for the BON scanner."
   project:     "The Extended BON Tool Suite"
   author:      "Joseph R. Kiniry <kiniry@acm.org>"
   copyright:   "Copyright (C) 2001-2002 Joseph R. Kiniry"
   version:     "$Id: test_keywords.e,v 1.1 2005/05/02 23:17:08 kiniry Exp $"
   license:     "Eiffel Forum Freeware License v1 (see forum.txt)"

deferred class TEST_KEYWORDS
   -- A set of unit tests for the BON scanner focusing on scanning keywords.

inherit
   TS_TEST_CASE
      -- The base fixture class from getest.

   BON_TOKENS
      -- The set of BON tokens.

feature -- Data

   keyword_count: INTEGER is 65
         -- todo: figure out how to make this value non-hardcoded

   keyword_tokens: ARRAY[INTEGER] is
         -- Note that the order of this array is identical to the order of 
         -- the keywords in keyword_list.  If this is not true, the unit 
         -- tests will fail.
      local
         i: INTEGER
      do
         !! Result.make(1, keyword_count)
         i := 1
         Result.put(ACTION_TOKEN, i); i := i + 1
         Result.put(CREATOR_TOKEN, i); i := i + 1
         Result.put(FALSE_TOKEN, i); i := i + 1
         Result.put(NOT_TOKEN, i); i := i + 1
         Result.put(REUSED_TOKEN, i); i := i + 1
         Result.put(AND_TOKEN, i); i := i + 1
         Result.put(CURRENT_TOKEN, i); i := i + 1
         Result.put(FEATURE_TOKEN, i); i := i + 1
         Result.put(OBJECT_TOKEN, i); i := i + 1
         Result.put(ROOT_TOKEN, i); i := i + 1
         Result.put(CALLS_TOKEN, i); i := i + 1
         Result.put(DEFERRED_TOKEN, i); i := i + 1
         Result.put(FOR_ALL_TOKEN, i); i := i + 1
         Result.put(OBJECT_GROUP_TOKEN, i); i := i + 1
         Result.put(SCENARIO_TOKEN, i); i := i + 1
         Result.put(CLASS_TOKEN, i); i := i + 1
         Result.put(DELTA_TOKEN, i); i := i + 1
         Result.put(INCOMING_TOKEN, i); i := i + 1
         Result.put(OBJECT_STACK_TOKEN, i); i := i + 1
         Result.put(SCENARIO_CHART_TOKEN, i); i := i + 1
         Result.put(CLASS_CHART_TOKEN, i); i := i + 1
         Result.put(DESCRIPTION_TOKEN, i); i := i + 1
         Result.put(INDEXING_TOKEN, i); i := i + 1
         Result.put(OLD_TOKEN, i); i := i + 1
         Result.put(STATIC_DIAGRAM_TOKEN, i); i := i + 1
         Result.put(CLIENT_TOKEN, i); i := i + 1
         Result.put(DICTIONARY_TOKEN, i); i := i + 1
         Result.put(OR_TOKEN, i); i := i + 1
         Result.put(STRING_MARKS_TOKEN, i); i := i + 1
         Result.put(CLUSTER_TOKEN, i); i := i + 1
         Result.put(DYNAMIC_DIAGRAM_TOKEN, i); i := i + 1
         Result.put(INHERIT_TOKEN, i); i := i + 1
         Result.put(OUTGOING_TOKEN, i); i := i + 1
         Result.put(SUCH_THAT_TOKEN, i); i := i + 1
         Result.put(CLUSTER_CHART_TOKEN, i); i := i + 1
         Result.put(EFFECTIVE_TOKEN, i); i := i + 1
         Result.put(INTERFACED_TOKEN, i); i := i + 1
         Result.put(PART_TOKEN, i); i := i + 1
         Result.put(SYSTEM_CHART_TOKEN, i); i := i + 1
         Result.put(COMMAND_TOKEN, i); i := i + 1
         Result.put(END_TOKEN, i); i := i + 1
         Result.put(INVARIANT_TOKEN, i); i := i + 1
         Result.put(PERSISTENT_TOKEN, i); i := i + 1
         Result.put(TRUE_TOKEN, i); i := i + 1
         Result.put(COMPONENT_TOKEN, i); i := i + 1
         Result.put(ENSURE_TOKEN, i); i := i + 1
         Result.put(INVOLVES_TOKEN, i); i := i + 1
         Result.put(VOID_TOKEN, i); i := i + 1
         Result.put(CONCATENATOR_TOKEN, i); i := i + 1
         Result.put(EVENT_TOKEN, i); i := i + 1
         Result.put(IT_HOLDS_TOKEN, i); i := i + 1
         Result.put(QUERY_TOKEN, i); i := i + 1
         Result.put(XOR_TOKEN, i); i := i + 1
         Result.put(CONSTRAINT_TOKEN, i); i := i + 1
         Result.put(EVENT_CHART_TOKEN, i); i := i + 1
         Result.put(KEYWORD_PREFIX_TOKEN, i); i := i + 1
         Result.put(REDEFINED_TOKEN, i); i := i + 1
         Result.put(CREATES_TOKEN, i); i := i + 1
         Result.put(EXISTS_TOKEN, i); i := i + 1
         Result.put(MEMBER_OF_TOKEN, i); i := i + 1
         Result.put(REQUIRE_TOKEN, i); i := i + 1
         Result.put(CREATION_CHART_TOKEN, i); i := i + 1
         Result.put(EXPLANATION_TOKEN, i); i := i + 1
         Result.put(NAMELESS_TOKEN, i); i := i + 1
         Result.put(RESULT_TOKEN, i)
      end

   keyword_list: STRING is
         -- list of all pre-defined keywords in BON grammar.
      "%
      %action         creator         false          not          reused %
      %and            Current         feature        object       root %
      %calls          deferred        for_all        object_group scenario %
      %class          delta           incoming       object_stack scenario_chart %
      %class_chart    description     indexing       old          static_diagram %
      %client         dictionary                     or           string_marks %
      %cluster        dynamic_diagram inherit        outgoing     such_that %
      %cluster_chart  effective       interfaced     part         system_chart %
      %command        end             invariant      persistent   true %
      %component      ensure          involves                    Void %
      %concatenator   event           it_holds       query        xor %
      %constraint     event_chart     keyword_prefix redefined %
      %creates        exists          member_of      require %
      %creation_chart explanation     nameless       Result%
      % "
      
feature -- Test

   test_keywords is
         -- Scan all keywords.
      local
         scanner: BON_SCANNER
         i: INTEGER
      do
         !! scanner.make_scanner
         scanner.scan_string(keyword_list)
         from
            i := 1
         invariant 
            1 <= i and i <= keyword_count
         variant 
            keyword_count - i
         until 
            i = keyword_count
         loop
            scanner.read_token
            assert("keyword scan successful", not scanner.scanning_error)
            assert_equal("keyword identification",
                         token_name(keyword_tokens @ i),
                         token_name(scanner.last_token))
            i := i + 1
         end
      end

end -- class TEST_KEYWORDS

-- Local Variables:
-- mode:eiffel
-- End:
