%{
--
-- The Extended BON Tool Suite: Comment Parsing Point Experiment
-- Copyright (c) 2002 Joseph Kiniry
-- All Rights Reserved
--

--
-- $Id: comments.y,v 1.1 2005/05/02 22:58:28 kiniry Exp $
--

indexing
   description: "The Extended BON Parser: Comment Parsing Point Experiment."
   project:     "The Extended BON Tool Suite"
   author:      "Joseph R. Kiniry <kiniry@acm.org>"
   copyright:   "Copyright (C) 2002 Joseph R. Kiniry"
   version:     "$Id: comments.y,v 1.1 2005/05/02 22:58:28 kiniry Exp $"
   license:     "Eiffel Forum Freeware License v1 (see forum.txt)"

class BON_COMMENT_PARSER
   -- A point experiment parser for parsing comments in the BON specification 
   -- language.

inherit
   -- All core code for parser is in the skeleton.
   BON_PARSER_SKELETON

creation
   make_parser, execute, benchmark
%}

%token <STRING> SIMPLE_STRING_TOKEN
%token DOUBLE_DASH_TOKEN "--"

%%

-- Optional_Comment:  -- Empty
--                    | Comment ;

-- Comment: At_least_one_Line_comment ;

-- -- The following three rules will exhibit a shift/reduce conflict.

-- At_least_one_Line_comment: Line_Comment
--                            Optional_Line_comments ;

-- Optional_Line_comments: -- Empty
--                         | Optional_Line_comments Line_comment ;

-- Line_comment: DOUBLE_DASH_TOKEN SIMPLE_STRING_TOKEN ;

-- Dan's version.

Optional_Comment: -- Empty
       | DOUBLE_DASH_TOKEN SIMPLE_STRING_TOKEN ;

Comment: DOUBLE_DASH_TOKEN SIMPLE_STRING_TOKEN Optional_Comment ;


%%

end -- class BON_COMMENT_PARSER

-- Local Variables:
-- mode:eiffel
-- End:
