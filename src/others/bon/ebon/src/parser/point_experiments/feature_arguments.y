%{
--
-- The Extended BON Tool Suite: Feature Arguments Parsing Point Experiment
-- Copyright (c) 2002 Joseph Kiniry
-- All Rights Reserved
--

--
-- $Id: feature_arguments.y,v 1.1 2005/05/02 22:58:28 kiniry Exp $
--

indexing
   description: "The Extended BON Parser: Feature Arguments Parsing Point Experiment."
   project:     "The Extended BON Tool Suite"
   author:      "Joseph R. Kiniry <kiniry@acm.org>"
   copyright:   "Copyright (C) 2002 Joseph R. Kiniry"
   version:     "$Id: feature_arguments.y,v 1.1 2005/05/02 22:58:28 kiniry Exp $"
   license:     "Eiffel Forum Freeware License v1 (see forum.txt)"

class BON_FEATURE_ARGUMENTS_PARSER
   -- A point experiment parser for parsing feature arguments in the BON
   -- specification language.

inherit
   -- All core code for parser is in the skeleton.
   BON_PARSER_SKELETON

creation
   make_parser, execute, benchmark
%}

%token <STRING> IDENTIFIER_TOKEN CLASS_NAME_TOKEN ALL_CAPS_IDENTIFIER_TOKEN
%right IMPLIES_TOKEN

%%

Feature_arguments: At_least_one_Feature_argument ;

At_least_one_Feature_argument: Feature_argument
                               Optional_Feature_arguments ;

Optional_Feature_arguments: -- Empty
                            | Optional_Feature_arguments Feature_argument ;

Feature_argument: IMPLIES_TOKEN Optional_Identifier_list Type ;

Optional_Identifier_list: -- Empty
                          | Identifier_list ':' ;

Identifier_list: At_least_one_Identifier ;

At_least_one_Identifier: IDENTIFIER_TOKEN 
                         Optional_Identifiers ;

Optional_Identifiers: -- Empty
                      | Optional_Identifiers ',' IDENTIFIER_TOKEN ;

Class_type: Class_name Optional_Actual_generics ;

Optional_Actual_generics: -- Empty
                          | Actual_generics ;

Actual_generics: '[' Type_list ']' ;
 
Type_list: At_least_one_Type ;

At_least_one_Type: Type
                   Optional_Types ;

Optional_Types: -- Empty
                | Optional_Types ',' Type ;

Type: Class_type 
      | Formal_generic_name ;

Class_name: CLASS_NAME_TOKEN { $$ := $1 } 
            | ALL_CAPS_IDENTIFIER_TOKEN { $$ := $1 } 
            | IDENTIFIER_TOKEN { $$ := $1 } ;

Formal_generic_name: ALL_CAPS_IDENTIFIER_TOKEN 
                     | IDENTIFIER_TOKEN ;

%%

end -- class BON_COMMENT_PARSER

-- Local Variables:
-- mode:eiffel
-- End:
