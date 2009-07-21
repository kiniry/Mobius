-- ====================
-- Declarations section
-- ====================

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Eiffel code to define scanner class header.
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

%{
--
-- The Extended BON Toolsuite: BON Scanner
-- Copyright (C) 2001 Joseph Kiniry
-- All Rights Reserved
--

--
-- $Id: bon_scanner.l,v 1.2 2005/12/21 14:11:10 kiniry Exp $
--

indexing
	title:       "The Extended BON Tool Suite"
	description: "The BON Scanner."
	copyright:   "Copyright (c) 2001-2002 Joseph R. Kiniry and others, %
					% see file 'forum.txt'"
	license:     "Eiffel Forum License v1 (see forum.txt)"
	author:      "Joseph R. Kiniry <kiniry@acm.org>"
	revision:    "$Revision: 1.2 $"
	version:     "v2-2002"

class BON_SCANNER
	-- A scanner for the BON specification language.

inherit
	BON_SCANNER_SKELETON
		-- All core code for scanner is in the skeleton.

creation
	make_scanner, scan_file
%}

-- ~~~~~~~~~~~~~
-- Gelex options
-- ~~~~~~~~~~~~~

%option outfile="bon_scanner.e"

-- ~~~~~~~~~~~~~~~~
-- Name definitions
-- ~~~~~~~~~~~~~~~~

-- First we define standard character classes so that we can precisely 
-- define syntax rules for various types of identifiers.

SPACETAB                [ \t]
WHITESPACE              [ \t\r\n]
NOT_WHITESPACE          [^ \t\r\n]
UNDERSCORE              _
DIGIT                   [0-9]
CAPITALIZED_ALPHA       [A-Z]
LOWERCASE_ALPHA         [a-z]
ALPHA                   {CAPITALIZED_ALPHA}|{LOWERCASE_ALPHA}
ALPHANUMERIC            {ALPHA}|{DIGIT}
ALPHANUMERIC_UNDERSCORE {ALPHANUMERIC}|{UNDERSCORE}

-- The Identifier construct is defined as a sequence of alphanumeric -
-- characters including underscore. An identifier must begin with an
-- alphanumeric character and must not end with an underscore (whose
-- purpose really is to mimic word separation). Letter case is not
-- significant, but using consistent style rules is important.

-- COMMON_POSTFIX         {ALPHANUMERIC_UNDERSCORE}*{ALPHANUMERIC}
-- IDENTIFIER             {ALPHA}{COMMON_POSTFIX}
-- CAPITALIZED_IDENTIFIER {CAPITALIZED_ALPHA}{COMMON_POSTFIX}
-- LOWERCASE_IDENTIFIER   {LOWERCASE_ALPHA}{COMMON_POSTFIX}
-- FIRST_CAPITALIZED_IDENTIFIER {CAPITALIZED_ALPHA}
--                              ({LOWERCASE_ALPHA}|{DIGIT}|{UNDERSCORE})*
--                              ({LOWERCASE_ALPHA}|{DIGIT})

-- The recommended BON standard is to use all upper case names for class
-- and cluster names, all lower case for feature names, and lower case
-- beginning with a capital for object groups and constants values. We also
-- strongly recommend using underscore for word separation rather than, for
-- example, in-word capitalization, since this greatly enhances
-- readability.

-- CLASS_NAME_TOKEN         {CAPITALIZED_IDENTIFIER}
-- CLUSTER_NAME_TOKEN       {CAPITALIZED_IDENTIFIER}
-- FEATURE_NAME_TOKEN       {LOWERCASE_IDENTIFIER}
-- OBJECT_GROUP_OR_CONSTANT_NAME_TOKEN {FIRST_CAPITALIZED_IDENTIFIER}

-- The FREE_OPERATOR construct represents feature names used as infix and
-- prefix operations. Such operations may be textual keywords, such as the
-- boolean "and" and "or", but are more often composed of special
-- characters, like "+", "**", "=>", etc.  

-- Given that the scanner cannot tell that these operators are operators,
-- they are just scanned as identifiers and the parser is responsible for
-- determining that they are operators.

-- We need a start condition for string lexing; we'll call it
-- <STRING_CONDITION>.  It is an "exclusive" start condition because you
-- are either inside of a string or you aren't.

-- Also, there are situations were we know we are simple parsing what BON
-- called a "simple string".  E.g., a comment line.  We need a condition
-- for such as well.

%x STRING_CONDITION
%x SIMPLE_STRING_CONDITION
%x CONCATENATE_CONDITION
%x END_OF_STRING_CONDITION
%x CHARACTER_CONDITION
%x UNARY_OPERATOR_DECLARATION_CONDITION
%x UNARY_OPERATOR_CONDITION
%x BINARY_OPERATOR_DECLARATION_CONDITION
%x BINARY_OPERATOR_CONDITION

%%

-- =============
-- Grammar Rules
-- =============

-- ~~~~~~~~~~~~
-- BON Keywords
-- ~~~~~~~~~~~~

action          last_token := ACTION_TOKEN
and             last_token := AND_TOKEN
calls           last_token := CALLS_TOKEN
class           last_token := CLASS_TOKEN
class_chart     last_token := CLASS_CHART_TOKEN
client          last_token := CLIENT_TOKEN
cluster         last_token := CLUSTER_TOKEN
cluster_chart   last_token := CLUSTER_CHART_TOKEN
command         last_token := COMMAND_TOKEN
component       last_token := COMPONENT_TOKEN
concatenator    last_token := CONCATENATOR_TOKEN
constraint      last_token := CONSTRAINT_TOKEN
creates         last_token := CREATES_TOKEN
creation_chart  last_token := CREATION_CHART_TOKEN

creator         last_token := CREATOR_TOKEN
Current         last_token := CURRENT_TOKEN
deferred        last_token := DEFERRED_TOKEN
delta           last_token := DELTA_TOKEN
description     last_token := DESCRIPTION_TOKEN
dictionary      last_token := DICTIONARY_TOKEN
dynamic_diagram last_token := DYNAMIC_DIAGRAM_TOKEN
effective       last_token := EFFECTIVE_TOKEN
end             last_token := END_TOKEN
ensure          last_token := ENSURE_TOKEN
event           last_token := EVENT_TOKEN
event_chart     last_token := EVENT_CHART_TOKEN
exists          last_token := EXISTS_TOKEN
explanation     last_token := EXPLANATION_TOKEN

false           last_token := FALSE_TOKEN
feature         last_token := FEATURE_TOKEN
for_all         last_token := FOR_ALL_TOKEN
incoming        last_token := INCOMING_TOKEN
indexing        last_token := INDEXING_TOKEN
inherit         last_token := INHERIT_TOKEN
interfaced      last_token := INTERFACED_TOKEN
invariant       last_token := INVARIANT_TOKEN
involves        last_token := INVOLVES_TOKEN
it_holds        last_token := IT_HOLDS_TOKEN
keyword_prefix  last_token := KEYWORD_PREFIX_TOKEN
member_of       last_token := MEMBER_OF_TOKEN
nameless        last_token := NAMELESS_TOKEN

not             last_token := NOT_TOKEN
object          last_token := OBJECT_TOKEN
object_group    last_token := OBJECT_GROUP_TOKEN
object_stack    last_token := OBJECT_STACK_TOKEN
old             last_token := OLD_TOKEN
or              last_token := OR_TOKEN
outgoing        last_token := OUTGOING_TOKEN
part            last_token := PART_TOKEN
persistent      last_token := PERSISTENT_TOKEN
-- prefix is below
query           last_token := QUERY_TOKEN
redefined       last_token := REDEFINED_TOKEN
require         last_token := REQUIRE_TOKEN
Result          last_token := RESULT_TOKEN

reused          last_token := REUSED_TOKEN
root            last_token := ROOT_TOKEN
scenario        last_token := SCENARIO_TOKEN
scenario_chart  last_token := SCENARIO_CHART_TOKEN
static_diagram  last_token := STATIC_DIAGRAM_TOKEN
string_marks    last_token := STRING_MARKS_TOKEN
such_that       last_token := SUCH_THAT_TOKEN
system_chart    last_token := SYSTEM_CHART_TOKEN
true            last_token := TRUE_TOKEN
Void            last_token := VOID_TOKEN
xor             last_token := XOR_TOKEN

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Dealing with operator declarations
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

-------------------------------
-- Prefix operator declarations
-------------------------------

prefix {
  -- declares a prefix operator
  last_token := PREFIX_TOKEN
  set_start_condition (UNARY_OPERATOR_DECLARATION_CONDITION)
}

-- We start the declaration of an unary operator with a double quote.

<UNARY_OPERATOR_DECLARATION_CONDITION>"\"" {
  last_token := Double_quote_code
  set_start_condition (UNARY_OPERATOR_CONDITION)
}

-- There are exactly five pre-defined unary operators: delta, old, not, +,
-- and -.

-- @todo: Consider whether we should alert the user that he is overriding 
-- the semantics of these default unary operators.

<UNARY_OPERATOR_CONDITION>delta {
  last_token := DELTA_TOKEN
  last_free_operator := "delta"
}

<UNARY_OPERATOR_CONDITION>old {
  last_token := OLD_TOKEN
  last_free_operator := "old"
}

<UNARY_OPERATOR_CONDITION>not {
  last_token := NOT_TOKEN
  last_free_operator := "not"
}

<UNARY_OPERATOR_CONDITION>"+" {
  last_token := Plus_code
  last_free_operator := "+"
}

<UNARY_OPERATOR_CONDITION>"-" {
  last_token := Minus_code
  last_free_operator := "-"
}

------------------------------
-- Infix operator declarations
------------------------------

-- todo: (kiniry) Consider whether we should collapse these rules so that
-- as soon as we see the infix or prefix keywords we just look for the
-- whole shebang and do all declaration handling in the scanner

infix {
  last_token := INFIX_TOKEN
  set_start_condition (BINARY_OPERATOR_DECLARATION_CONDITION)
}

-- We start the declaration of a binary operator with a double quote.

<BINARY_OPERATOR_DECLARATION_CONDITION>"\"" {
  last_token := Double_quote_code
  set_start_condition (BINARY_OPERATOR_CONDITION)
}

-- There are twenty pre-defined binary operators: +, -, *, /, <, >, <=, >=,
-- =, /=, //, \\, ^, or, xor, and, ->, <->, member_of, and :.

<BINARY_OPERATOR_CONDITION>"+" {
  last_token := Plus_code
  last_free_operator := "+"
}
<BINARY_OPERATOR_CONDITION>"-" {
  last_token := Minus_code
  last_free_operator := "-"
}
<BINARY_OPERATOR_CONDITION>"*" {
  last_token := Star_code
  last_free_operator := "*"
}
<BINARY_OPERATOR_CONDITION>"/" {
  last_token := Slash_code
  last_free_operator := "/"
}
<BINARY_OPERATOR_CONDITION>"<" {
  last_token := Less_than_code
  last_free_operator := "<"
}
<BINARY_OPERATOR_CONDITION>">" {
  last_token := Greater_than_code
  last_free_operator := ">"
}
<BINARY_OPERATOR_CONDITION>"<=" {
  last_token := LESS_THAN_OR_EQUAL_TOKEN
  last_free_operator := "<="
}
<BINARY_OPERATOR_CONDITION>">=" {
  last_token := GREATER_THAN_OR_EQUAL_TOKEN
  last_free_operator := ">="
}
<BINARY_OPERATOR_CONDITION>"=" {
  last_token := Equal_code
  last_free_operator := "="
}
<BINARY_OPERATOR_CONDITION>"/=" {
  last_token := NOT_EQUAL_TOKEN
  last_free_operator := "/="
}
<BINARY_OPERATOR_CONDITION>"//" {
  last_token := DOUBLE_SLASH_TOKEN
  last_free_operator := "//"
}
<BINARY_OPERATOR_CONDITION>"\\" {
  last_token := DOUBLE_BACKSLASH_TOKEN
  last_free_operator := "\\"
}
<BINARY_OPERATOR_CONDITION>"^" {
  last_token := Caret_code
  last_free_operator := "^"
}
<BINARY_OPERATOR_CONDITION>"or" {
  last_token := OR_TOKEN
  last_free_operator := "or"
}
<BINARY_OPERATOR_CONDITION>"xor" {
  last_token := XOR_TOKEN 
  last_free_operator := "xor"
}
<BINARY_OPERATOR_CONDITION>"and" {
  last_token := AND_TOKEN 
  last_free_operator := "and"
}
<BINARY_OPERATOR_CONDITION>"->" {
  last_token := IMPLIES_TOKEN
  last_free_operator := "->"
}
<BINARY_OPERATOR_CONDITION>"<->" {
  last_token := EQUIVALENT_TO_TOKEN
  last_free_operator := "<->"
}
<BINARY_OPERATOR_CONDITION>"member_of" {
  last_token := MEMBER_OF_TOKEN 
  last_free_operator := "member_of"
}
<BINARY_OPERATOR_CONDITION>":" {
  last_token := Colon_code
  last_free_operator := ":"
}

-- We end both kinds of declaration with a double quote and we go back to
-- normal lexing condition.

<UNARY_OPERATOR_CONDITION,BINARY_OPERATOR_CONDITION>"\"" {
  last_token := Double_quote_code
  set_start_condition (INITIAL)
}

-- Ignore leading whitespace.

<UNARY_OPERATOR_DECLARATION_CONDITION,BINARY_OPERATOR_DECLARATION_CONDITION>[^\"]

-- Anything else is a new (unary or binary) free operator.

<UNARY_OPERATOR_CONDITION,BINARY_OPERATOR_CONDITION>[^"]+ {
  last_token := FREE_OPERATOR_TOKEN
  last_value := text
  last_free_operator := text
}

-- ~~~~~~~~~~~~~~~~~~~~~
-- Extended BON Keywords
-- ~~~~~~~~~~~~~~~~~~~~~

-- None currently specified.  Must finish BON grammar first.

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Single and Multi-Character Symbols
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

"--" {
  -- Introduces comments
  last_token := DOUBLE_DASH_TOKEN
  set_start_condition (SIMPLE_STRING_CONDITION)
}

-- Feature arguments, constrained genericity, logical implication 
"->" {
  last_token := IMPLIES_TOKEN
}

-- General element separator
","   last_token := Comma_code

-- Separator for parent lists, assertion clauses, and indexing clauses
";"   last_token := Semicolon_code

"("   last_token := Left_parenthesis_code  -- Grouping of expressions,
")"   last_token := Right_parenthesis_code -- multiplicity
"["   last_token := Left_bracket_code      -- Encloses generic
"]"   last_token := Right_bracket_code     -- parameters
"{"   last_token := Left_brace_code        -- Encloses restricted export lists,
"}"   last_token := Right_brace_code       -- renaming, enumerated sets
"+"   last_token := Plus_code              -- Arithmetic operators 
"-"   last_token := Minus_code
"*"   last_token := Star_code
"/"   last_token := Slash_code
"//"  last_token := DOUBLE_SLASH_TOKEN     -- Integer division operator
"\\\\"  last_token := DOUBLE_BACKSLASH_TOKEN -- Modulo operator
"^"   last_token := Caret_code             -- Power operator, renaming 
"<->" last_token := EQUIVALENT_TO_TOKEN    -- Logical equivalence 
"<="  last_token := LESS_THAN_OR_EQUAL_TOKEN
"<"   last_token := Less_than_code         -- Relational operators 
">="  last_token := GREATER_THAN_OR_EQUAL_TOKEN 
">"   last_token := Greater_than_code
"="   last_token := Equal_code             -- Equality and non-equality  
"/="  last_token := NOT_EQUAL_TOKEN 
"."   last_token := Dot_code               -- Feature calls, renaming,
														 -- relational references,
														 -- object_id  
".."  last_token := DOUBLE_DOT_TOKEN       -- Interval marker

-- Type mark, type operator, index separator
":"   last_token := Colon_code

":{"  last_token := AGGREGATE_MARK_TOKEN   -- Indicates aggregate supplier

-- Undocumented tokens in original BON grammar.

"..." last_token := ELLIPSES_TOKEN

-- ~~~~~~~~~
-- Character
-- ~~~~~~~~~

' {
  -- Encloses character constants
  last_token := Single_quote_code
  set_start_condition (CHARACTER_CONDITION)
}

<CHARACTER_CONDITION>.' {
  last_token := CHARACTER_TOKEN
  last_character_constant := text @ 1
  unread_character ('%'')
}

<CHARACTER_CONDITION>' {
  last_token := Single_quote_code
  set_start_condition (INITIAL)
}

-- ~~~~~~~
-- Strings
-- ~~~~~~~

-- We'll deal with simple strings first.  Remember that . matches anything 
-- but a newline, so .* will match the remainder of the line.

<SIMPLE_STRING_CONDITION>.* {
  set_start_condition (INITIAL)
  last_token := SIMPLE_STRING_TOKEN
  last_value := text
  last_string_constant := text
}

-- In case we have a comment that ends immediately and contains no text, 
-- we must match it as well.

<SIMPLE_STRING_CONDITION>\n {
  set_start_condition (INITIAL)
  last_token := SIMPLE_STRING_TOKEN
  last_value := ""
  last_string_constant := ""
}

-- We look for a start of a new string with the STRING_DELIMITER_TOKEN.
-- When then move into the STRING start state which means that we are
-- in the middle of a string.

"\"" {
  set_start_condition (STRING_CONDITION)
  last_token := STRING_DELIMITER_TOKEN
  bon_buffer.wipe_out
}

-- While in the string, we scan everything that isn't a delimiter or a
-- concatenation character.

<STRING_CONDITION>[^"\\]* append_text_to_string (bon_buffer)

-- If we see a concatenator, we move into the CONCATENATE state to look
-- for its twin.  We eat up the concatenate terminals as well as all
-- EOL and whitespace between them.

<STRING_CONDITION>\\ set_start_condition (CONCATENATE_CONDITION)

-- While we are searching for the twin concatenator, just skip anything else.

<CONCATENATE_CONDITION>[^\\]*

-- When we find the twin, lex and forget it and move back into the STRING
-- start state to continue lexing our string.

<CONCATENATE_CONDITION>\\ set_start_condition (STRING_CONDITION)

-- Finally, when we are in the string state and we find that second
-- delimiter, we know we have a full string.  We emit the string contents
-- as a single SIMPLE_STRING token then we emit its closing
-- STRING_DELIMITOR.

<STRING_CONDITION>"\"" {
  set_start_condition (END_OF_STRING_CONDITION)
  last_token := SIMPLE_STRING_TOKEN
  last_value := bon_buffer.twin
  last_string_constant := bon_buffer.twin
  debug ("GELEX")
	stdoutput.put_string ("Returning string '" + 
								  last_string_constant + "'%N")
  end
  unread_character ('%"')
}

<END_OF_STRING_CONDITION>"\"" {
  last_token := STRING_DELIMITER_TOKEN
  set_start_condition (INITIAL)
}

-- From the BON text:

-- The construct Simple_string is defined as any string of characters not
-- containing a New_line character.

-- The non-terminal construct Manifest_string is a Simple_string enclosed
-- in the pair of terminals String_begin and String_end.  Thus,
-- Manifest_string is defined in the grammar and all we have to scan are
-- the String_begin and String_end.  

-- Similarly, the non-terminal Manifest_textblock is a sequence of
-- Simple_string separated by New_line and enclosed by the same pair of
-- terminal constructs.

-- These delimiters are defined by default as a string containing one
-- double quote character. The character sequence 
-- "show some class, don't treat me like an object" 
-- is then interpreted as a Manifest_string. However, to facilitate the 
-- accommodation of double quotes inside strings without having to insert 
-- escape characters, the delimiting strings may be changed (often to some 
-- control characters in connection with automatic processing). 

-- Ed. note: String_begin and String_end are currently defined as
-- non-terminals that directly map to STRING_DELIMITER.  We currently do
-- not support redefining these non-terminals.

-- BON also defines a lexical Concatenator construct. If a Concatenator is 
-- found inside a Simple_string, it is removed along with all characters
-- (including New_line) up to and including the next Concatenator
-- construct. This makes it possible to embed formatting whitespace into
-- strings for readability, without making the formatting characters part
-- of the strings. 

-- The Concatenator construct is defined as a single backslash by default,
-- but may be changed by the user. It must not conflict with the string
-- delimiters. An example of its use is shown below. 

--   "This is a long simple string, which has been broken into\
--    \ two lines for readability" 

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Identifiers and potential operators
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

-- Look up text to see if it is a declared Class_name or Cluster_name.  If
-- so, return the appropriate token, otherwise return an
-- ALL_CAPS_IDENTIFIER_TOKEN

[A-Z]([A-Z0-9_]*[A-Z0-9])? {
  if (is_class_name (text)) then
	last_token := CLASS_NAME_TOKEN
  else if (is_cluster_name (text)) then
			last_token := CLUSTER_NAME_TOKEN
		 else
			last_token := ALL_CAPS_IDENTIFIER_TOKEN
		 end
  end
  last_value := text
  last_identifier := text
}

[0-9][0-9]*[A-Z]([A-Z0-9_]*[A-Z0-9])? {
  if (is_class_name (text)) then
	last_token := CLASS_NAME_TOKEN
  else if (is_cluster_name (text)) then
			last_token := CLUSTER_NAME_TOKEN
		 else
			last_token := ALL_CAPS_IDENTIFIER_TOKEN
		 end
  end
  last_value := text
  last_identifier := text
}

-- Feature names are all lowercase.

[a-z]([a-z0-9_]*[a-z0-9])? {
  if (is_feature_name (text)) then
	last_token := FEATURE_NAME_TOKEN
  else
	last_token := IDENTIFIER_TOKEN
  end
  last_value := text
  last_identifier := text
}

[0-9][0-9]*[a-z]([a-z0-9_]*[a-z0-9])? {
  if (is_feature_name (text)) then
	last_token := FEATURE_NAME_TOKEN
  else
	last_token := IDENTIFIER_TOKEN
  end
  last_value := text
  last_identifier := text
}

-- First letter capitalized and rest lowercase is an object group or
-- constant.

[A-Z]([a-z0-9_]*[a-z0-9])? {
  if (is_object_group_or_constant_name (text)) then
	last_token := OBJECT_GROUP_OR_CONSTANT_NAME_TOKEN
  else
	last_token := IDENTIFIER_TOKEN
  end
  last_value := text
  last_identifier := text
}

[0-9][0-9]*[A-Z]([a-z0-9_]*[a-z0-9])? {
  if (is_object_group_or_constant_name (text)) then
	last_token := OBJECT_GROUP_OR_CONSTANT_NAME_TOKEN
  else
	last_token := IDENTIFIER_TOKEN
  end
  last_value := text
  last_identifier := text
}

-- Remaining mixed case are just identifiers.

[A-Za-z]([A-Za-z0-9_]*[A-Za-z0-9])? {
  last_token := IDENTIFIER_TOKEN
  last_value := text
  last_identifier := text
}

[0-9][0-9]*[A-Za-z]([A-Za-z0-9_]*[A-Za-z0-9])? {
  last_token := IDENTIFIER_TOKEN
  last_value := text
  last_identifier := text
}

-- ~~~~~~~~~~~~~~~~~~
-- Reals and Integers
-- ~~~~~~~~~~~~~~~~~~

[-+]?[0-9][0-9]*\.[0-9][0-9]* {
  last_token := REAL_TOKEN
  last_value := text.to_real
  last_real := text.to_real
}

[-+]?[0-9][0-9]* {
  last_token := INTEGER_TOKEN
  last_value := text.to_integer
  last_integer := text.to_integer
}

-- ~~~~~~~~~~
-- Whitespace
-- ~~~~~~~~~~

{WHITESPACE}+    -- Just ignore whitespace.

-- Drop in default rule for testing lexer.

.               default_action

%%
end -- class BON_SCANNER

-- Local Variables:
-- mode:eiffel
-- font-lock-mode:nil
-- End:
