--
-- The Extended BON Tool Suite: BON Parser Skeleton
-- Copyright (C) 2001-2005 Joseph Kiniry and others, see file "forum.txt"
-- All Rights Reserved
--

--
-- $Id: bon_parser_skeleton.e,v 1.1 2005/05/02 22:58:29 kiniry Exp $
--

indexing
	title:       "The Extended BON Tool Suite"
	description: "The BON Parser Skeleton."
	copyright:   "Copyright	(c) 2001-2005 Joseph R. Kiniry and others, %
					 % see file 'forum.txt'"
	license:     "Eiffel Forum License v1 (see forum.txt)"
	author:      "Joseph R. Kiniry <kiniry@acm.org>"
	revision:    "$Revision: 1.1 $"
	version:     "v2-2002"

deferred class BON_PARSER_SKELETON
	-- A parser skeleton for the BON specification language.

inherit
	KL_SHARED_ARGUMENTS
		-- For unit testing via command-line arguments.
		export
			{NONE} all
		end;

	KL_STANDARD_FILES
		-- Standardized manipulation of files needed for opening and reading
		-- files to scan.
		rename
			output as stdoutput,
			input as stdinput,
			error as stderror
		export
			{NONE} all
		end

	KL_SHARED_EXCEPTIONS
		-- So when something goes wrong we can signal such in a portable
		-- manner.
		export
			{NONE} all
		end

	YY_PARSER_SKELETON
		rename
			make as make_parser_skeleton
		end

	UT_CHARACTER_CODES
		-- Used to specify character codes for single-character
		-- terminals/tokens in a portable way.
		export
			{NONE} all
		end

	BON_SCANNER
		-- Our scanner.

feature -- Initialization

	make_parser is
			-- Create a new parser.
		do
			make_scanner
			make_parser_skeleton
		end

feature -- Parsing

	execute is
			-- Parse an BON specifications specified on the command line.
			-- Taken directly from Eiffel parser example in Gobo 2.0.
		local
			a_file: KI_TEXT_INPUT_STREAM
			a_filename: STRING
			j, n: INTEGER
		do
			make_parser
			n := Arguments.argument_count
			if n = 0 then
				stderror.put_string ("usage: bon_parser filename ...%N")
				Exceptions.die (1)
			else
				from j := 1 until j > n loop
					a_filename := Arguments.argument (j)
					a_file := create {KL_TEXT_INPUT_FILE}.make (a_filename)
					if a_file.is_open_read then
						reset_scanner
						set_input_buffer (new_file_buffer (a_file))
						parse
						a_file.close
					else
						stderror.put_string ("bon_parser: cannot read %'")
						stderror.put_string (a_filename)
						stderror.put_string ("%'%N")
					end
					j := j + 1
				end
			end
		end

	parse_string (s: STRING) is
			-- Parse a string provided via the argument `s'.
		do
		end

feature -- Testing

	benchmark is
			-- Benchmark our lexer/parser combination by parsing BON file
			-- `argument(2)' `argument(1)' times.  Taken directly from Eiffel
			-- parser example in Gobo 2.0.
		local
			j, n: INTEGER
			a_filename: STRING
			a_file: KI_TEXT_INPUT_STREAM
		do
			make_parser
			if
				Arguments.argument_count < 2 or else
				not STRING_.is_integer (Arguments.argument (1))
			 then
				stderror.put_string ("usage: bon_parser #parses filename%N")
				Exceptions.die (1)
			else
				n := Arguments.argument (1).to_integer
				a_filename := Arguments.argument (2)
				from j := 1 until j > n loop
					a_file := create {KL_TEXT_INPUT_FILE}.make (a_filename)
					if a_file.is_open_read then
						reset_scanner
						set_input_buffer (new_file_buffer (a_file))
						parse
						a_file.close
					else
						stderror.put_string ("bon_parser: cannot read %'")
						stderror.put_string (a_filename)
						stderror.put_string ("%'%N")
						Exceptions.die (1)
					end
					j := j + 1
				end
			end
		end

end -- class BON_PARSER_SKELETON

-- Local Variables:
-- mode:eiffel
-- End:
