--
-- The Extended BON Tool Suite: BON Scanner Skeleton
-- Copyright (c) 2001-2002 Joseph Kiniry
-- All Rights Reserved
--

--
-- $Id: bon_scanner_skeleton.e,v 1.1 2005/05/02 22:58:28 kiniry Exp $
--

indexing
	title:       "The Extended BON Tool Suite"
	description: "The BON Scanner Skeleton."
	copyright:   "Copyright (c) 2001-2005 Joseph R. Kiniry and others, %
					 % see file 'forum.txt'"
	license:     "Eiffel Forum License v1 (see forum.txt)"
	author:      "Joseph R. Kiniry <kiniry@acm.org>"
	revision:    "$Revision: 1.1 $"
	version:     "v2-2002"

deferred class BON_SCANNER_SKELETON
	-- A scanner skeleton for the BON specification language.

inherit
	KL_SHARED_ARGUMENTS
		-- For unit testing via command-line arguments.
		export
			{NONE} all
		end

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

	YY_COMPRESSED_SCANNER_SKELETON
		-- We use a compressed scanner.
		rename
			make as make_scanner_skeleton,
			reset as reset_scanner
		redefine
			default_action
		end

	BON_TOKENS
		-- The tokens are generated from the grammar description in the
		-- parser.
		export
			{NONE} all
		end

	UT_CHARACTER_CODES
		-- Used to specify character codes for single-character
		-- terminals/tokens in a portable way.
		export
			{NONE} all
		end

feature -- Initialization

	make_scanner is
			-- Build a new scanner.
		do
			create bon_buffer.make (256)

			-- Initial sizes are estimates based upon our example decent-sized 
			-- specifications.
			create class_names.make (256)
			create cluster_names.make (32)
			create feature_names.make (512)
			create system_names.make (4)
			create extended_id_names.make (64)
			create object_group_or_constant_names.make (64)
			create formal_generic_names.make (16)
			create group_names.make (64)

			make_scanner_skeleton
		end

feature {BON_PARSER} -- Mini-symbol table

	resize_if_necessary (set: DS_SPARSE_SET[STRING]) is
			-- Resize the passed set to twice its original maximum size if it is 
			-- full.
		do
			if set.count = set.capacity then
				set.resize (2 * set.capacity)
			end
		end

	add_class_name (name: STRING) is
			-- Adds 'name' to the set of declared class names.
		do
			resize_if_necessary (class_names)
			class_names.put (name)
		end

	is_class_name (name: STRING): BOOLEAN is
			-- Check if 'name' is a declared class name.
		do
			Result := class_names.has (name)
		end

	add_cluster_name (name: STRING) is
			-- Adds 'name' to the set of declared cluster names.
		do
			resize_if_necessary (cluster_names)
			cluster_names.put (name)
		end

	is_cluster_name (name: STRING): BOOLEAN is
			-- Check if 'name' is a declared cluster name.
		do
			Result := cluster_names.has (name)
		end

	add_feature_name (name: STRING) is
			-- Adds 'name' to the set of declared feature names.
		do
			resize_if_necessary (feature_names)
			feature_names.put (name)
		end

	is_feature_name (name: STRING): BOOLEAN is
			-- Check if 'name' is a declared feature name.
		do
			Result := feature_names.has (name)
		end

	add_system_name (name: STRING) is
			-- Adds 'name' to the set of declared system names.
		do
			resize_if_necessary (system_names)
			system_names.put (name)
		end

	is_system_name (name: STRING): BOOLEAN is
			-- Check if 'name' is a declared system name.
		do
			Result := system_names.has (name)
		end

	add_extended_id_name (name: STRING) is
			-- Adds 'name' to the set of declared extended_id names.
		do
			resize_if_necessary (extended_id_names)
			extended_id_names.put (name)
		end

	is_extended_id_name (name: STRING): BOOLEAN is
			-- Check if 'name' is a declared extended_id name.
		do
			Result := extended_id_names.has (name)
		end

	add_object_group_or_constant_name (name: STRING) is
			-- Adds 'name' to the set of declared object_group_or_constant names.
		do
			resize_if_necessary (object_group_or_constant_names)
			object_group_or_constant_names.put (name)
		end

	is_object_group_or_constant_name (name: STRING): BOOLEAN is
			-- Check if 'name' is a declared object_group_or_constant name.
		do
			Result := object_group_or_constant_names.has (name)
		end

	add_formal_generic_name (name: STRING) is
			-- Adds 'name' to the set of declared formal_generic names.
		do
			resize_if_necessary (formal_generic_names)
			formal_generic_names.put (name)
		end

	is_formal_generic_name (name: STRING): BOOLEAN is
			-- Check if 'name' is a declared formal_generic name.
		do
			Result := formal_generic_names.has (name)
		end

	add_group_name (name: STRING) is
			-- Adds 'name' to the set of declared group names.
		do
			resize_if_necessary (group_names)
			group_names.put (name)
		end

	is_group_name (name: STRING): BOOLEAN is
			-- Check if 'name' is a declared group name.
		do
			Result := group_names.has (name)
		end

feature {BON_PARSER} -- Parser

	last_value: ANY
			-- Semantic value to be passed to the parser.

	is_operator: BOOLEAN
			-- Are we parsing an operator declaration?

feature -- Access

	last_string_constant: STRING
			-- The last string constant scanned.

	last_character_constant: CHARACTER
			-- The last character constant scanned.

	last_identifier: STRING
			-- The last identifier scanned.

	last_free_operator: STRING
			-- The last free operator scanned.

	last_integer: INTEGER
			-- The last integer scanned.

	last_real: REAL
			-- The last real scanned.

feature -- State

	bon_buffer: STRING
			-- A buffer for lexical tokens.

	bon_lineno: INTEGER
			-- The current line number for error messages.

	class_names: DS_HASH_SET[STRING]
			-- The set of declared class names.

	cluster_names: DS_HASH_SET[STRING]
			-- The set of declared cluster names.

	feature_names: DS_HASH_SET[STRING]
			-- The set of declared feature names.

	system_names: DS_HASH_SET[STRING]
			-- The set of declared system names.

	extended_id_names: DS_HASH_SET[STRING]
			-- The set of declared extended ids.

	object_group_or_constant_names: DS_HASH_SET[STRING]
			-- The set of declared object group or constant names.

	formal_generic_names: DS_HASH_SET[STRING]
			-- The set of declared formal generic names.

	group_names: DS_HASH_SET[STRING]
			-- The set of declared group names.

feature -- Error

	bon_error_message: STRING
			-- If we emit an error token we fill this with an informative error
			-- message if we have sufficient information in the lexer state.

feature -- Terminals

	String_begin: CHARACTER
			-- The characters used to start and end a simple string.  By default,
			-- both are the `"' (double quote) character.
	String_end: CHARACTER
			--* see: String_begin

feature -- Actions

	default_action is
			-- If no rules is matched, this default action is executed.
			-- We want rules to account for all input, thus this rule
			-- should never fire.  If it does it indicates either an
			-- error in the lexer or an error in the input.
		do
			fatal_error ("Default action fired; current token is " + text)
		end

feature -- Scanning

	scan_file is
			-- Scan file whose name has been given as argument.
			-- Scan standard input if no argument has been given.
		local
			a_file: KI_TEXT_INPUT_STREAM
			a_filename: STRING
		do
			if (Arguments.argument_count >= 1) then
				a_filename := Arguments.argument (1)
				a_file := create {KL_TEXT_INPUT_FILE}.make (a_filename);
			else
				a_file := stdinput
			end
			check 
				a_file /= Void
			end
			make_scanner
			set_input_buffer (new_file_buffer (a_file))
			scan
		end

	scan_string (s: STRING) is
			-- Prepare to scan a string provided via the argument `s'.  This
			-- routine does not actually call `scan'; that is the client's
			-- responsibility.
		require
			s_valid: s /= Void
		do
			set_input_buffer (new_string_buffer (s))
		end

end -- class BON_SCANNER_SKELETON

-- Local Variables:
-- mode:eiffel
-- font-lock-mode:nil
-- End:
