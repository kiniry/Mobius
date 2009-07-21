indexing
	description: "A list of commands."

class
	COMMAND_LIST

inherit
	STRING_LIST
		redefine
			to_set
		end

creation
	make_list, make_optional_rest, make_optional_first, make_from_list,
	make_from_string_list

feature -- Conversion

	to_set: COMMAND_SET is
			-- Convert `Current' into a command set.
		do
			check false end
		end

end -- class COMMAND_LIST
