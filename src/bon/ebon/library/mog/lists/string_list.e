indexing
	description: "A list of strings."

class
	STRING_LIST

inherit
	MOG_LIST [STRING]
		redefine
			to_set
		end

creation
	make_list, make_optional_rest, make_optional_first,
	make_from_list, make_from_set, make_from_string_list,
	make_from_linear

feature -- Initialization

	make_from_string_list (a_list: STRING_LIST) is
			-- Initialize `Current' to the contents of 'a_list'.
		do
			make_from_list (a_list)
		ensure
			is_equal (a_list)
		end
		
feature -- Conversion

	to_set: STRING_SET is
			-- Convert `Current' into a string set.
		do
			check false end
		end

end -- class STRING_LIST
