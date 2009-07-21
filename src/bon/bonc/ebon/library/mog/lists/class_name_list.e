indexing
	description: "A list of class names."

class
	CLASS_NAME_LIST

inherit
	STRING_LIST
		redefine
			to_set
		end

creation
	make_list, make_optional_rest, make_optional_first, make_from_linear

feature -- Conversion

	to_set: CLASS_NAME_SET is
			-- Convert `Current' into a class name set.
		do
			check false end
		end

end -- class CLASS_NAME_LIST
