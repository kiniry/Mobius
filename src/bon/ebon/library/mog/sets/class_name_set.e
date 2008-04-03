indexing
	description: "A set of class names."

class
	CLASS_NAME_SET

inherit
	STRING_SET
		redefine
			to_list
		end

creation
	make_set, make_optional_rest, make_optional_first,
	make_from_set, make_from_list,
	make_from_string_set

feature -- Conversion

	to_list: CLASS_NAME_LIST is
			-- Convert `Current' into a class name list.
		do
			check false end
		end

end -- class CLASS_NAME_SET
