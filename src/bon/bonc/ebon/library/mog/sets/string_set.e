indexing
	description: "A set of strings."

class
	STRING_SET

inherit
	MOG_SET [STRING]
		redefine
			to_list
		end

creation
	make, make_set, make_optional_rest, make_optional_first,
	make_from_set, make_from_list,
	make_from_string_set

feature -- Initialization

	make_from_string_set (set: STRING_SET) is
		-- Initialize `Current'.
	do
		make_equal (default_capacity)
		from
			start
		until
			not after
		loop
			put (item_for_iteration)
			forth
		end
		ensure
			is_equal (set)
		end

feature -- Conversion

	to_list: STRING_LIST is
			-- Convert `Current' into a string list.
		do
			check false end
		end

end -- class STRING_SET
