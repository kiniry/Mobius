indexing
	description: "A list of comments."

class
	COMMENT

inherit
	SPECIFICATION_ELEMENT
	
	STRING_LIST
	
creation
	make_list, make_optional_rest, make_optional_first, make_from_list, 
	make_from_linear

feature -- Access

	hash_code: INTEGER is
		do
			check false end
		end

feature -- Status report

	is_valid: BOOLEAN is
		do
			check false end
		end

end -- class COMMENT
