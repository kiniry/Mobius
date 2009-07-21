indexing
   description: "A list of identifiers that are members of a set."

class
   MEMBER_RANGE

inherit
   VARIABLE_RANGE

feature -- Access

	hash_code: INTEGER is
		do
			check false end
		end

end -- class MEMBER_RANGE
