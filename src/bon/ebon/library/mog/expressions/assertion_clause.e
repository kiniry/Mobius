indexing
   description: "A boolean expression or an informal comment."

class
  ASSERTION_CLAUSE

inherit
	HASHABLE

feature -- Access

	hash_code: INTEGER is
		do
			check false end
		end

end -- class ASSERTION_CLAUSE
