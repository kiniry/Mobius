indexing
   description: "A parenthesized operator expression."

class
   PARENTHESIZED

inherit
   OPERATOR_EXPRESSION

feature -- Access

	hash_code: INTEGER is
		do
			check false end
		end

end -- class PARENTHESIZED
