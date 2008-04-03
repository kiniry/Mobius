indexing
   description: "An unary expression."

class
   UNARY_EXPRESSION

inherit
   OPERATOR_EXPRESSION

feature -- Access

	hash_code: INTEGER is
		do
			check false end
		end

end -- class UNARY_EXPRESSION
