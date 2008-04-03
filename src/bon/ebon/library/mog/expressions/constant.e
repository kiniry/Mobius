indexing
   description: "A constant expression."

class
   CONSTANT

inherit
   EXPRESSION

feature -- Access

	hash_code: INTEGER is
		do
			check false end
		end

end -- class CONSTANT
