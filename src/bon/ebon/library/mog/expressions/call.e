indexing
   description: "A call chain representing a feature invocation."

class
   CALL

inherit
   EXPRESSION

   SET_EXPRESSION

feature -- Access

	hash_code: INTEGER is
		do
			check false end
		end

end -- class CALL
