indexing
	description: "A formal class invariant."

class
	CLASS_INVARIANT

inherit
	ASSERTION

feature -- Access

	hash_code: INTEGER is
		do
			check false end
		end

feature -- Transformation

	canonicalize: like Current is
		do
			check false end
		end

feature -- Output

	bon_out: STRING is
		do
			check false end
		end
		
end -- CLASS_INVARIANT
