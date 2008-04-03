indexing
	description: "An entity that can be rewritten into canonical form."

deferred class
	CANONICALIZABLE

inherit
	ANY
		undefine
			copy, is_equal
		end

feature -- Transformation

	canonicalize: like Current is
			-- Return a clone of `Current' into canonical form.
		deferred
		ensure
			is_equal (old Current)
		end

end -- class CANONICALIZABLE
