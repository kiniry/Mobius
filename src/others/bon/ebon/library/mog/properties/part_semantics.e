indexing
	description: "An entity that has a kind theory part semantics."

deferred class
	PART_SEMANTICS

inherit
	ANY
		undefine
			is_equal, copy
		end

	-- All definitions here in contracts are partial, as we don't have
	-- first order quantifiers.

feature -- Status report
	
	is_part_of (other: like Current): BOOLEAN is
			-- Is `Current' a part of `other'?
		require
			other_not_void: other /= Void
		deferred
		ensure
			definition: Result = other.contains (Current)
		end

	contains (other: like Current): BOOLEAN is
			-- Does `Current' contain `other'?
		require
			other_not_void: other /= Void
		deferred
		ensure
			definition: Result = other.is_part_of (Current)
		end

	is_disjoint (other: like Current): BOOLEAN is
			-- Are none of the items of `Current' included in `other'?
		require
			other_not_void: other /= Void
		deferred
--		do
--			Result := not is_part_of (other) and not contains (other)
		ensure
			definition: Result = not is_part_of (other) and not contains (other)
		end

feature -- Basic operations

	merge (other: like Current): like Current is
			-- Merge `Current' and `other'.
		require
			other_not_void: other /= Void
		deferred
		ensure
			merge_not_void: Result /= Void
			definition: Result.contains (other) and Result.contains (Current)
		end

	intersect (other: like Current): like Current is
			-- Remove all parts not included in `other'.
		require
			other_not_void: other /= Void
		deferred
		ensure
			containment: Result /= Void implies
				Result.is_part_of (other) and Result.is_part_of (Current)
		end

	subtract (other: like Current): like Current is
			-- Remove all items also included in `other'.
		require
			other_not_void: other /= Void
		deferred
		ensure
			subtraction_not_void: Result /= Void
			is_disjoint: not Result.is_part_of (other)
		end

	symdif (other: like Current): like Current is
			-- Add items of `other' which are not included in current set
			-- and remove those which are.
			-- I.e., Result = (A union B) - (A intersect B)
		require
			other_not_void: other /= Void
		deferred
		ensure
			symdifference_not_void: Result /= Void
			definition: Result.is_part_of (Current) or Result.is_part_of (other) 
		end

end -- class PART_SEMANTICS
