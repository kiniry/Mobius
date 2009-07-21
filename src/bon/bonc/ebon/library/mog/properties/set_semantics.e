indexing
	description: "An entity that has a set theory-based semantics."

deferred class
	SET_SEMANTICS [G]

inherit
	ANY
		undefine
			is_equal
		end

feature -- Access

	has (element: G): BOOLEAN is
			--- Is `element' in the current set?
		require
			element_not_void: element /= Void
		deferred
		end

	choose: G is
			-- Choose any element of the current set.
		deferred
		ensure
			empty_set_has_no_choices: cardinality = 0 implies Result = Void
			non_empty_set_always_has_a_choice: cardinality /= 0 implies Result /= Void
		end
	
feature -- Comparison

	is_equal (other: like Current): BOOLEAN is
		require
			other_non_void: other /= Void
		do
			Result = is_subset(other) and is_superset(other)
		ensure
			definition: Result = is_subset(other) and is_superset(other)
			equal_sets_have_same_cardinality: Result implies cardinality = other.cardinality
		end

feature -- Status report

	is_empty: BOOLEAN is
			-- Does `Current' contain any elements?
		do
			Result := count = 0
		ensure
			Result = count = 0
			-- (forall G e; not has(e))
		end
	
	is_subset (other: like Current): BOOLEAN is
			-- Are all items of `Current' included in `other'?
		require
			other_not_void: other /= Void
		deferred
		end

	is_proper_subset (other: like Current): BOOLEAN is
			-- Are all items of `Current' included in `other' and
			-- `Current' and `other' are not equal?
		require
			other_not_void: other /= Void
		do
			Result := is_subset (other) and not is_equal (other)
		ensure
			definition: (Result implies is_subset (other) and not is_equal (other)) and
				(is_subset (other) and not is_equal (other) implies Result)
		end

	is_superset (other: like Current): BOOLEAN is
			-- Does `Current' include all items of `other'?
		require
			other_not_void: other /= Void
		do
			Result := other.is_subset (Current)
		ensure
			definition: Result = other.is_subset (Current)
		end

	is_proper_superset (other: like Current): BOOLEAN is
			-- Does `Current' include all items of `other' and `Current'
			-- and `other' are not equal?
		require
			other_not_void: other /= Void
		do
			Result := other.is_proper_subset (Current)
		ensure
			definition: Result = other.is_proper_subset (Current)
		end

	is_disjoint (other: like Current): BOOLEAN is
			-- Are none of the items of `Current' included in `other'?
		require
			other_not_void: other /= Void
		deferred
		end

feature -- Measurement

	count, cardinality: INTEGER is
			-- Cardinality of current set.
		deferred
		ensure
			cardinality_non_negative: Result >= 0
			empty_set: is_empty implies Result = 0
			-- not is_empty implies (exists G e such_that has(e); Result = 1 + remove(e).size)
		end

feature -- Basic operations

	union (other: like Current): like Current is
			-- Add all items of `other' to current set.
		require
			other_not_void: other /= Void
		deferred
		ensure
			union_not_void: Result /= Void
			is_superset: Result.is_superset (other) and Result.is_superset (Current)
		end

	intersect (other: like Current): like Current is
			-- Remove all items not included in `other'.
		require
			other_not_void: other /= Void
		deferred
		ensure
			no_bigger: count >= Result.count
			is_subset: Result.is_subset (Current) and Result.is_subset (other)
		end

	subtract (other: like Current): like Current is
			-- Remove all items also included in `other'.
		require
			other_not_void: other /= Void
		deferred
		ensure
			no_bigger: count >= Result.count
			definition: Result.intersect (intersect (other)).is_empty
		end

	symdif (other: like Current): like Current is
			-- Add items of `other' which are not included in current set
			-- and remove those which are.
		require
			other_not_void: other /= Void
		deferred
		ensure
			definition: 
		end

	insert (element: G): like Current is
			-- Returns a new set that contains all the elements of
			-- `Current' and also `element'.
		require
			element_not_void: element /= Void
			enough_room: count < INTEGER.Max_value or has(element)
		deferred
		ensure
			result_not_void: Result /= Void
			-- definition: (forall G e; Result.has (e) iff has (e) or e = element)
			definition_part_1: is_subset (Result)
			definition_part_2: Result.has (element)
			definition_part_3: Result.count = count
			definition_part_4: has (element) implies Result.count = count
			definition_part_5: not has (element) implies Result.count = count + 1
		end

	remove (element: G): like Current is
			-- Returns a new set that contains all the elements of `Current'
			-- except for `element'.
		require
			element_not_void: element /= Void
		deferred
		ensure
			result_not_void: Result /= Void
			-- definition: (forall G e; Result.has (e) iff has (e) and not (e = element))
			definition_part_1: Result.is_subset (Current)
			definition_part_2: Result.has (element)
			definition_part_3: has (element) implies Result.count = count - 1
			definition_part_4: not has (element) implies Result.count = count
		end

	powerset: like Current is
			-- Returns a new set that is the set of all subsets of `Current'.
		require
			avoid_exponential_explosion: count < 32
		deferred
		ensure
			-- definition: (forall SET_SEMANTICS s; s.is_subset (Current) iff Result.has (s))
		end

end -- class SET_SEMANTICS
