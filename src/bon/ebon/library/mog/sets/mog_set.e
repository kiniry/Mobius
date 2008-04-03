indexing
	description: "A set of hashable items with a parser-specific %
					% initialization interface."

deferred class
	MOG_SET [G -> HASHABLE]

inherit
	BON_TEXT

	CANONICALIZABLE

	DS_HASH_SET [G]
		rename
			make as make_as_size,
			is_disjoint as set_is_disjoint,
			merge as set_merge,
			intersect as set_intersect,
			subtract as set_subtract,
			symdif as set_symdif
		end

	PART_SEMANTICS
		redefine
			is_part_of, contains, is_disjoint,
			merge, intersect, subtract, symdif
		end

feature -- Initialization

	make is
			-- Initialize `Current'
		do
			make_equal (default_capacity)
		ensure
			is_empty
		end

	make_set (singleton: G) is
			-- Initialize `Current' with the single element `singleton'.
		do
			make_equal (default_capacity)
			put (singleton)
		ensure
			has (singleton)
			count = 1
		end

	make_optional_rest (singleton: G; optional: like Current) is
			-- Initialize `Current'.
		require
			singleton /= Void
		do
			make_equal (default_capacity)
			put (singleton)
			append (optional)
		ensure
			has (singleton)
			optional /= Void and then is_superset(optional)
			optional /= Void implies count = 1 + optional.count
			optional = Void implies count = 1
		end

	make_optional_first (optional: like Current; singleton: G) is
			-- Initialize `Current'.
		require
			singleton /= Void
		do
			make_equal (default_capacity)
			put (singleton)
			append (optional)
		ensure
			has (singleton)
			optional /= Void and then is_superset(optional)
			optional /= Void implies count = 1 + optional.count
		end
		
	make_from_set (set: like Current) is
			-- Initialize `Current'.
		do
			make_equal (default_capacity)
			append (set)
		ensure
			is_equal (set)
		end

	make_from_list (list: MOG_LIST [G]) is
			-- Initialize `Current'.
		do
			check false end
			-- ensure forall i in Current: i in list
		end

feature -- Conversion

	to_list: MOG_LIST [G] is
			-- Convert `Current' into a list.
		do
			from
				start
			until
				not after
			loop
				Result.put_last (item_for_iteration)
			end
		ensure
			-- is_equal (Result.to_set)
		end

feature -- Output

	bon_out: STRING is
		do
			Result := "{"
			from
				start
			until
				not after
			loop
				-- @design kiniry - should be bon_out
				Result.append (item_for_iteration.out)
			end
			Result.append ("}")
		end
	
feature -- Transformation

	canonicalize: like Current is
-- 		local
-- 			list: MOG_LIST [G]
		do
			check false end
--			list.make_from_list (sorted_items)
--			Result := list.to_set
		end

feature -- Status report
	
	is_part_of (other: like Current): BOOLEAN is
		do
			check false end
		end

	contains (other: like Current): BOOLEAN is
		do
			check false end
		end

	is_disjoint (other: like Current): BOOLEAN is
		do
			check false end
		end

feature -- Basic operations

	merge (other: like Current): like Current is
		do
			check false end
		end

	intersect (other: like Current): like Current is
		do
			check false end
		end

	subtract (other: like Current): like Current is
		do
			check false end
		end

	symdif (other: like Current): like Current is
		do
			check false end
		end

feature -- Implementation

	my_sorter: DS_HASH_TOPOLOGICAL_SORTER [G]

end -- class MOG_SET
