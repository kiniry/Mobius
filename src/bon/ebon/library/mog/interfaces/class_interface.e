indexing
	description: "A description of a class, primarily consisting of its features."

class
	CLASS_INTERFACE

inherit
	BON_TEXT

	CANONICALIZABLE

	HASHABLE

	PART_SEMANTICS

creation
	make

feature -- Initialization

	make (an_index: INDEX_LIST;
				some_parents: CLASS_TYPE_LIST;
				some_features: FEATURE_CLAUSE_LIST;
				an_invariant: CLASS_INVARIANT) is
			-- Initialize `Current'.
		require
			some_features /= Void and then some_features.count >= 0
		do
			my_index := an_index.twin
			my_parents := some_parents.twin
			my_features := some_features.twin
			my_class_invariant := an_invariant.twin
		ensure
			equal (my_index, an_index)
			equal (my_parents, some_parents)
			equal (my_features, some_features)
			equal (my_class_invariant, an_invariant)
		end
		
feature -- Access

	hash_code: INTEGER is
		do
			check false end
		end

	index: INDEX_LIST is
			-- The index list of this class interface.
		do
			Result := my_index.twin
		end

	parents: CLASS_TYPE_LIST is
		do
			Result := my_parents.twin
		end

	features: FEATURE_CLAUSE_LIST is
		do
			Result := my_features.twin
		ensure
			result_not_void: Result /= Void
			feature_count_non_negative: Result.count >= 0
		end

	class_invariant: CLASS_INVARIANT is
		do
			Result := my_class_invariant.twin
		end

feature -- Measurement

	index_count: INTEGER is
			-- The number of index terms of this interface.
		do
			if my_index /= Void then
				Result := my_index.count
			end
		ensure
			Result >= 0
		end

	parent_count: INTEGER is
		do
			if my_parents /= Void then
				Result := my_parents.count
			end
		ensure
			Result >= 0
		end

	feature_count: INTEGER is
		do
			Result := my_features.count
		ensure
			Result > 0
		end

	class_invariant_count: INTEGER is
		do
			if my_class_invariant /= Void then
				Result := 1
			end
		ensure
			Result = 0 or Result = 1
		end

--feature -- Comparison
--
--	is_equal (other: like Current): BOOLEAN is
--		do
--			Result :=
--				my_index = other.my_index and
--				my_parents = other.my_parents and
--				my_features = other.my_features and
--				my_class_invariant = other.my_class_invariant
--		end
	
feature -- Element change

	set_index (an_index: INDEX_LIST) is
		do
			my_index := an_index.twin
		ensure
			index.is_equal (an_index)
		end

	add_index_clause (a_clause: INDEX_CLAUSE) is
		do
			my_index.put_last (a_clause)
		ensure
			index.has (a_clause)
		end

	-- parents

	set_parents (some_parents: CLASS_TYPE_LIST) is
		do
			my_parents := some_parents.twin
		ensure
			parents.is_equal (some_parents)
		end

	add_parents (some_parents: CLASS_TYPE_LIST) is
		do
			my_parents.extend_last (some_parents.twin)
--		ensure
--			some_parents.is_subset (parents)
		end

	add_parent (a_parent: CLASS_TYPE) is
		require
			a_parent /= Void
		do
			my_parents.put_last (a_parent.twin)
		ensure
			parents.has (a_parent)
		end

feature -- Removal

	wipe_out is
		do
			clear_index
			clear_parents
			clear_features
			clear_class_invariant
		ensure
			index.is_empty
			parents.is_empty
			features.is_empty
--			class_invariant.is_empty
		end

	clear_index is
		do
			my_index.wipe_out
		ensure
			index.is_empty
		end

	remove_indices (some_indices: INDEX_LIST) is
		do
-- 			my_index.subtract (some_indices.to_list)
-- 		ensure
-- 			index.is_disjoint (some_indices)
		end

	remove_index (an_index: INDEX_CLAUSE) is
		do
-- 			my_index.remove (an_index)
-- 		ensure
-- 			index.is_disjoint (an_index)
		end

	clear_parents is
		do
			my_parents.wipe_out
		ensure
			parents.is_empty
		end

	remove_parents (some_parents: CLASS_TYPE_LIST) is
		do
-- 			my_parents.subtract (some_parents)
-- 		ensure
-- 			parents.is_disjoint (some_parents)
		end

	remove_parent (a_parent: CLASS_TYPE) is
		do
			my_parents.delete (a_parent)
		ensure
			not parents.has (a_parent)
		end

	clear_features is
		do
			my_features.wipe_out
		ensure
			features.is_empty
		end

	remove_features (some_features: FEATURE_CLAUSE_LIST) is
		do
-- 			my_parents.subtract (some_parents)
-- 		ensure
-- 			parents.is_disjoint (some_parents)
		end

	remove_feature (a_feature: FEATURE_CLAUSE) is
		do
			my_features.delete (a_feature)
		ensure
			not features.has (a_feature)
		end

	clear_class_invariant is
		do
			my_class_invariant := Void
		ensure
			class_invariant = Void
		end

	remove_class_invariants (some_invariants: INVARIANT_LIST) is
		do
-- 			my_parents.subtract (some_parents)
-- 		ensure
-- 			parents.is_disjoint (some_parents)
		end

	remove_class_invariant (an_invariant: CLASS_INVARIANT) is
		do
			if an_invariant.is_equal (my_class_invariant) then
				clear_class_invariant
			end
--		ensure
--			not my_class_invariant.has (an_invariant)
		end

feature -- Transformation

	canonicalize: like Current is
		do
			create Result.make (my_index.canonicalize, my_parents.canonicalize,
				my_features.canonicalize, my_class_invariant.canonicalize)
		end

feature -- Conversion

feature -- Output

	bon_out: STRING is
		do
			Result.make_empty
			Result.append (my_index.bon_out + "%N")
			if my_parents.count /= 0 then
				Result.append ("inherit " + my_parents.bon_out + "%N")
			end
			Result.append (my_features.bon_out)
			Result.append ("invariant%N" + my_class_invariant.bon_out + "%N")
			Result.append ("end%N")
		end

feature -- Duplication

feature -- Miscellaneous

feature -- Basic operations

-- 	append (other: like Current): like Current is
-- 			-- Add all parts of `other' to current chart.
-- 		do
-- 			Result := Precursor (other)
-- 			Result.my_parents.append (other.my_parents.twin)
-- 			Result.my_queries.append (other.my_queries.twin)
-- 			Result.my_commands.append (other.my_commands.twin)
-- 			Result.my_constraints.append (other.my_constraints.twin)
-- 		end

-- 	intersect (other: like Current) is
-- 			-- Remove all parts not in `other'.
-- 		do
-- 			Precursor (other)
-- 			my_parents.intersect (other.my_parents)
-- 			my_queries.intersect (other.my_queries)
-- 			my_commands.intersect (other.my_commands)
-- 			my_constraints.intersect (other.my_constraints)
-- 		end

-- 	subtract (other: like Current) is
-- 			-- Remove all parts also included in `other'.
-- 		do
-- 			Precursor (other)
-- 			my_parents.subtract (other.my_parents)
-- 			my_queries.subtract (other.my_queries)
-- 			my_commands.subtract (other.my_commands)
-- 			my_constraints.subtract (other.my_constraints)
-- 		end

-- 	symdif (other: like Current) is
-- 			-- Add parts of `other' which are not included in current chart 
-- 			-- and remove those which are.
-- 		do
-- 			Precursor (other)
-- 			my_parents.symdif (other.my_parents)
-- 			my_queries.symdif (other.my_queries)
-- 			my_commands.symdif (other.my_commands)
-- 			my_constraints.symdif (other.my_constraints)
-- 		end

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

feature {CLASS_INTERFACE} -- Implementation

	my_index: INDEX_LIST
	my_parents: CLASS_TYPE_LIST
	my_features: FEATURE_CLAUSE_LIST
	my_class_invariant: CLASS_INVARIANT

invariant

	my_features /= Void
	my_features.count >= 0

end -- class CLASS_INTERFACE
