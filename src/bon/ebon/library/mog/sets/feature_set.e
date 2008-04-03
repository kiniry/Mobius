indexing
	description: "A nonempty set of feature specifications."

class
	FEATURE_SET

inherit
	MOG_SET [FEATURE_CLAUSE]

creation
	make_set, make_optional_rest, make_optional_first,
	make_from_set, make_from_list

end -- class FEATURE_SET
