(theory escjava2-object-logic
  :notes "SMT-LIB realization of ESC/Java2's object logic.
          by Cesare Tinelli and Joe Kiniry
          Begun 24 June 2004
          $Id$
          Based upon SRC ESC/Java object logic
            (design document ESCJ8a)"

  :sorts ( # sort that represents *values* of Java's boolean base type
           booleanValue
           # sort that represents *values* of all Java's base types but boolean
           numberValue
           # sort that represents all Java non-base types
           objectType
           # ... represents object references
           objectRef
           # ... represents object values
           objectValue
           # field names
           field
           # 
           memory )

  :funs ( (java.lang.Object objectType)
          (0       number)
          (1       number)
          (maxLong  number)  (minLong  number)
          (maxInt   number)  (minInt   number)
          (maxShort number)  (minShort number)
          (maxByte  number)  (minByte  number)
          (maxChar  number)  (minChar  number)

          (TRUE     boolean) (FALSE   boolean)

          (narrowLong2Int number number)
          (narrowLong2Short number number)
          ...etc...

          (NULL     objectRef)
          (+        number number number)
          (-        number number number)
          ...etc...

          (!        boolean boolean)
          (&&       boolean boolean boolean)
          (||       boolean boolean boolean)
          ...etc...

          (?:number      boolean number number)
          (?:boolean     boolean boolean boolean)
          (?:object boolean objectRef objectRef)
          (?:objectArray boolean objectArray objectArray)

          (arrayBoolean  objectType)
          (arrayNumber   objectType)
          (arrayObject   objectType objectType)

          (elementTypeObject objectType objectType)

          (typeOf objectRef objectType)
          (cast objectRef objectType objectRef)

          # 
          (getNumber objectValue numberValue numberValue)
          (setNumber objectValue numberValue numberValue objectValue)
          #
          (getBoolean objectValue numberValue booleanValue)
          (setBoolean objectValue numberValue booleanValue objectValue)
          #
          (getObject objectValue numberValue objectRef)
          (setObject objectValue numberValue objectRef objectValue)

          #
          (getMem memory objectRef objectValue)
          (setMem memory objectRef objectValue memory)

          #
          (selectObject field objectValue objectRef)
          (storeObject field objectValue objectRef field)

          (selectNumber field objectValue numberValue)
          (storeNumber field objectValue numberValue field)

          (selectBool field objectValue booleanValue)
          (storeBool field objectValue booleanValue field)

          (selectClassObject field objectType objectRef)
          (storeClassObject field objectType objectRef field)

          (selectClassNumber field objectType numberValue)
          (storeClassNumber field objectType numberValue field)

          (selectClassBool field objectType booleanValue)
          (storeClassBool field objectType booleanValue field)

          (vAllocTime objectRef numberValue)
         )

  :preds ( (isChar number)
           (isByte number)
           (isShort number)
           (isInt number)
           (isLong number)
           (isZ number)
           (isFloat number)
           (isDouble number)

           (extends objectType objectType)
           (<:      objectType objectType :reflex :trans)
           
           # Cesare says these are built-in, since they are 
           # not easily axiomatized.
           (< number number)
           (<= number number)
           ...etc...


           # "is a" predicate
           (isa objectRef objectType)

           # 
           (instantiable objectType)

           #
           (isAllocated objectRef)
      )
           

  :extensions ()

  :definition "Unlike the logic in ESCJ8a, this is a 
    many-sorted logic.
    Additionally, this is a prover-independent logic.  We only
    assume that the prover provides:
      o a theory of rational arithemetic
      o a theory of arrays
      o a theory of uninterpreted function symbols on which
        equality is defined"

  :axioms ( # extends is antireflexive
            (forall ?x objectType (not (extends ?x ?x)) )
            # subtype includes extends
            (forall ?x objectType
               (forall ?y objectType
                  (implies (extends ?x ?y) (<: ?x ?y))))
            # subtype transitivity
            (forall ?x objectType
               (forall ?y objectType
                  (forall ?z objectType
                     (implies (and (<: ?x ?y)
                                   (<: ?y ?z))
                              (<: ?x ?z)))))
            # subtype reflexivity
            (forall ?x objectType (<: ?x ?x))
            # subtype is the smallest relation that contains extends
            (forall ?x objectType
               (forall ?y objectType
                  (implies (and (<: ?x ?y)
                                (not (= ?x ?y)))
                           (exists ?z objectType
                              (and (extends ?x ?z)
                                   (<: ?z ?y))))))

            # <: is anti-symmetric
            (forall ?x objectType
               (forall ?y objectType
                 (implies (and (<: ?x ?y) (<: ?y ?x))
                          (= (?x ?y)))))

            # java.lang.Object is top of subtype hierarchy
            (forall ?x objectType (<: ?x java.lang.Object))

            # subtype rules for arrays
            (forall ?x objectType
               (forall ?y objectType
                 (implies (<: ?x ?y)
                          (<: (array ?x) (array ?y)))))

            # left inverses of object constructors
            (forall ?x objectType
               (= (elementTypeObject (arrayObject ?x))
                  ?x))

            # integral type boundaries
            (= minByte -128)
            (= maxByte 127)
            (forall ?x numberValue
               (iff (isByte ?x) (and (<= minByte ?x)
                                     (<= ?x maxByte))))
            ...

            # define an approximation of Z
            (isZ 0)
            (isZ 1)
            (forall ?x number
              (iff (isZ ?x) (isZ (+ ?x 1))))
            (forall ?x number
              (implies (isZ ?x)
                (forall ?y number
                  (implies (and (< ?x ?y)
                                (< ?y (+ ?x 1)))
                           (not (isZ ?y))))))

         
            # all object reference are NULL or have a unique dynamic subtype
            (forall ?x objectRef
              (forall ?t objectType 
                (iff (isa ?x ?t)
                     (or (= ?x NULL)
                         (typeOf ?x ?t)))))

            # definition of cast
            (forall ?x objectRef
              (forall ?t objectType 
                (isa (cast ?x ?t) ?t)))

            # upcasting a value does not change it
            (forall ?x objectRef
              (forall ?t objectType 
                (implies (isa ?x ?t)
                         (= (cast ?x ?t) ?x))))


            # TRUE and FALSE are distinct values
            (distinct TRUE FALSE)

	    # TRUE and FALSE are the only boolean values
            (forall ?x boolean (or (= ?x TRUE)
                                   (= ?x FALSE)))

            # definition of boolean operators
            ...

	    # definition of instantiable type
            (instantiable arrayBoolean)
            (instantiable arrayNumber)
            (instantiable java.lang.Object)
            (forall ?x objectRef (instantiable (typeOf ?x)))
            (forall ?x objectType (iff (instantiable ?x)
                                       (instantiable (arrayObject ?x))))
            # to be checked
            (forall ?x objectType
              (forall ?y objectType 
                (implies (and (subtype ?x ?y)
                              (instantiable ?x))
                         (instantiable ?x))))

            # for simplicity, get* and set* functions are defined
            # on all object values, whether they are arrays or not

            (forall ?a objectValue
              (for all ?i numberValue 
                (forall ?x numberValue
                   (= (getNumber (setNumber ?a ?i ?x) ?i) 
                      ?x))))
             (forall ?a objectValue 
               (for all ?i numberValue 
                 (for all ?j numberValue 
                   (forall ?x numberValue
                     (or (= ?i ?j)
                         (= (getNumber (setNumber ?a ?i ?x) ?j)
                            (getNumber ?a ?j)))))))

            (forall ?a objectValue
              (for all ?i numberValue 
                (forall ?x booleanValue
                  (= (getBoolean (setBoolean ?a ?i ?x) ?i) 
                     ?x))))
            (forall ?a objectValue 
              (for all ?i numberValue 
                (for all ?j numberValue 
                  (forall ?x booleanValue
                    (or (= ?i ?j)
                        (= (getBoolean (setBoolean ?a ?i ?x) ?j)
                           (getBoolean ?a ?j))))))

            (forall ?a objectValue
              (for all ?i numberValue 
                (forall ?x objectRef
                  (= (getObject (setObject ?a ?i ?x) ?i) 
                     ?x))))
            (forall ?a objectValue 
              (for all ?i numberValue 
                (for all ?j numberValue 
                  (forall ?x objectRef
                    (or (= ?i ?j)
                        (= (getObject (setObject ?a ?i ?x) ?j)
                           (getObject ?a ?j)))))))


            (forall ?m memory
              (for all ?o objectRef 
                (forall ?x objectValue
                  (= (getMemory (setMemory ?m ?o ?x) ?o) 
                     ?x))))
            (forall ?m memory 
              (for all ?o1 objectRef 
                (for all ?o2 objectRef 
                  (forall ?x objectValue
                    (or (= ?o1 ?o2)
                        (= (getMemory (setMemory ?m ?o1 ?x) ?o2)
                           (getMemory ?m ?o2)))))))

            # axioms for select
            ...

            (forall ?x objectRef
              (forall ?t numberValue
                (iff (isAllocated x) (< (vAllocTime x) ?t))))


  )

end)