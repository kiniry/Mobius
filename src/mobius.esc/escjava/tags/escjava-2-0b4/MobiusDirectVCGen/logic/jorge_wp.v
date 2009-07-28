Definition wps_i pc (s0 : SInitState) (s: SLocalState) : SWp:=
      match BYTECODEMETHOD.instructionAt m pc with
      | Some ins =>
(** Basic instruction *)
        match ins, s with
        | Aconst_null, (h, os, l) => wps_next pc s0 (h, SVVar Null :: os, l)

        | Arraylength, (h, val :: os', l) =>
          let wp := Forall length : BtInt, 
                    Forall tp : BtType,
                     HTypeArray pc h val length tp -->
                     wps_next pc s0 (h, SVnum length :: os', l) in
          wps_checkNull pc val O wp h l s0
          (*(SisNull val --> wps_NullPointerException pc h l s0)
          & (! SisNull val --> wp)*)

        | Checkcast t, (h, val :: os', l) =>
          (wps_jvmExc (Sassign_compatible pc h val (ReferenceType t))
             (wps_next pc s0 (h, val :: os', l))
             pc ClassCastException h l s0)

        | Const t z, (h, os, l) => SIntBound pc t z -->
            wps_next pc s0 (h, (SVnum ((SIVar (Int.const z)))) :: os, l)

        | Dup, (h, v :: os, l) => wps_next pc s0 (h, v :: v :: os, l)
        | Dup_x1, (h, v1 :: v2 :: os',l) => 
          (wps_next pc s0 (h, v1 :: v2 :: v1 :: os', l))
        | Dup_x2, (h, v1 :: v2 :: v3 :: os', l) =>
          (wps_next pc s0 (h, v1 :: v2 :: v3 :: v1 :: os', l))
        | Dup2, (h, v1 :: v2 :: os', l) =>
          (wps_next pc s0 (h, v1 :: v2 :: v1 :: v2 :: os', l))
        | Dup2_x1, (h, v1 :: v2 :: v3 :: os', l) =>
          (wps_next pc  s0 (h, v1 :: v2 :: v3 :: v1 :: v2 :: os', l))
        | Dup2_x2, (h, v1 :: v2 :: v3 :: v4 :: os', l) =>
          (wps_next pc  s0 (h, v1 :: v2 :: v3 :: v4 :: v1 :: v2 :: os', l))
   
      	| Getfield f, (h, val :: os', l) =>
          let ft := FIELDSIGNATURE.type (snd f) in
          (*let wp := match ft with
                    | PrimitiveType _ => Forall i : BtInt,
                    (HGet pc h (SAMDynamicField (svalue2sloc val) f) (SVnum (SnI i)) --> 
                       wps_next pc s0 (h, (SVnum (SnI i)) :: os', l))
                    | ReferenceType _ => Forall loc : BtLocation,
                    (HGet pc h (SAMDynamicField (svalue2sloc val) f) (SVRef loc) --> 
                       wps_next pc s0 (h, (SVRef loc) :: os', l))
                    end in
                    *)
          let wp2 := let v := SHGet h (SAMDynamicField (svalue2sloc val) f) in 
                     wps_next pc s0 (h, v :: os', l)
          in
          wps_checkNull pc val O wp2 h l s0
	  (*(SisNull val --> wps_NullPointerException pc h l s0)
	  & (! SisNull val --> wp)*)

        | Getstatic f, (h, os, l) =>
          let v := SHGet h (SAMStaticField f) in 
          SisStatic pc f --> wps_next pc s0 (h, v :: os, l)

        | I2b, (h, i :: os', l) => 
          (wps_next pc s0 (h, SVnum (SI2b i) :: os', l))
        | I2s, (h, i :: os', l) =>
          (wps_next pc s0 (h, SVnum (SI2s i) :: os', l))

        | Ibinop DivInt, (h, i2 :: i1 :: os', l) =>
          let x:=ArithmeticException in 
          (*SisZero pc i1 --> SisZero pc i2 --> 
          (wps_next pc s0 (h, SVnum (SIBinop DivInt i1 i2) :: os', l))*)
          (wps_jvmExc (SNeg (SisZero pc i2))
            (wps_next pc s0 (h, SVnum (SIBinop DivInt i1 i2) :: os', l))
            pc ArithmeticException h l s0)
        | Ibinop RemInt, (h, i2 :: i1 :: os', l) =>
          (wps_jvmExc (SNeg (SisZero pc i2))
            (wps_next pc s0 (h, SVnum (SIBinop RemInt i1 i2) :: os', l))
            pc ArithmeticException h l s0)
        | Ibinop op, (h, i2 :: i1 :: os', l) =>
          (wps_next pc s0 (h, SVnum (SIBinop op i1 i2) :: os', l))

        | Iinc x z, (h, os, l) =>
(*          Forall i : BtInt,*)
          (SCheckByteSize pc z -->
(*            SLvGet l x i --> *)
              wps_next pc s0 (h, os, mkupdate l x (SVnum (SIBinop AddInt (SLvGet l x) (SVnum (SIVar (Int.const z)))))))

        | Ineg, (h, i :: os', l) =>
          (wps_next pc s0 (h, SVnum (SINeg i) :: os', l))

        | Instanceof t, (h, loc :: os', l) =>
          ((SisNull pc loc --> wps_next pc s0 (h, (SVnum (SIVar (Int.const 0))) :: os', l))
          & (! SisNull pc loc -->
                wps_cond (Sassign_compatible pc h loc (ReferenceType t))
                  (wps_next pc s0 (h, (SVnum (SIVar (Int.const 1))) :: os', l))
                  (wps_next pc s0 (h, (SVnum (SIVar (Int.const 0))) :: os', l))))

        | New c, (h, os, l) =>
          Forall loc : BtLocation,
          (Forall h' : BtHeap,
           (HNewObject pc h c loc h' -->
            wps_next pc s0 (h', SVRef loc :: os, l)))

        | Newarray t, (h, i :: os', l) => 
          (wps_jvmExc (SNonNegative pc i)
            (Forall loc : BtLocation,
            (Forall h' : BtHeap,
             (HNewArray pc h i t loc h' -->
               wps_next pc s0 (h', SVRef loc :: os', l))))
            pc NegativeArraySizeException h l s0)

        | Nop, s => wps_next pc s0 s

        | Pop, (h, v :: os, l) => wps_next pc s0 (h, os, l)
        | Pop2, (h, v1 :: v2 :: os, l) => wps_next pc s0 (h, os, l)

        | Putfield f, (h, v :: loc :: os', l) =>
	  let wp := Forall cn : BtClassName,
                (HTypeObject pc h loc cn -->
                 Sdefined_field pc cn f -->
                 Sassign_compatible pc h v (FIELDSIGNATURE.type (snd f)) -->
                 wps_next pc s0 (SHUpdate h (SAMDynamicField (svalue2sloc loc) f) v, os', l)) in
	  wps_checkNull pc loc 1 wp h l s0

        | Putstatic f, (h, v :: os', l) =>
          (SisStatic pc f -->
           Sassign_compatible pc h v (FIELDSIGNATURE.type (snd f)) -->
           wps_next pc s0 (SHUpdate h (SAMStaticField f) v, os', l))

        | Swap, (h, v1 :: v2 :: os', l) =>
          (wps_next pc s0 (h, v2 :: v1 :: os', l))
 
        | Vaload k, (h, i :: loc :: os', l) =>
          ((SisNull pc loc --> wps_NullPointerException pc h l s0)
          & (SNeg (SisNull pc loc) -->
              (Forall length : BtInt,
              (Forall t : BtType,
               (HTypeArray pc h loc length t --> 
                (*Scompat_ArrayKind_type pc k t -->*)
                wps_bound i (SVnum length)
                  (let v := SHGet h (SAMArrayElement (svalue2sloc loc) i) in
                    (*Scompat_ArrayKind_value pc k v -->*)
                    wps_next pc s0 (h, SConv4Stack v :: os', l))
                pc h l s0)))))

        | Vastore k, (h, val :: i :: loc :: os', l) =>
          ((SisNull pc loc --> wps_NullPointerException pc h l s0)
          & (SNeg (SisNull pc loc) -->
              (Forall length : BtInt,
              (Forall t : BtType,
               (HTypeArray pc h loc length t -->
                (*Scompat_ArrayKind_type pc k t -->
                Scompat_ArrayKind_value pc k val -->*)
                wps_bound i (SVnum length)
                 (wps_jvmExc (Sassign_compatible pc h val t)
                   (wps_next pc s0
                     (SHUpdate h (SAMArrayElement (svalue2sloc loc) i) (SConv4Array val t), os', l))
                     pc ArrayStoreException h l s0)
                 pc h l s0)))))
                     
        | Vload k x, (h, os, l) =>
(*          Forall v : BtValue,*)
            (*Scompat_ValKind_value pc k (SLvGet l x) -->*)
            wps_next pc s0 (h, (SLvGet l x) :: os, l)

        | Vstore k x, (h, v :: os', l) =>
          ((*Scompat_ValKind_value pc k v --> *)wps_next pc s0 (h, os', mkupdate l x v))

        | Athrow, (h, loc :: os', l) =>
          ((SisNull pc loc --> wps_NullPointerException pc h l s0)
          & (SNeg (SisNull pc loc) --> 
             (Forall cn : BtClassName,
              (HTypeObject pc h loc cn -->
              (Ssubclass_name pc cn javaLangThrowable -->
              wps_Exception_unknown pc loc cn h l s0)))))
         
        | Vreturn k, (h, val :: os, l) =>
          match METHODSIGNATURE.result (METHOD.signature m) with
          | Some t => Sassign_compatible pc h val t -->
                      Scompat_ValKind_value pc k val -->
                      SPost pc None m s0 (h, SRVNormalSome val)
          | _ => STrue pc
          end

        | Return, (h, os, l) =>
          match METHODSIGNATURE.result (METHOD.signature m) with
          | None => SPost pc None m s0 (h, @SRVNormalNone SValue)
          | _ => STrue pc
          end

        | Goto o, _ => wps_label (OFFSET.jump pc o) s0 s

        | If_acmp cmp o, (h, val2 :: val1 :: os', l) =>
          (wps_cond (SCompRef pc cmp val1 val2)
            (wps_label (OFFSET.jump pc o) s0 (h, os', l))
            (wps_next pc s0 (h, os', l)))
        | If_icmp cmp o, (h, i2 :: i1 :: os', l) =>
          (wps_cond (SCompInt pc cmp i1 i2)
            (wps_label (OFFSET.jump pc o) s0 (h, os', l))
            (wps_next pc s0 (h, os', l)))
        | If0 cmp o, (h, i :: os', l) =>
          (wps_cond (SCompInt pc cmp i (SVnum (SIVar (Int.const 0))))
            (wps_label (OFFSET.jump pc o) s0 (h, os', l))
            (wps_next pc s0 (h, os', l)))
        | Ifnull cmp o, (h, loc :: os', l) =>
          (wps_cond (SCompRef pc cmp loc Null)
            (wps_label (OFFSET.jump pc o) s0 (h, os', l))
            (wps_next pc s0 (h, os', l)))

        | Invokestatic msig, (h, os, l) => 
          match findMethod p msig with
          | None => SFalse pc
          | Some m' =>
            if METHOD.isNative m' then SFalse pc
            else 
             match globalLookup p msig with
             | None => SFalse pc
             | Some (pairT pre post) =>
               let n := length (METHODSIGNATURE.parameters (snd msig)) in
  	       let (l', os') := init_args n os in
  	       (*pre (l', h) /\ *)
               match METHODSIGNATURE.result (snd msig) with
               | None =>
                 Forall rh : BtHeap,
                 (((SPre pc None msig (l',h) --> SPost pc None msig (l',h) (rh, @SRVNormalNone SValue)) -->
                  wps_next pc s0 (rh, os', l))
                 & (Forall loc : BtLocation,
                    (Forall cn : BtClassName,
                     (HTypeObject pc rh (SVRef loc) cn -->
                      (SPre pc None msig (l', h) --> SPost pc None msig (l', h) (rh, SRVException loc)) -->
                      wps_Exception_unknown pc loc cn rh l s0))))

               | Some _ =>
                 Forall rh : BtHeap,
                 ((Forall v : BtValue,
                   ((SPre pc None msig (l', h) --> SPost pc None msig (l', h) (rh, SRVNormalSome v)) -->
                    wps_next pc s0 (rh, v :: os', l)))
                 & (Forall loc : BtLocation,
                    (Forall cn : BtClassName,
                     (HTypeObject pc rh (SVRef loc) cn -->
                      (SPre pc None msig (l', h) --> SPost pc None msig (l', h) (rh, SRVException loc)) -->
                      wps_Exception_unknown pc loc cn rh l s0))))
                end
             end
          end 

        | Invokeinterface _, _ => SFalse pc
        | Invokespecial _, _ => SFalse pc
        | Invokevirtual msig, (h, os, l) =>
          match findMethod p msig with
          | None => SFalse pc
          | Some m' =>
            if METHOD.isNative m' then SFalse pc
            else 
             match globalLookup p msig with
             | None => SFalse pc
             | Some (pairT pre post) =>
               let n := length (METHODSIGNATURE.parameters (snd msig)) in
               match pop _ n os with 
               v :: _ => 
               let wp := 
                  (let (l', os') := init_args (n+1) os in
                   match METHODSIGNATURE.result (snd msig) with
                   | None =>
                     Forall rh : BtHeap,
                      (((SPre pc None msig (l',h) --> SPost pc None msig (l', h) (rh, @SRVNormalNone SValue)) -->
                         wps_next pc s0 (rh, os', l))
                       & (Forall loc : BtLocation,
                           (Forall cn : BtClassName,
                            (HTypeObject pc rh (SVRef loc) cn -->
                             (SPre pc None msig (l', h) --> SPost pc None msig (l', h) (rh, SRVException loc)) -->
                             wps_Exception_unknown pc loc cn rh l s0))))
                   | Some (PrimitiveType _) => 
                     Forall rh : BtHeap,
                     (Forall i : BtInt,
                      (SPre pc None msig (l',h) --> SPost pc None msig (l', h) (rh, (SRVNormalSome (SVnum (SnI i))))) -->
                         wps_next pc s0 (rh, (SVnum (SnI i)) :: os', l))
                       & (Forall loc : BtLocation,
                          Forall cn : BtClassName,
                            HTypeObject pc rh (SVRef loc) cn -->
                            (SPre pc None msig (l', h) --> SPost pc None msig (l', h) (rh, SRVException loc)) -->
                             wps_Exception_unknown pc loc cn rh l s0)
                   | Some (ReferenceType _) => 
                     Forall rh : BtHeap,
                     (Forall lr : BtLocation,
                      (SPre pc None msig (l',h) --> SPost pc None msig (l', h) (rh, (SRVNormalSome (SVRef lr)))) -->
                         wps_next pc s0 (rh, (SVRef lr) :: os', l))
                       & (Forall loc : BtLocation,
                          Forall cn : BtClassName,
                            HTypeObject pc rh (SVRef loc) cn -->
                            (SPre pc None msig (l', h) --> SPost pc None msig (l', h) (rh, SRVException loc)) -->
                             wps_Exception_unknown pc loc cn rh l s0)
                   end) in
	       wps_checkNull pc v n wp h l s0 
               | _ => STrue pc
               end
             end
          end 
        | Lookupswitch _ _ , _=> SFalse pc
        | Tableswitch _ _ _ _, _ => SFalse pc
 
        | _, _ => STrue pc
        end
      | None => SFalse pc
      end.
