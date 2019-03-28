(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open Names
open Pp
open Lazy

(* From Coqlib *)
let make_dir l = DirPath.make (List.rev_map Id.of_string l)

(** [get_type_of] performs beta reduction ;
    Is it ok for Retyping.get_type_of (Zpower_nat n q) to return (fun _ : nat => Z) q ? *)
let get_type_of env evd e =
  Tacred.cbv_beta env evd (Retyping.get_type_of env evd e)

(** [unsafe_to_constr c] returns a [Constr.t] without considering an evar_map.
    This is useful for calling Constr.hash *)
let unsafe_to_constr c = EConstr.to_constr ~abort_on_undefined_evars:false Evd.empty c


let pr_constr env evd e =
  Printer.pr_constr_env env evd (unsafe_to_constr e)


let debug = false (** Debug flag to get some intermediate terms *)



(** [is_constructor evd c] holds if the term is solely made of constructors *)
let rec is_constructor evd c =
    match EConstr.kind evd c with
    | App(c, args) ->
       if EConstr.isConstruct evd c
       then
         Array.fold_left (fun acc e -> acc && is_constructor evd e) true args
       else false
    |  _ -> false


(** [get_arrow_typ evd t] returns [t1;..tn] such that t = t1 -> ... -> tn.ci_npar
    (only syntactic matching)
 *)
let rec get_arrow_typ evd t  =
  match EConstr.kind evd t with
  | Prod (a,p1,p2) (*when a.Context.binder_name = Names.Anonymous*) ->
       p1::(get_arrow_typ evd p2)
  |  _ -> [t]

        (*
let get_arrow_typ evd t  =
  let r = get_arrow_typ evd t in
  let env = Global.env () in
  Feedback.msg_debug Pp.(str "get_arrow_typ "++(Termops.Internal.debug_print_constr t)++str" = "++
                           Pp.seq (List.map (pr_constr  env evd) r));
  r
         *)




(** [is_binary_arrow t] return t' such that t = t' -> t' -> t' *)
let is_binary_arrow evd t =
  let l = get_arrow_typ evd t in
  match l with
  | []  -> assert false
  | [t1;t2;t3] ->  Some (t1,t2,t3)
  |  _   -> None

(** [is_unary_arrow t] return t' such that t = t' -> t' *)
let is_unary_arrow evd t =
  let l = get_arrow_typ evd t in
  match l with
  | []  -> assert false
  | [t1;t2] -> Some (t1,t2)
  |  _   -> None


(** [HConstr] is a map indexed by EConstr.t.
    It should only be used using closed terms.
 *)
module HConstr =
  struct
    module M =
      Map.Make(
          struct
            type t = EConstr.t

            let compare c c' = Constr.compare (unsafe_to_constr c) (unsafe_to_constr c')

          end)

    let is_empty m = M.is_empty m

    let lfind h m =
      try M.find h m
      with Not_found -> []


    let add h e m =
      let l = lfind h m in
      M.add h (e::l) m

    let empty = M.empty

    let find h m =
      match lfind h m with
      | e::_ -> e
      | [] -> raise Not_found


    let find_all  = lfind

    let fold f m acc =
      M.fold (fun k l acc ->
          List.fold_left (fun acc e -> f k e acc) acc l) m acc

    let iter f m = M.iter f m

  end


(** [get_projections_from_constant (evd,c) ]
    returns an array of constr [| a1,... an|] such that [c] is defined as
    Definition c := mk a1 ... an with mk a constructor.
    ai is therefore either a type parameter or a projection.
*)
let get_projections_from_constant (evd,i) =
  match EConstr.kind evd i with
  | Constr.Const(c,_ ) ->
     begin
       match Global.body_of_constant Library.indirect_accessor c with
       | None -> failwith "Add Injection requires a constant (with a body)"
       | Some(c,_,_) ->
          match EConstr.kind evd  (EConstr.of_constr c) with
          | App(c,a) -> Some a
          |    _            -> None
         end
      |   _   -> None

(** [reduce_term evd t] carefully unfolds aliases in [t] i.e.
    if t = ctx[c] where c is a constant which
    body is another constant c' then
    [reduce_term env evd t] returns ctx[c']

    This could be made more agressive...
 *)

let rec unfold_const evd c ctx =
  match Global.body_of_constant Library.indirect_accessor c with
  | None -> EConstr.mkConstU(c,ctx)
  | Some (b,_,u) ->
     match EConstr.kind evd (EConstr.of_constr b) with
     | Const(c',ctx') -> unfold_const evd c' ctx'
     | Ind i      -> EConstr.mkIndU i
     | _              -> EConstr.mkConstU(c,ctx)

let rec reduce_term evd t =
  match EConstr.kind evd t with
  | Const(c,ctx) -> unfold_const evd c ctx
  | App(c,a) -> EConstr.mkApp(reduce_term evd c,
                              Array.map (reduce_term evd) a)
  | _ -> t (* could do more... *)

(**  An instance of type, say T, is registered into a hashtable, say TableT. *)

type 'a decl = {
    decl  : EConstr.t; (* Registered type instance *)
    deriv : 'a         (* Projections of insterest *)
  }

module type Elt =
  sig
    type elt

    (** [name]  of the table *)
    val name    : string

    (** [get_key] is the type-index used as key for the instance *)
    val get_key : int

    (** [mk_elt evd i [a0,...,an]  returns the element of the table
        built from the type-instance i and the arguments (type indexes and projections)
        of the type-class constructor. *)
    val mk_elt  : Evd.evar_map -> EConstr.t -> EConstr.t array -> elt

  end

module MakeTable(E : Elt) =
  struct
    (** Given a term [c] and its arguments ai,
        we construct a HConstr.t table that is
        indexed by ai for i = E.get_key.
        The elements of the table are built using E.mk_elt c [|a0,...,an|]
     *)

    type elt = E.elt decl

    let make_elt (evd,i) =
      match get_projections_from_constant (evd,i) with
      | None ->
         let env = Global.env () in
         let t = string_of_ppcmds (pr_constr env evd  i) in
         failwith ("Cannot register term "^t)
      | Some a -> E.mk_elt evd i a

    let table = Summary.ref ~name:("zify_"^E.name) HConstr.empty

(*    let pp_table () =
      let env = Global.env () in
      let evd = Evd.from_env env in
      HConstr.fold (fun k _ acc -> pr_constr env evd  k ++ Pp.str " " ++ acc) !table (Pp.str "")
 *)

    let register_constr env evd c =
      let c = EConstr.of_constr c in
      let t = get_type_of env evd c in
      match EConstr.kind evd t with
      | App(intyp,args) ->
         let styp = reduce_term evd (args.(E.get_key)) in
         let elt  = {decl = c; deriv = make_elt (evd,c)} in
         table :=  HConstr.add   styp elt !table;
      | _               ->
         failwith "Can only register terms of type [F X1 ... Xn]"


    let get evd c =
      let c' = reduce_term  evd  c in
      HConstr.find c' !table

    let get_all evd c =
      let c' = reduce_term  evd  c in
      HConstr.find_all c' !table


    let fold_declared_const f evd acc =
      HConstr.fold (fun _ e acc -> f (fst (EConstr.destConst evd e.decl)) acc) !table acc

    let pp_keys ()  =
      let env = Global.env () in
      let evd = Evd.from_env env in
      HConstr.fold (fun k _ acc -> Pp.(pr_constr env evd k ++ str " "++ acc)) !table (Pp.str "")


    let new_id =
      let id = ref 0 in
      fun () ->
      incr id ;
      Names.Id.of_string (E.name^"_"^(string_of_int !id))

    let register_obj : Constr.constr ->  Libobject.obj  =
      let cache_constr (_,c) =
        let env = Global.env () in
        let evd = Evd.from_env env in
        register_constr env evd c in
      let subst_constr (subst,c) = Mod_subst.subst_mps subst c in

      (Libobject.declare_object @@ (Libobject.superglobal_object_nodischarge ("register-zify-"^E.name)
                                        ~cache:cache_constr
                                        ~subst:(Some subst_constr))

      )

   (** [register c] is called from the VERNACULAR ADD [name] constr(t).
       The term [c] is interpreted and
       registered as a [superglobal_object_nodischarge].
       TODO: pre-compute [get_type_of] - [cache_constr] is using another environment.
    *)
    let register  c =
      let env = Global.env () in
      let evd = Evd.from_env env in
      let (evd,c)  = Constrintern.interp_open_constr env evd c in
      let name = new_id () in
      let _ = Lib.add_leaf name (register_obj (EConstr.to_constr evd c)) in
      ()

  end

(** Each type-class gives rise to a different table.
    They only differ on how projections are extracted.  *)
module InjElt  =
  struct
    type elt = {
        isid : bool ; (* S = T ->  inj = fun x -> x*)
        source : EConstr.t; (* S *)
        target : EConstr.t; (* T *)
        (* projections *)
        inj  : EConstr.t ; (* S -> T *)
        pred : EConstr.t ; (* T -> Prop *)
        cstr :  EConstr.t option; (* forall x, pred (inj x) *)
      }

    let name = "InjTyp"

    let mk_elt evd i (a:EConstr.t array) =
      let isid = EConstr.eq_constr evd a.(0) a.(1) in
      {
        isid   = isid;
        source = a.(0);
        target = a.(1);
        inj    =  a.(2) ;
        pred   = a.(3);
        cstr   = if isid then None else Some a.(4)
      }

    let get_key = 0

  end

module EBinOp=
  struct
    type elt =
      { (* Op : source1 -> source2 -> source3 *)
        source1   : EConstr.t;
        source2   : EConstr.t;
        source3   : EConstr.t;
        target    : EConstr.t;
        inj1      : EConstr.t; (* InjTyp source1 target *)
        inj2      : EConstr.t; (* InjTyp source2 target *)
        inj3      : EConstr.t; (* InjTyp source3 target *)
        tbop      : EConstr.t; (* TBOpInj *)
      }

    let name = "BinOp"

    let mk_elt evd i a =
      {
        source1   = a.(0);
        source2   = a.(1);
        source3   = a.(2);
        target    = a.(3);
        inj1      = a.(5);
        inj2      = a.(6);
        inj3      = a.(7);
        tbop      = a.(9);
      }
    let get_key = 4
  end

module ECstOp=
  struct
    type elt =
      {
        source : EConstr.t;
        target : EConstr.t;
        inj    : EConstr.t;
      }

    let name = "CstOp"

    let mk_elt evd i a =
      {
        source = a.(0);
        target = a.(1);
        inj    = a.(3);
      }
    let get_key = 2
  end



module EBinRel=
  struct
    type elt =
      {
        source : EConstr.t;
        target : EConstr.t;
        inj    : EConstr.t;
        brel   : EConstr.t;
      }

    let name = "BinRel"

    let mk_elt evd i a =
      {
        source = a.(0);
        target = a.(1);
        inj    = a.(3);
        brel   = a.(4);
      }
    let get_key = 2
  end



module EUnOp=
  struct
    type elt =
      {
        source1   : EConstr.t;
        source2   : EConstr.t;
        target    : EConstr.t;
        inj1_t    : EConstr.t;
        inj2_t    : EConstr.t;
        unop : EConstr.t;
      }

    let name = "UnOp"

    let mk_elt evd i a = {
        source1 = a.(0);
        source2 = a.(1);
        target  = a.(2);
        inj1_t  = a.(4);
        inj2_t  = a.(5);
        unop    = a.(6)
      }

    let get_key = 3
  end
open EUnOp

module EPropOp=
  struct
    type elt = EConstr.t

    let name = "PropOp"
    let mk_elt evd i a = i
    let get_key = 0
  end

module ESat=
  struct
    type elt = {
        parg1 : EConstr.t;
        parg2 : EConstr.t;
        satOK : EConstr.t
      }

    let name = "Saturate"

    let mk_elt evd i a = {
        parg1 = a.(2);
        parg2 = a.(3);
        satOK = a.(5)
      }

    let get_key = 1
  end

module InjTable  = MakeTable(InjElt)
module BinOp     = MakeTable(EBinOp)
module UnOp      = MakeTable(EUnOp)
module CstOp     = MakeTable(ECstOp)
module BinRel    = MakeTable(EBinRel)
module PropOp    = MakeTable(EPropOp)
module Saturate  = MakeTable(ESat)

(** The module [Spec] is used to register
    the instances of [BinOpSpec], [UnOpSpec].
    They are not indexed and stored in a list. *)

module Spec =
  struct
    let table  = Summary.ref ~name:"zify_Spec" []

    let new_id =
      let id = ref 0 in
      fun () ->
      incr id ;
      Names.Id.of_string ("Spec_"^(string_of_int !id))



    let register_obj : Constr.constr ->  Libobject.obj  =
      let cache_constr (_,c) =   table := (EConstr.of_constr c)::!table
      in
           let subst_constr (subst,c) = Mod_subst.subst_mps subst c in

      (Libobject.declare_object @@ Libobject.superglobal_object_nodischarge
                                     ("register-zify-Spec")
                                     ~cache:cache_constr
                                     ~subst:(Some subst_constr) )



    let register c =
      let env = Global.env () in
      let evd = Evd.from_env env in
      let (_,c)  = Constrintern.interp_open_constr env evd c in
      let name = new_id () in
      let _ = Lib.add_leaf name (register_obj (EConstr.to_constr evd c)) in
      ()

    let get () = !table

  end


let unfold_decl evd =
  let f cst acc =  cst::acc in
  let acc = InjTable.fold_declared_const f evd [] in
  let acc = BinOp.fold_declared_const f evd acc in
  let acc = UnOp.fold_declared_const f evd acc in
  let acc = CstOp.fold_declared_const f evd acc in
  let acc = BinRel.fold_declared_const f evd acc in
  let acc = PropOp.fold_declared_const f evd acc in
  acc

open InjElt

(** Get constr of lemma and projections in ZifyClasses. *)

let zify str =
  EConstr.of_constr (UnivGen.constr_of_monomorphic_global (Coqlib.lib_ref ("ZifyClasses."^str)))

let locate_const str =
  let rf = "ZifyClasses."^str in
  match Coqlib.lib_ref rf with
  | GlobRef.ConstRef c -> c
  |  _         -> CErrors.anomaly Pp.(str rf ++ str " should be a constant")


(* The following [constr] are necessary for constructing the proof terms *)
let mkapp2     = lazy (zify "mkapp2")
let mkapp      = lazy (zify "mkapp")
let mkapp0     = lazy (zify "mkapp0")
let mkdp       = lazy (zify "mkinjterm")
let eq_refl    = lazy (zify "eq_refl")
let mkrel      = lazy (zify "mkrel")
let mkprop_op  = lazy (zify "mkprop_op")
let mkuprop_op = lazy (zify "mkuprop_op")
let mkdpP      = lazy (zify "mkinjprop")
let iff_refl   = lazy (zify "iff_refl")
let q          = lazy (zify "target_prop")
let p          = lazy (zify "source_prop")
let ieq        = lazy (zify "injprop_ok")
let iff        = lazy (zify "iff")

(* A super-set of the previous are needed to unfold the generated proof terms. *)

let to_unfold = lazy (List.map locate_const
                        ["source_prop";"target_prop";"uop_iff";"op_iff";"mkuprop_op";"TUOp";"inj_ok";
                         "TRInj"; "inj";"source";"injprop_ok";"TR";"TBOp";
                         "TCst" ; "target";"mkrel"; "mkapp2" ; "mkapp" ; "mkapp0";"mkprop_op"])


(** Module [CstrTable] records terms  [x] injected into [inj x]
    together with the corresponding type constraint.
    The terms are stored by side-effect during the traversal
    of the goal. It must therefore be cleared before calling
    the main tactic.
 *)



module CstrTable =
  struct
    module HConstr = Hashtbl.Make(
                         struct
                           type t = EConstr.t

                           (*                           let compare c c' = Constr.compare (unsafe_to_constr c) (unsafe_to_constr c')*)

                           let  hash c = Constr.hash (unsafe_to_constr c)

                           let  equal c c' = Constr.equal (unsafe_to_constr c) (unsafe_to_constr c')
                         end)


    let table : EConstr.t HConstr.t =  HConstr.create 10

    let clear  =
      Proofview.Goal.enter  begin fun gl ->
        HConstr.clear table ; Tacticals.New.tclIDTAC
        end

    let register evd t (i:EConstr.t) =
      HConstr.replace table  t  i

    let get () =
      let l =  HConstr.fold (fun k i acc -> (k,i)::acc) table [] in
      HConstr.clear table ; l

    (** [gen_cstr table] asserts (cstr k) for each element of the table (k,cstr).
        NB: the constraint is only asserted if it does not already exist in the context.
     *)
    let gen_cstr table  =
      Proofview.Goal.enter begin fun gl ->
        let evd = Tacmach.New.project gl in

        (* Build the table of existing hypotheses *)
        let has_hyp =
          let hyps_table = HConstr.create 20 in
          List.iter (fun (_,(t:EConstr.types)) -> HConstr.replace hyps_table  t ()) (Tacmach.New.pf_hyps_types gl);
          fun c ->
          HConstr.mem hyps_table c in

        (* Add the constraint (cstr k) if it is not already present *)
        let gen k cstr =
            Proofview.Goal.enter begin fun gl ->
              let env   = Tacmach.New.pf_env gl  in
              let term =  EConstr.mkApp(cstr,[| k|]) in
              let types = get_type_of env evd  term in
              if has_hyp  types
              then Tacticals.New.tclIDTAC
              else
                let n = Tactics.fresh_id_in_env Id.Set.empty (Names.Id.of_string "cstr") env in
                Tactics.pose_proof (Names.Name n)  term
              end
          in
            (List.fold_left (fun acc (k,i)  -> Tacticals.New.tclTHEN (gen k i) acc) Tacticals.New.tclIDTAC table )
          end

  end


let mkvar red evd inj v =
  begin
    if not red then
      match inj.cstr with
      | None -> ()
      | Some ctr -> CstrTable.register evd v  ctr
  end;
  let iv = EConstr.mkApp(inj.inj,[| v|]) in
  let iv = if red then Tacred.compute (Global.env ()) evd iv else iv in
  EConstr.mkApp(force mkdp, [|inj.source; inj.target; inj.inj; v; iv ; EConstr.mkApp(force eq_refl,[|inj.target ; iv|])|])



type texpr =
  | Var of InjElt.elt * EConstr.t
  (** Var is a term that cannot be injected further *)

  | Constant of InjElt.elt * EConstr.t
  (** Constant is a term that is solely built from constructors *)

  | Injterm of EConstr.t
(** Injected is an injected term represented by a  term of type [injterm] *)

let is_construct = function
  | Constant _ -> true
  | _          -> false

let constr_of_texpr = function
  | Constant(i,e) | Var(i,e) -> if i.isid then Some e else None
  |  _  -> None


let inj_term_of_texpr evd = function
  | Injterm e -> e
  | Var (inj,e) -> mkvar false evd inj e
  | Constant(inj,e) -> mkvar true evd inj e

let mkapp2_id evd
      i (* InjTyp S3 T *)
      inj (* deriv i *)
      t (* S1 -> S2 -> S3 *)
      b (* Binop S1 S2 S3 t ... *)
      dbop (* deriv b *) e1 e2 =
  let default () =
    let e1' = inj_term_of_texpr evd e1 in
    let e2' = inj_term_of_texpr evd e2 in
    EBinOp.(Injterm (EConstr.mkApp(force mkapp2,
                           [| dbop.source1 ;
                              dbop.source2;
                              dbop.source3 ;
                              dbop.target ;
                              t ;
                              dbop.inj1 ; dbop.inj2 ; dbop.inj3  ; b ; e1' ; e2'|]))) in
  if not (inj.isid)
  then default ()
  else
    match e1 , e2 with
    | Constant(_,e1) , Constant(_,e2)
      | Var(_,e1) , Var(_,e2)
      | Constant(_,e1) , Var(_,e2)
      | Var(_,e1) ,Constant(_,e2) -> Var(inj,EConstr.mkApp(t,[|e1;e2|]))
    | _ , _    -> default ()

let mkapp_id evd i inj (unop,u) f e1 =
  if EConstr.eq_constr evd u.unop f
  then (* Injection does nothing *)
    match e1 with
    | Constant(_,e) | Var(_,e) -> Var(inj,EConstr.mkApp(f,[|e|]))
    | Injterm e1 ->
       Injterm(EConstr.mkApp(force mkapp,[| u.source1 ; u.source2 ; u.target ; f; u.inj1_t; u.inj2_t; unop; e1|]))
  else
    begin
      let e1 = inj_term_of_texpr evd e1 in
      Injterm(EConstr.mkApp(force mkapp,[| u.source1 ; u.source2 ; u.target ; f; u.inj1_t; u.inj2_t; unop; e1|]))
    end


type typed_constr = { constr : EConstr.t ; typ : EConstr.t }

type op =
  | Unop  of  {unop : EConstr.t ; (* unop : typ unop_arg -> unop_typ *)
               unop_typ :  EConstr.t ;
               unop_arg : typed_constr}
  | Binop of  {binop : EConstr.t ; (* binop : typ binop_arg1 -> typ binop_arg2 -> binop_typ *)
               binop_typ :  EConstr.t ;
               binop_arg1 : typed_constr ; binop_arg2 : typed_constr}
  | Other

let pp_typed_constr env evd {constr; typ}=
  Pp.(str "("++pr_constr env evd constr ++ str " : " ++ pr_constr env evd typ++str ")")

let pp_op env evd = function
  | Unop {unop;unop_typ;unop_arg} ->
     Pp.(str "Unop"++(pr_constr env evd unop) ++ pp_typed_constr env evd unop_arg ++ str " : " ++ pr_constr env evd unop_typ)
  | Binop {binop;binop_typ;binop_arg1;binop_arg2} ->
     Pp.(str "Binop"++(pr_constr env evd binop) ++ pp_typed_constr env evd binop_arg1 ++ pp_typed_constr env evd binop_arg2 ++
           str " : " ++ pr_constr env evd binop_typ)
  | Other -> Pp.str "Other"


let rec trans_expr env evd e =

  if debug
  then
    Feedback.msg_debug  (Pp.str "Term "++ pp_typed_constr env evd e);

  (* Get the injection *)
  let {decl = i; deriv = inj} = InjTable.get evd e.typ in

  let e = e.constr in

  if EConstr.isConstruct evd e
  then Constant (inj,e) (* Evaluate later *)
  else
    try
      (* The term [e] might be a registered constant *)
        let {decl = c} = CstOp.get  evd e in
        Injterm (EConstr.mkApp(force mkapp0, [| inj.source ; inj.target; e ; i ; c|]))
    with Not_found ->
          (* Let decompose the term *)
          match  EConstr.kind evd e with
          | App(t,a) ->
             begin
               try
                 match Array.length a with
                 | 1 ->
                    let {decl = unop ; deriv = u} = UnOp.get evd t in
                    let a' = trans_expr env evd {constr = a.(0) ; typ = u.source1}  in
                    if is_construct a' && EConstr.isConstruct evd t
                    then Constant(inj,e)
                    else mkapp_id evd i inj (unop,u) t a'
                 | 2 ->
                    let {decl = bop ; deriv = b} = BinOp.get evd t in
                    let a0 = trans_expr env evd {constr = a.(0) ; typ = b.EBinOp.source1}  in
                    let a1 = trans_expr env evd {constr = a.(1) ; typ = b.EBinOp.source2} in
                    if is_construct a0 && is_construct a1 && EConstr.isConstruct evd t
                    then Constant(inj,e)
                    else  mkapp2_id evd i inj t bop b a0 a1
                 | _ -> Var (inj, e)
               with Not_found -> Var (inj, e)
             end
          | _  -> Var (inj,e)

let trans_expr env evd e =
  try
    trans_expr env evd e
  with Not_found -> raise (CErrors.user_err  (Pp.str "Missing injection for type "++ Printer.pr_leconstr_env env evd e.typ))





let get_rel env evd e =
  let is_prop env evd p =
    let ty = get_type_of env evd p in
    Constr.is_Prop (unsafe_to_constr ty) in
  let is_arrow a p1 p2 =
    (* cheap *)
    match a.Context.binder_name with
    | Names.Anonymous -> is_prop env evd p1 && is_prop env evd p2
    | _               ->
       is_prop env evd p1 && is_prop env evd p2 &&
         EConstr.Vars.noccurn evd 1 p2 in

  match EConstr.kind evd e with
  | Prod(a,p1,p2) when (is_arrow a p1 p2) ->
     begin
       (* X -> Y becomes (fun x y => x -> y) x y *)
        let name x = Context.make_annot (Name.mk_name (Names.Id.of_string x)) Sorts.Relevant in
        let arrow  =  (EConstr.mkLambda (name "x",EConstr.mkProp,
                           EConstr.mkLambda (name "y",EConstr.mkProp,
                                             EConstr.mkProd(
                                                 Context.make_annot Names.Anonymous Sorts.Relevant,
                                                 EConstr.mkRel 2, EConstr.mkRel 2)))) in
        Binop { binop = arrow ;
                binop_typ = EConstr.mkProp;
                binop_arg1 = {constr=  p1; typ= EConstr.mkProp};
                binop_arg2 = {constr=  p2; typ= EConstr.mkProp}
          }
     end
  | App(c,a) ->
     begin
     let len = Array.length a in
     if len >= 2
     then
       let (c,a1,a2) = if len = 2
                       then  (c,a.(0),a.(1))
                       else if len > 2
                       then  (EConstr.mkApp(c,Array.sub a 0 (len - 2)),a.(len-2),a.(len-1))
                       else raise Not_found in
       let typ = reduce_term evd (get_type_of env evd c) in
       match is_binary_arrow evd typ with
       | None -> raise Not_found
       | Some (t1,t2,t3) ->
          Binop {binop = c ; binop_typ = t3 ;
                 binop_arg1 = {constr= a1; typ= t1};
                 binop_arg2 = {constr= a2 ; typ= t2}}
     else if len = 1
     then
       let typ = reduce_term evd (get_type_of env evd c) in
       match is_unary_arrow evd typ with
       | None -> raise Not_found
       | Some (t1,t2)  ->
          Unop {unop = c ;
                unop_typ = t2 ;
                unop_arg = {constr = a.(0) ; typ = t1}}
     else raise Not_found
     end
  |   _   -> raise Not_found


let get_rel env evd e =
  try Some (get_rel env evd e)
  with Not_found -> None

let get_rel env evd e =
  if not debug then get_rel env evd e
  else
    begin
      let res = get_rel env evd e in
      Feedback.msg_debug
        (match res with
         | None -> Pp.(str "get_rel " ++ (pr_constr env evd e) ++ str " = None")
         | Some r -> Pp.(str "get_rel " ++ (pr_constr env evd e) ++ str " = " ++ pp_op env evd r)
        )
      ; res
    end



type tprop =
  | TProp of EConstr.t
  (** Transformed proposition *)

  | IProp of EConstr.t
  (** Identical proposition *)


let mk_iprop e = EConstr.mkApp(force mkdpP,[|e;e; EConstr.mkApp(force iff_refl,[|e|])|])

let inj_prop_of_tprop = function
  | TProp p -> p
  | IProp e -> mk_iprop e


let rec trans_prop env evd e =
  match get_rel env evd e with
  | None -> IProp e
  | Some (Binop {binop = r; binop_typ = t1 ; binop_arg1 = a1; binop_arg2 = a2}) ->
     begin
       assert (EConstr.eq_constr evd EConstr.mkProp t1);
       if EConstr.eq_constr evd a1.typ a2.typ
       then
         (* Arguments have the same type *)
         if
           EConstr.eq_constr evd EConstr.mkProp t1     &&
             EConstr.eq_constr evd EConstr.mkProp a1.typ
         then (* Prop -> Prop -> Prop *)
           try
             let {decl = rop} = PropOp.get evd r in
             let t1 = trans_prop env evd a1.constr in
             let t2 = trans_prop env evd a2.constr in
             match t1 , t2 with
             | IProp _ , IProp _ -> IProp e
         |    _    ,    _    ->
               let t1 = inj_prop_of_tprop t1 in
               let t2 = inj_prop_of_tprop t2 in
               TProp (EConstr.mkApp(force mkprop_op, [|r; rop; t1; t2|]))
         with Not_found -> IProp e
         else (* A -> A -> Prop *)
       try
         let {decl = br ; deriv = rop} = BinRel.get evd r in
         let a1 = trans_expr env evd  a1 in
         let a2 = trans_expr env evd  a2 in
         if EConstr.eq_constr evd r rop.EBinRel.brel
         then match  constr_of_texpr a1 , constr_of_texpr a2 with
              | Some e1, Some e2 -> IProp(EConstr.mkApp(r,[|e1;e2|]))
              |   _ , _   ->
                   let a1 = inj_term_of_texpr evd a1 in
                   let a2 = inj_term_of_texpr evd a2 in
                   TProp (EConstr.mkApp(force mkrel,[|rop.EBinRel.source;rop.EBinRel.target;r;rop.EBinRel.inj;br;a1;a2|]))
         else      let a1 = inj_term_of_texpr evd a1 in
                   let a2 = inj_term_of_texpr evd a2 in
                   TProp (EConstr.mkApp(force mkrel,[|rop.EBinRel.source;rop.EBinRel.target;r;rop.EBinRel.inj;br;a1;a2|]))
       with Not_found ->
             IProp e
       else IProp e
     end
  | Some (Unop {unop ; unop_typ ; unop_arg}) ->
     begin
       if EConstr.eq_constr evd EConstr.mkProp unop_typ &&
            EConstr.eq_constr evd EConstr.mkProp unop_arg.typ
     then
       try
         let {decl = rop} = PropOp.get evd unop in
         let t1 = trans_prop env evd unop_arg.constr in
         match t1 with
         | IProp _  -> IProp e
         |    _     ->
               let t1 = inj_prop_of_tprop t1 in
               TProp (EConstr.mkApp(force mkuprop_op, [|unop; rop; t1|]))
       with Not_found -> IProp e
     else
             IProp e
     end
  | _ -> IProp e


let trans_prop env evd e =
  let res = trans_prop env evd e in
  if debug
  then begin
      match res with
      | IProp _  -> Feedback.msg_debug Pp.(str "\ntrans_prop IProp" ++  (pr_constr env evd  e))
      | TProp e' -> Feedback.msg_debug Pp.(str "\ntrans_prop " ++ (pr_constr env evd  e)
                                           ++ str "TProp " ++  (pr_constr env evd  e'))
    end;
  res



let unfold n env evd  c =
  let cbv l = CClosure.RedFlags.(
      Tacred.cbv_norm_flags (mkflags (fBETA::fMATCH::fFIX::fCOFIX::fZETA:: (List.map fCONST l))))  in

  let unfold_decl = unfold_decl evd in
  (* Unfold the let binding *)
  let c = match n with
    | None -> c
    | Some n -> Tacred.unfoldn  [(Locus.AllOccurrences,Names.EvalVarRef n) ] env evd c in
  (* Reduce the term *)
  let c = cbv (force to_unfold @ unfold_decl) env evd c in
  c


let trans_check_prop env evd t =
  if Constr.is_Prop (unsafe_to_constr (get_type_of env evd t))
  then
    (*let t = Tacred.unfoldn [Locus.AllOccurrences, Names.EvalConstRef coq_not] env evd t in*)
    match trans_prop env evd t with
    | IProp e -> None
    | TProp e -> Some e
  else None

let trans_hyps env evd l  =
  List.fold_left (fun acc (h,p)  ->
      match trans_check_prop env evd p with
      | None -> acc
      | Some p' -> (h,p,p') :: acc) [] (List.rev l)


(* Only used if a direct rewrite fails *)
let trans_hyp  h t =
  Tactics.(Tacticals.New.(
  Proofview.Goal.enter  begin fun gl ->
    let env   = Tacmach.New.pf_env gl  in
    let n = fresh_id_in_env Id.Set.empty (Names.Id.of_string "__zify") env in
    let h' = fresh_id_in_env Id.Set.empty h env in
    tclTHENLIST
      [
        letin_tac None (Names.Name n) t None  Locus.{onhyps = None ; concl_occs = NoOccurrences} ;
        assert_by (Name.Name h') (EConstr.mkApp(force q,[|EConstr.mkVar  n|]))
          (tclTHEN (Equality.rewriteRL (EConstr.mkApp(force ieq,[|EConstr.mkVar n|])))
             (exact_check (EConstr.mkVar h)));
        reduct_in_hyp ~check:true ~reorder:false (unfold (Some n) ) (h',Locus.InHyp);
        clear [n] ;
        (* [clear H] may fail if [h] has dependencies *)
        tclTRY (clear [h]);
      ]
    end
  ))



let is_progress_rewrite evd t rew =
  match EConstr.kind evd rew with
  | App(c,[|lhs;rhs|]) ->
     if EConstr.eq_constr evd (force iff) c
                          (* too strong: some reduction may occur && (EConstr.eq_constr evd t lhs) *)
     then (* This is a successful rewriting *)
       not (EConstr.eq_constr evd lhs rhs)
     else
       CErrors.anomaly Pp.(str "is_progress_rewrite: not a rewrite" ++ pr_constr (Global.env ()) evd rew)
  |  _   -> failwith "is_progress_rewrite: not even an application"


let trans_hyp  h t0 t =
  (Tacticals.New.(
  Proofview.Goal.enter  begin fun gl ->
    let env   = Tacmach.New.pf_env gl  in
    let evd   = Tacmach.New.project gl in
    let t' = unfold None env evd (EConstr.mkApp(force ieq,[| t|])) in
    if debug then Feedback.msg_debug Pp.(str "trans_hyp : "++ Printer.pr_leconstr_env env evd t');
    if is_progress_rewrite  evd t0 (get_type_of env evd t')
    then
    tclFIRST
      [
        (Equality.general_rewrite_in true Locus.AllOccurrences true false h t' false);
        trans_hyp h t
      ]
    else tclIDTAC
    end
  ))


let trans_concl t =
  (Tacticals.New.(
  Proofview.Goal.enter  begin fun gl ->
    let concl = Tacmach.New.pf_concl gl in
    let env   = Tacmach.New.pf_env gl  in
    let evd   = Tacmach.New.project gl in
    let t' = unfold None env evd (EConstr.mkApp(force ieq,[| t|])) in
    if debug then Feedback.msg_debug Pp.(str "trans_concl : "++ Printer.pr_leconstr_env env evd t');
    if is_progress_rewrite  evd concl (get_type_of env evd t')
    then
        (Equality.general_rewrite true Locus.AllOccurrences true false t')
    else tclIDTAC
    end
  ))



let tclTHENOpt e tac tac' =
  match e with
  | None -> tac'
  | Some e' -> Tacticals.New.tclTHEN (tac e') tac'


let zify_tac =
  Proofview.Goal.enter  begin fun gl ->
    Coqlib.check_required_library ["Coq";"zify";"ZifyClasses"];
    Coqlib.check_required_library ["Coq";"zify";"ZifyInst"];

    let evd = Tacmach.New.project gl in
    let env   = Tacmach.New.pf_env gl  in
    let concl = trans_check_prop env evd (Tacmach.New.pf_concl gl) in
    let hyps  = trans_hyps env evd (Tacmach.New.pf_hyps_types gl) in
    let l     = CstrTable.get () in

    tclTHENOpt concl trans_concl
      (Tacticals.New.tclTHEN
         (Tacticals.New.tclTHENLIST (List.map (fun (h,p,t) -> trans_hyp h p t) hyps))
         (CstrTable.gen_cstr l))
    end


let iter_hyps tac =
  Proofview.Goal.enter  begin fun gl ->
    let hyps = List.rev (Tacmach.New.pf_hyps_types gl) in
    Tacticals.New.tclTHENLIST
          (List.map (fun (h,t) -> Tacticals.New.tclTRY (tac  h t)) hyps)
    end


let iter_specs tac =
  Tacticals.New.tclTHENLIST
    (List.fold_right (fun d acc -> (tac d)::acc) (Spec.get ())  [])

let find_hyp evd t l =
  try
    Some (fst (List.find (fun (h,t') -> EConstr.eq_constr evd t t') l))
  with Not_found -> None

let sat_constr c d =
  Proofview.Goal.enter begin fun gl ->
    let evd  = Tacmach.New.project gl in
    let env  = Tacmach.New.pf_env gl  in
    let hyps = Tacmach.New.pf_hyps_types gl in

    match EConstr.kind evd c with
    | App(c,args) ->
       if Array.length args = 2
       then
         let h1 = Tacred.cbv_beta env evd (EConstr.mkApp(d.ESat.parg1,[|args.(0)|])) in
         let h2 = Tacred.cbv_beta env evd (EConstr.mkApp(d.ESat.parg2,[|args.(1)|])) in
         if debug then Feedback.msg_debug Pp.(str "Looking for " ++ (Printer.pr_constr_env (Tacmach.New.pf_env gl) evd (EConstr.to_constr evd h1)));
         match find_hyp evd h1 hyps , find_hyp evd h2 hyps with
         | Some h1 , Some h2 ->
            let n = Tactics.fresh_id_in_env Id.Set.empty (Names.Id.of_string "__sat") env in
            let trm = EConstr.mkApp(d.ESat.satOK,[|args.(0); args.(1);EConstr.mkVar h1; EConstr.mkVar h2|]) in
           if debug then Feedback.msg_debug (Pp.str "Lemma " ++ (Printer.pr_constr_env env evd (EConstr.to_constr evd trm))) ;
            Tactics.pose_proof (Names.Name n) trm
         |   _     ,   _     -> Tacticals.New.tclIDTAC
       else Tacticals.New.tclIDTAC
    |  _  -> Tacticals.New.tclIDTAC
    end

let saturate  =
  Proofview.Goal.enter begin fun gl ->
    let table = CstrTable.HConstr.create 20 in

    let concl = Tacmach.New.pf_concl gl in
    let hyps  = Tacmach.New.pf_hyps_types gl in
    let evd   = Tacmach.New.project gl in

    let rec sat t  =
      match EConstr.kind evd t with
      | App(c,args) ->
       sat c ;  Array.iter sat args ;
       if Array.length args = 2
       then
         let ds = Saturate.get_all evd c in
         if ds = [] then ()
         else
           begin
             if debug then Feedback.msg_debug Pp.(str "saturate " ++ (Printer.pr_constr_env (Tacmach.New.pf_env gl) evd (EConstr.to_constr evd t)));
             List.iter (fun x -> CstrTable.HConstr.add table t x.deriv) ds
           end
       else ()
      | Prod(a,t1,t2) when a.Context.binder_name = Names.Anonymous ->
         sat t1 ; sat t2
    |  _  -> () in

    (* Collect all the potential saturation lemma *)
    sat concl ; List.iter (fun (_,t) -> sat t) hyps ;
    Tacticals.New.tclTHENLIST (CstrTable.HConstr.fold (fun c d acc -> (sat_constr c d)::acc) table [] )
    end

let print_zify_types () =
  Feedback.msg_notice  (InjTable.pp_keys ())

let print_zify_binop () =
  Feedback.msg_notice  (BinOp.pp_keys ())

let print_zify_unop () =
  Feedback.msg_notice  (UnOp.pp_keys ())

let print_zify_cst () =
  Feedback.msg_notice  (CstOp.pp_keys ())

let print_zify_binrel () =
  Feedback.msg_notice  (BinRel.pp_keys ())

let print_zify_spec  () =
  let env = Global.env () in
  let evd = Evd.from_env env in
  let constr_of_spec c =
    let t = get_type_of env evd c in
    match EConstr.kind evd t with
    | App(intyp,args) -> pr_constr env evd args.(2)
    |  _              -> Pp.str "" in

  let l = List.fold_left (fun acc c -> Pp.(constr_of_spec c ++ str " " ++ acc)) (Pp.str "") !Spec.table in
  Feedback.msg_notice l
