
signature FIXER =
sig
  val log_fold_list: ('a -> 'b -> 'b list) -> 'b -> 'a list -> 'b list
  val repair_sorrys: (Actions.T * Toplevel.state * (exn * string) option) list 
    -> (Actions.T * Toplevel.state * (exn * string) option) list
  val process_all: {err_timeout_in_secs: int} -> Actions.T list 
    -> (Actions.T * Toplevel.state * (exn * string) option) list
  val fix_end_to_end: theory -> string -> string -> string -> unit
end;


structure Fixer: FIXER =
struct


fun log_fold_list _ _ [] = []
  | log_fold_list f s (x :: xs) = 
    let 
      val vs = f x s 
    in vs @ log_fold_list f (List.last vs) xs end;

fun repair_sorrys stacts =
  let
    fun fix_using_sledgehammer st =
      let
        val thy = Toplevel.theory_of st;
        val timeout = Time.fromSeconds 90;
        val timed_hammer = Ops.apply_with_timeout timeout (Hammer_Alt.hammer_away 1)
        val (_, str2) = (case timed_hammer (Toplevel.proof_of st) of
          Exn.Exn _ => ("timed out", "timed out")
          | Exn.Res res => res)
        val sorry_fix = (if (Pred.contains "imed out" orf Pred.contains "No proof found") str2 then "sorry" else "")
        val actual_fix = (if sorry_fix = "" then (Hammer_Alt.extract_one_liner_proof (YXML.content_of str2)) else sorry_fix)
        val new_acts = Actions.make thy actual_fix;
        val _ = warning ("Adopted proof: " ^ actual_fix)
        val act_st_err_list = Actions.apply_all new_acts st;
      in act_st_err_list end
    fun do_next (act', st', err') (_:Actions.T, st, _:(exn * string) option) =
      if Actions.on_kind (Pred.is "sorry") act'
      then fix_using_sledgehammer st
      else [(act', st', err')]
  in log_fold_list do_next (Actions.void, Toplevel.make_state NONE, NONE) stacts end;

fun process_all {err_timeout_in_secs=t} acts =
  let
    (* Handling "Failed to refine any pending goal" *)
    fun is_refine_mssg ((_, txt), _) = Pred.contains "Failed to refine any pending goal" txt;
    fun is_refine (act, exn) = exists is_refine_mssg (Runtime.exn_messages exn)
      andalso (member (op =) ["have", "hence", "show", "thus"] (Actions.kind_of act));
    fun fix_refine_goal st act' =
      let
        val thy = Toplevel.theory_of st;
        val ctxt = Toplevel.context_of st;
        val prf = Toplevel.proof_of st;
        val prf_goals = #goal (Proof.goal prf);
        val (objs, _) = Logic.strip_horn (Thm.prop_of prf_goals);
        val (new_act, new_st, new_err) = if null objs
          then (Actions.void, st, NONE)
          else let
            val nxt_goal = hd objs; (* ideally we would find the objective most similar
              to the original action, and not the head *)
            val goal_txt = Print.string_of_pretty (Syntax.pretty_term ctxt nxt_goal);
            val splitted = Pred.split (fn c => str c = "\"") (String.explode (Actions.text_of act'))
            val _ = if null splitted then Output.error_message "empty splitted" else ();
            val declaration =
              Pred.split (fn c => str c = "\"") (String.explode (Actions.text_of act'))
              |> hd |> String.implode;
            val new_act = Actions.make_one thy (declaration ^ " " ^ (enclose "\"" "\"" goal_txt));
            val _ = warning ("Fixed to " ^ Actions.text_of new_act)
            val (new_st, new_err) = Actions.apply_safe new_act st;
          in (new_act, new_st, new_err) end
       in [(new_act, new_st, new_err)] end

    (* Handling proof timeouts *)
    val timeout = Time.fromSeconds t
    val might_timeout = Actions.on_kind (Pred.is "apply")
      andf Actions.on_text (Pred.contains "smt" orf Pred.contains "metis" orf Pred.contains "simp");
    fun is_timeout exn = (case exn of Timeout.TIMEOUT _ => true | _ => false);
    fun fix_using_sorry st =
      let
        val thy = Toplevel.theory_of st;
        val new_act = Actions.make_one thy "sorry";
        val (new_st, new_err) = Actions.apply_safe new_act st;
      in [(new_act, new_st, new_err)] end

    (* Handling incorrectly placed done's after Sledgehammer uses a by *)
    fun is_illegal_app_mssg ((_, txt), _) = Pred.contains "Illegal application of proof" txt;
    fun is_failed_finished_mssg ((_, txt), _) = Pred.contains "Failed to finish" txt;
    fun is_ill_app_done (act, exn) = exists (is_illegal_app_mssg orf is_failed_finished_mssg) (Runtime.exn_messages exn)
      andalso (Pred.is "done" (Actions.kind_of act))
    fun fix_ill_app_done st = let val _ = warning "fixing ill app done" in [(Actions.void, st, NONE)] end

    (* Handling non timed-out bad Sledgehammer proofs *)
    fun is_failed_mthd_mssg ((_, txt), _) = (Pred.contains "Failed to apply proof method" txt 
      orelse Pred.contains "terminated abnormally" txt
      orelse Pred.contains "Undefined fact:" txt);
    fun is_failed_sledgeh (act, exn) = exists is_failed_mthd_mssg (Runtime.exn_messages exn)
      andalso Actions.on_text (Pred.contains "smt" orf Pred.contains "metis" orf Pred.contains "apply") act;

    (* Handling incomplete proofs calling qed *)
    fun is_failed_qed (act, exn) = exists (is_failed_finished_mssg) (Runtime.exn_messages exn)
      andalso (Pred.is "qed" (Actions.kind_of act))
    fun fix_incomplete_qed st =
      let
        val thy = Toplevel.theory_of st;
        val ctxt = Toplevel.context_of st;
        val prf = Toplevel.proof_of st;
        val prf_goals = #goal (Proof.goal prf);
        val (objs, _) = Logic.strip_horn (Thm.prop_of prf_goals);
        val result = if null objs
          then [(Actions.void, st, NONE)]
          else let
            fun txt_of goal = Print.string_of_pretty (Syntax.pretty_term ctxt goal);
            fun act_of goal = Actions.make_one thy ("show " ^ enclose "\"" "\"" (txt_of goal));
            val sorry_action = Actions.make_one thy ("sorry")
            val qed_action = Actions.make_one thy ("qed")
            val new_acts = (Library.separate sorry_action (map act_of objs)) @ [sorry_action, qed_action];
            val new_acts_text = implode (Library.separate "\n" (map Actions.text_of new_acts));
            val _ = writeln ("Adding missing actions:\n" ^ new_acts_text)
            val to_add = Actions.apply_all new_acts st;
          in to_add end
       in result end

    (* Main body: combines all the handlings above *)
    (* fun do_next act' (_:Actions.T, st, _:(exn * string) option) = *)
    fun do_next act' (_:Actions.T, st, _:(exn * string) option) =
      if Toplevel.is_proof st
      then
        let
          val (st', err') = if might_timeout act' then
              (case Ops.apply_with_timeout timeout (Actions.apply_safe act') st of
                Exn.Exn exn => (st, SOME (exn, "TIMEOUT"))
                | Exn.Res res => res)
            else Actions.apply_safe act' st
          val result =
            (case err' of
              SOME (exn, _) =>
                if is_refine (act', exn) then fix_refine_goal st act'
                else if is_timeout exn then fix_using_sorry st
                else if is_failed_sledgeh (act', exn) then fix_using_sorry st
                else if is_ill_app_done (act', exn) then fix_ill_app_done st
                else if is_failed_qed (act', exn) then fix_incomplete_qed st
                else [(act', st', err')]
              | NONE => [(act', st', err')])
        in result end
      else let
        val (st', err') = Actions.apply_safe act' st
      in [(act', st', err')] end
  in log_fold_list do_next (Actions.void, Toplevel.make_state NONE, NONE) acts end;

fun fix_end_to_end thy0 old_name new_name path =
  let 
    val actions = Actions.make' thy0 (File.read (Path.explode old_name));
    val fixed_trace = process_all {err_timeout_in_secs=45} actions;
    val perfect_trace = repair_sorrys fixed_trace
    val new_texts = Library.separate "\n" (map (fn (act, _, _) => Actions.text_of act) perfect_trace);
    val _ = Ops.create_file {force=true} path new_name (implode new_texts)
  in () end

end;
