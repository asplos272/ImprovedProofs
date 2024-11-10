(* ML \<open>
first_draft_fix_timeouts \<^theory> file_with_errors
\<close> *)
theory dofix
  imports  BaseProof.BasicInvariants
begin
declare [[ML_print_depth = 4000000]]
ML_file "~/Documents/GitHub/DeepIsaHOL/src/main/ml/pred.ML"
ML_file "~/Documents/GitHub/DeepIsaHOL/src/main/ml/ops.ML"
ML_file "~/Documents/GitHub/DeepIsaHOL/src/main/ml/get.ML"
ML_file "~/Documents/GitHub/DeepIsaHOL/src/main/ml/sections.ML"
ML_file "~/Documents/GitHub/DeepIsaHOL/src/main/ml/seps.ML"
ML_file "~/Documents/GitHub/DeepIsaHOL/src/main/ml/actions.ML"
ML_file "~/Documents/GitHub/DeepIsaHOL/src/main/ml/data.ML"
ML_file "~/Documents/GitHub/DeepIsaHOL/src/main/ml/print.ML"
ML_file "~/Documents/GitHub/betterProof/HammerAlt.ML"


ML \<open>
(*utility to write to a file with a unique name each time *)
fun print_string_op NONE = "NoID"
| print_string_op (SOME s) = s
fun writeFileln dirname content =
    let val fd = TextIO.openAppend (dirname ^ print_string_op (Position.id_of (Position.thread_data ())) ^ LargeInt.toString (Time.toMilliseconds (Time.now ())) ^ ".thy")
        val _ = TextIO.output (fd, String.concat [content, "\n"]) 
        val _ = writeln content
        val _ = TextIO.closeOut fd
    in () end;

fun log_fold_list _ _ [] = []
  | log_fold_list f s (x :: xs) = let val vs = f x s in vs @ log_fold_list f (List.last vs) xs end;
\<close>


ML \<open>
(*telling if a line is refining a goal*)
    fun is_refine_mssg ((_, txt), _) = Pred.contains "Failed to refine any pending goal" txt;
    fun is_refine (act, exn) = exists is_refine_mssg (Runtime.exn_messages exn)
      andalso (member (op =) ["have", "hence", "show", "thus"] (Actions.kind_of act));

(*telling if a line is a proof *)
    fun is_proof_error_msg ((_, txt), _) = Pred.contains "Failed to apply initial" txt orelse Pred.contains "Undefined fact" txt;
    fun is_proof (act, exn) = (Pred.contains "apply" (Actions.text_of act) orelse Pred.contains "by" (Actions.text_of act));(*exists is_proof_error_msg (Runtime.exn_messages exn)*)
   (*   andalso (Pred.contains "apply" (Actions.text_of act) orelse Pred.contains "by" (Actions.text_of act));*)
    fun is_timeout exn = (case exn of Timeout.TIMEOUT _ => true | _ => false);
    val might_timeout = Actions.on_kind (Pred.is "apply")
      andf Actions.on_text (Pred.contains "smt" orf Pred.contains "metis");

\<close>
ML \<open>
fun repair_sorrys stacts =
  let
    fun fix_using_sledgehammer st =
      let
        val thy = Toplevel.theory_of st;
        val (_, str2) = Hammer_Alt.hammer_away 1 (Toplevel.proof_of st);
        val sorry_fix = (if (Pred.contains "imed out" orf Pred.contains "No proof found") str2 then "sorry" else "")
        val actual_fix = (if sorry_fix = "" then (Hammer_Alt.extract_one_liner_proof (YXML.content_of str2)) else sorry_fix)
        val new_acts = Actions.make thy actual_fix;
        val _ = warning ("Adopted proof: " ^ actual_fix) (*Actions.text_of new_act)*)
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
       in (new_act, new_st, new_err) end

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
      in (new_act, new_st, new_err) end

    fun fix_using_sledgehammer st =
      let
        val thy = Toplevel.theory_of st;
        val (_, str2) = Hammer_Alt.hammer_away 1 (Toplevel.proof_of st);
        val sorry_fix = (if (Pred.contains "timed out" orf Pred.contains "No proof found") str2 then "sorry" else "")
        val actual_fix = "sorry" (*(if sorry_fix = "" then (Hammer_Alt.extract_one_liner_proof (YXML.content_of str2)) else sorry_fix)*)
        val new_act = Actions.make_one thy actual_fix;
        val _ = warning ("Adopted proof: " ^ Actions.text_of new_act)
        val (new_st, new_err) = Actions.apply_safe new_act st;
      in (new_act, new_st, new_err) end

    (* Handling incorrectly placed done's after Sledgehammer uses a by *)
    fun is_illegal_app_mssg ((_, txt), _) = Pred.contains "Illegal application of proof" txt;
    fun is_failed_finished_mssg ((_, txt), _) = Pred.contains "Failed to finish" txt;
    fun is_ill_app_done (act, exn) = exists (is_illegal_app_mssg orf is_failed_finished_mssg) (Runtime.exn_messages exn)
      andalso (Pred.is "done" (Actions.kind_of act))
    fun fix_ill_app_done st = let val _ = warning "fixing ill app done" in (Actions.void, st, NONE) end

    (* Handling non timed-out bad Sledgehammer proofs *)
    fun is_failed_mthd_mssg ((_, txt), _) = (Pred.contains "Failed to apply proof method" txt orelse Pred.contains "terminated abnormally" txt);
    fun is_failed_sledgeh (act, exn) = exists is_failed_mthd_mssg (Runtime.exn_messages exn)
      andalso Actions.on_text (Pred.contains "smt" orf Pred.contains "metis" orf Pred.contains "apply") act;

    (* Main body: combines all the handlings above *)

    fun do_next act' (_:Actions.T, st, _:(exn * string) option) =
      let val _ = () in
      if Toplevel.is_proof st
      then
        let
          val (st', err') = if might_timeout act' then
              (case Ops.apply_with_timeout timeout (Actions.apply_safe act') st of
                Exn.Exn exn => (st, SOME (exn, "TIMEOUT"))
                | Exn.Res res => res)
            else Actions.apply_safe act' st
          val (fixed_act', fixed_st', fixed_err') =
            (case err' of
              SOME (exn, _) =>
                if is_refine (act', exn) then fix_refine_goal st act'
                else if is_timeout exn then fix_using_sorry st
                else if is_failed_sledgeh (act', exn) then fix_using_sorry st
                else if is_ill_app_done (act', exn) then fix_ill_app_done st
                else (act', st', err')
              | NONE => (act', st', err'))
        in (fixed_act', fixed_st', fixed_err') end
      else let
        val (st', err') = Actions.apply_safe act' st
      in (act', st', err') end end
  in Ops.log_fold do_next (Actions.void, Toplevel.make_state NONE, NONE) acts end;

\<close>
ML \<open>
val test_file = "~/Documents/GitHub/betterProof/FixIMDData.thy"
val actions = Actions.make' \<^theory> (File.read (Path.explode test_file));

\<close>

ML \<open>
fun end_to_end_fix old_name new_name path = (let val actions = Actions.make' \<^theory> (File.read (Path.explode old_name));
    val fixed_trace = process_all {err_timeout_in_secs=45} actions;
    val perfect_trace = repair_sorrys fixed_trace
    val new_texts = Library.separate "\n" (map (fn (act, _, _) => Actions.text_of act) perfect_trace);
    val _ = Ops.create_file {force=true} path new_name (implode new_texts)
    in () end)




\<close>
ML \<open>

\<close>
(*
val new_texts = Library.separate "\n" (map (fn (act, _, _) => Actions.text_of act) fixed_trace)
val new_errors = filter (fn (_, _, err) => is_some err) fixed_trace
val new_texts = Library.separate "\n" (map (fn (act, _, _) => Actions.text_of act) fixed_trace)
Ops.create_file {force=true} "/Users/Chengsong/Documents/GitHub/betterProof/" "FixIMDDataNew.thy" (implode new_texts)

*)
ML \<open>
\<close>
(* WARNING: this creates a new file, the `force` parameter is to force an overwrite *)
ML \<open>

\<close>
(*val sorry_filled_in_trace = repair_sorrys  fixed_trace
val sorry_filled_in_text = Library.separate "\n" (map (fn (act, _, _) => Actions.text_of act) sorry_filled_in_trace)

Ops.create_file {force=true} "/Users/Chengsong/Documents/GitHub/betterProof/" "FixIMDDataFilled.thy" (implode new_texts)

*)


ML \<open>
fun repair_sorrys1 stacts  =
  let
    fun fix_using_sledgehammer st =
      let
        val thy = Toplevel.theory_of st;
        val (_, str2) = Hammer_Alt.hammer_away 1 (Toplevel.proof_of st);
        val sorry_fix = (if Pred.contains "imed out" str2 then "sorry" else "")
        val actual_fix = (if sorry_fix = "" then ( (YXML.content_of str2)) else sorry_fix)
        val new_act = Actions.make_one thy actual_fix;
        val _ = warning ("Adopted proof: " ^ Actions.text_of new_act)
        val (new_st, new_err) = Actions.apply_safe new_act st;
      in (new_act, new_st, new_err) end
    fun do_next (act', st', err') (_:Actions.T, st, _:(exn * string) option) =
      if Actions.on_kind (Pred.is "sorry") act'
      then fix_using_sledgehammer st
      else (act', st', err')
  in Ops.log_fold do_next (Actions.void, Toplevel.make_state NONE, NONE) stacts end;

fun end_to_end_fix1 old_name new_name path = (let val actions = Actions.make' \<^theory> (File.read (Path.explode old_name));
    val fixed_trace = process_all {err_timeout_in_secs=45} actions;
    val perfect_trace = repair_sorrys1 fixed_trace
    val new_texts = Library.separate "\n" (map (fn (act, _, _) => Actions.text_of act) perfect_trace);
    val _ = Ops.create_file {force=false} path new_name (implode new_texts)
    in () end)

\<close>
ML \<open>

\<close>

