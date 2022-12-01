Require Import Lia String Bool Logic.FunctionalExtensionality List.
Import ListNotations.
(* Open Scope string_scope. *)
Open Scope list_scope.

Definition nodes := list string.
Definition edges := list string.
Definition labels := list string.

(* Function that maps a given edge id to its source or target node *)
Definition r_map := string -> string.
Definition set_r (m: r_map) (eid: string) (nid: string) : r_map :=
  fun (eid': string) => if string_dec eid eid' then nid else m eid'.

(* Function that maps a given node id to a list of labels *) 
Definition l_map := string -> list string.
Definition set_lambda (m: l_map) (nid: string) (ls: labels) : l_map :=
  fun (nid': string) => if string_dec nid nid' then ls else m nid'.

(* Function for kappa that takes an id, a property key and outputs a value *)
Definition k_map := string -> string -> string.
Definition set_k (m: k_map) (id: string) (pk: string) (v: string) : k_map := 
  fun (id': string) => if (string_dec id id') 
      then fun (pk': string) => if (string_dec pk' pk) then v else m id' pk'
      else m id'.  

(* A graph is just a tuple of nodes, edges, src, dest, lambda, kappa, and tau *)
Definition graph := (nodes * edges * r_map * r_map * l_map * k_map * r_map ) % type.

Definition get_nodes (g: graph) : nodes := 
match g with
  | (n, e, src, dest, lambda, kappa, tau) => n
end.

Definition get_edges (g: graph) : edges := 
match g with
  | (n, e, src, dest, lambda, kappa, tau) => e
end.

Definition get_src (g: graph) : r_map := 
match g with
  | (n, e, src, dest, lambda, kappa, tau) => src
end.

Definition get_dest (g: graph) : r_map := 
match g with
  | (n, e, src, dest, lambda, kappa, tau) => dest
end.

Definition get_lambda (g: graph) : l_map := 
match g with
  | (n, e, src, dest, lambda, kappa, tau) => lambda
end.

Definition get_kappa (g: graph) : k_map := 
match g with
  | (n, e, src, dest, lambda, kappa, tau) => kappa
end.

Definition get_tau (g: graph) : r_map := 
match g with
  | (n, e, src, dest, lambda, kappa, tau) => tau
end.



(* Example graph *)
Open Scope string_scope.
Definition example_nodes : nodes := ["n1"; "n2"; "n3"; "n4"; "n5"].
Definition example_edges : edges := ["e1"; "e2"; "e3"; "e4"; "e5"].

Definition src_0 : r_map := fun _ => "".
Definition dest_0 : r_map := fun _ => "".
Definition kappa_0 : k_map := fun _ => fun _ => "".
Definition lambda_0 : l_map := fun _ => nil.
Definition tau_0 : r_map := fun _ => "".

Definition src_1 : r_map := set_r src_0 "e1" "n1".
Definition src_2 : r_map := set_r src_1 "e2" "n1".
Definition src_3 : r_map := set_r src_2 "e3" "n4".
Definition src_4 : r_map := set_r src_3 "e4" "n1".
Definition example_src : r_map := set_r src_4 "e5" "n1".

Definition dest_1 : r_map := set_r dest_0 "e1" "n2".
Definition dest_2 : r_map := set_r dest_1 "e2" "n3".
Definition dest_3 : r_map := set_r dest_2 "e3" "n2".
Definition dest_4 : r_map := set_r dest_3 "e4" "n4".
Definition example_dest : r_map := set_r dest_4 "e5" "n5".

Definition lambda_1 : l_map := set_lambda lambda_0 "n1" ["Professor"; "Person"].
Definition lambda_2 : l_map := set_lambda lambda_1 "n2" ["Class"].
Definition lambda_3 : l_map := set_lambda lambda_2 "n3" ["Class"].
Definition lambda_4 : l_map := set_lambda lambda_3 "n4" ["Student"; "Person"].
Definition example_lambda : l_map := set_lambda lambda_4 "n5" ["Student"; "Person"].

Definition tau_1 : r_map := set_r tau_0 "e1" "Teaches".
Definition tau_2 : r_map := set_r tau_1 "e2" "Teaches".
Definition tau_3 : r_map := set_r tau_2 "e3" "Enrolls in".
Definition tau_4 : r_map := set_r tau_3 "e4" "Knows".
Definition example_tau : r_map := set_r tau_4 "e5" "Knows".

Definition kappa_1 : k_map := set_k kappa_0 "n1" "name" "Edsger".
Definition kappa_2 : k_map := set_k kappa_1 "n2" "name" "James".
Definition kappa_3 : k_map := set_k kappa_2 "n3" "name" "Turing Award".
Definition kappa_4 : k_map := set_k kappa_3 "n4" "name" "PL".
Definition example_kappa : k_map := set_k kappa_4 "n4" "name" "Luwen".

Compute example_lambda "n1".
Compute example_lambda "n2".
Compute example_lambda "n3".
Compute example_lambda "n4".
Compute example_lambda "n5".
Compute example_kappa "n2" "name".
Compute example_src "e2".
Compute example_src "e5".

Definition example_graph : graph := (example_nodes, example_edges, example_src, example_dest, example_lambda, example_kappa, example_tau).

Example example_graph_example:
length example_nodes = 5 /\
example_src "e2" = "n1" /\
example_lambda "n1" = ["Professor"; "Person"] /\
example_tau "e5" = "Knows".
Proof. auto. Qed.

(* ========== tables ============= *)
(* Definition record (A: Type) := string -> A.  *)
Definition record := string -> string.

(* A table is just a list of records *)
Definition table := list (record).

Definition add_table_record (t: table) (r: record) : table := 
  cons r t.

(* ========= queries ============= *)

Inductive expr := 
| MATCH (s: string)
| INSERT (s: string)
| UPDATE (s: string)
| DELETE (s: string)
.

Inductive direction :=
| Left_To_Right (s: string)
| Right_To_Left (s: string)
| Undirected (s: string)
.

(* A node pattern (simplified) is a tuple of (name, a single label, and mapping). *)
Definition node_pat := (option string * option string * option k_map) % type.

(* An edge pattern is a tuple of (direction, name, type, and length) *)
Definition edge_pat := (direction * option string * option string * nat) % type.

(* A match query is a tuple of (node pattern, edge pattern) *)
Definition path_pattern := ( (option node_pat) * (option edge_pat)) % type.

(* look up a label in a list of labels *)
Fixpoint lookup_lambda (needle: string) (haystack: labels): bool :=
  match haystack with
    | nil => false 
    | a :: ls' => if string_dec a needle then true else lookup_lambda needle ls'
  end.

Fixpoint append_table_nodes (vertices: nodes) (kappa: k_map) (t: table) : table :=
  let new_record : record := fun _ => "" in 

  match vertices with 
  | nil => t
  | v :: v' => (set_r new_record "id" v) :: (append_table_nodes v' kappa t)
end.

Theorem append_table_nodes_sound: 
  forall (v: nodes) (kappa: k_map) (t: table), length (append_table_nodes v kappa t) = length t + length v.
Proof.
  intros.
  induction v.
  - auto.
  - simpl. rewrite IHv. auto.  
Qed.

Fixpoint append_table_edges (rels: edges) (kappa: k_map) (t: table) : table :=
  let new_record : record := fun _ => "" in 

  match rels with 
  | nil => t
  | r :: r' => (set_r new_record "id" r) :: (append_table_edges r' kappa t)
end.


Definition node_satisfies_node_pattern (node: string) (np: node_pat) (lambda: l_map) : bool := 
  match np with 
  | (Some name, Some label, _) => if lookup_lambda label (lambda node)
                                  then true else false
  (* | (Some name, Some label, Some pk_map) => false TODO *)
  (* | (Some name, None, Some pk_map) => false (* TODO *) *)
  (* This satisfies every node *)
  | (Some name, None, _) =>  true
  | (None, _, _) => true
end.

Definition edge_satisfies_edge_pattern (edge: string) (ep: edge_pat) (tau: r_map) : bool :=
  match ep with 
  | (_, _, Some type, l) => if string_dec (tau edge) type 
      then true else false
  | (_, _, None, l) => true
end.

Fixpoint filter_matching_nodes (np: node_pat) (vertices: nodes) (lambda: l_map) (result: nodes) : nodes :=
  match vertices with 
  | nil => []
  | v :: v' => if node_satisfies_node_pattern v np lambda
              then v :: (filter_matching_nodes np v' lambda result)
              else filter_matching_nodes np v' lambda result
end.

Fixpoint filter_matching_edges (ep: edge_pat) (rels: edges) (tau: r_map) (result: edges) : edges :=
  match rels with 
  | nil => []
  | r :: r' => if edge_satisfies_edge_pattern r ep tau 
            then r :: (filter_matching_edges ep r' tau result)
            else filter_matching_edges ep r' tau result
end.

(* For now, assume we want to return nodes nodes *)
Fixpoint filter_matching_both (np: node_pat) (ep: edge_pat) (vertices: nodes) (rels: edges) (src: r_map) (dest: r_map) (lambda: l_map) (tau: r_map) (result: nodes) :=
  match rels with 
  | [] => result
  | r :: r' => let nid_src := src r in 
    let nid_dest := dest r in 

    match ep with 
    (* If the edge goes -> then only match source nodes *)
    | (Left_To_Right d, _, type, _) => if (edge_satisfies_edge_pattern r ep tau) && (node_satisfies_node_pattern nid_src np lambda) 
        then nid_src :: (filter_matching_both np ep vertices r' src dest lambda tau result)
        else (filter_matching_both np ep vertices r' src dest lambda tau result)

    (* If the edge goes <- then only match target nodes *)
    | (Right_To_Left d, _, _, _) => if node_satisfies_node_pattern nid_dest np lambda 
        then nid_dest :: (filter_matching_both np ep vertices r' src dest lambda tau result)
        else (filter_matching_both np ep vertices r' src dest lambda tau result)

    (* If the edge goes <-> then match source and target nodes *)
    | (Undirected d, _, _, _) => if node_satisfies_node_pattern nid_src np lambda
        then nid_src :: (filter_matching_both np ep vertices r' src dest lambda tau result)
        else if node_satisfies_node_pattern nid_dest np lambda 
            then nid_dest :: (filter_matching_both np ep vertices r' src dest lambda tau result)
            else filter_matching_both np ep vertices r' src dest lambda tau result
    end
end.

Definition eval_match_pattern (pat: path_pattern) (return_name: string) (g: graph) (t: table) : table :=
  let '(vertices, rels, src, dest, lambda, kappa, tau) := g in 

  match pat with 
    (* Only node pattern, no edge pattern *)
    | (Some np, None) => append_table_nodes (filter_matching_nodes np vertices lambda []) kappa t

    (* Only edge pattern, no node pattern *)
    | (None, Some ep) => append_table_edges (filter_matching_edges ep rels tau []) kappa t 

    (* Both edge patterns and node patterns *)
    | (Some np, Some ep) => append_table_nodes (filter_matching_both np ep vertices rels src dest lambda tau []) kappa t 

    | (None, None) => t 
  end.


Theorem eval_match_pattern_empty_sound: 
  forall (pp: path_pattern) (return_name: string) (g: graph) (t: table), (length t = 0 /\ get_nodes g = nil /\ get_edges g = nil) -> length (eval_match_pattern pp return_name g t) = 0.
Proof.
  intros.
  destruct g.
  try repeat destruct p.
  destruct H. destruct H0. 
  unfold get_edges in H1. unfold get_nodes in H0.
  destruct pp as [np ep].
  unfold eval_match_pattern.
  destruct np. destruct ep.
  - rewrite H1. auto. 
  - rewrite H0. auto.
  - destruct ep. rewrite H1.
    + auto.
    + auto.
Qed.


(* forall (nid: string) (lambda: l_map) (g: graph), get_lambda g = lambda ->  *)

(* If a node with some labels is in the graph, then evaluating solely a node pattern with one of those labels returns a table that contains a record with the id of that node *)
Theorem eval_match_pattern_node_patterns_complete:
  forall (nid: string) (name: string) (label: string) (vertices: nodes) (rels: edges) (src: r_map) (dest: r_map) (lambda: l_map) (kappa: k_map) (tau: r_map) (g: graph) (return_name: string),
  g = (vertices, rels, src, dest, lambda, kappa, tau) ->
  In label (lambda nid)  -> In nid vertices ->  exists record', In record' (eval_match_pattern (Some (Some nid, Some label, Some kappa), None) return_name g []) /\ record' "id" = nid.
Proof.
  intros.
  destruct g.
  try repeat destruct p.
  simpl.
  unfold append_table_nodes.
  admit.
Admitted.

(* Definition set_k (m: k_map) (id: string) (pk: string) (v: string) : k_map := 
  fun (id': string) => if (string_dec id id') 
      then fun (pk': string) => if (string_dec pk' pk) then v else m id' pk'
      else m id'.   *)

Definition prop_pair := (string * string) % type.

Definition create_node (nid: string) (ls: option labels) (kv: option prop_pair) (g: graph) : graph := 
  let '(vertices, rels, src, dest, lambda, kappa, tau) := g in 
  let new_vertices : nodes := nid :: vertices in
  
  match ls with 
  | Some a => let new_lambda := set_lambda lambda nid a in
        match kv with 
        | Some (pk, pv) => let new_kappa := set_k kappa nid pk pv in 
                          (new_vertices, rels, src, dest, new_lambda, new_kappa, tau)
        | None => (new_vertices, rels, src, dest, new_lambda, kappa, tau)
        end
  | None => (new_vertices, rels, src, dest, lambda, kappa, tau)
end.

(* The create operation leaves edges and their corresponding mappings unchanged *)
Lemma create_nodes_pure: 
  forall (nid: string) (ls: option labels) (pp: option prop_pair) (g: graph) (g': graph), 
  g' = (create_node nid ls pp g) -> (get_edges g = get_edges g') /\ (get_src g = get_src g') /\ (get_dest g = get_dest g') /\ (get_tau g = get_tau g').
  
Proof.
  intros.
  destruct g.
  try repeat destruct p.
  rewrite H.
  try repeat split; unfold create_node; destruct ls; destruct pp; auto; destruct p; auto.
Qed.

(* The create operation actually "saves" labels into a new lambda mapping, and a property key-value pair into a new kappa mapping *)
Lemma create_nodes_complete:
  forall (nid: string) (ls: labels) (pp: prop_pair) (g: graph) (g': graph), 
  g' = (create_node nid (Some ls) (Some pp) g) -> (get_lambda g') nid = ls /\ (get_kappa g') nid (fst pp) = snd pp.
Proof.
  intros.
  destruct g.
  try repeat destruct p.
  unfold create_node in H.
  rewrite H.
  destruct pp.
  split; simpl.
  - unfold set_lambda.
    destruct (string_dec nid nid).
    * auto.
    * contradiction.
  - unfold set_k.
    destruct (string_dec nid nid).
    * destruct (string_dec s s).
      + auto.
      + contradiction.    
    * contradiction. 
Qed.


Fixpoint get_outgoing_edge_of_node (nid: string) (rels: edges) (src: r_map) : option string :=
  match rels with 
  | nil => None
  | r :: r' => if string_dec (src r) nid 
            then Some r
            else get_outgoing_edge_of_node nid r' src
  end.

Fixpoint get_incoming_edge_of_node (nid: string) (rels: edges) (dest: r_map) : option string :=
  match rels with 
  | nil => None
  | r :: r' => if string_dec (dest r) nid 
            then Some r
            else get_incoming_edge_of_node nid r' dest
  end.

Fixpoint remove_node (x : string) (haystack: nodes) : nodes :=
  match haystack with
    | [] =>  []
    | y::h' => if (string_dec x y) then remove_node x h' else y::(remove_node x h')
  end.

Fixpoint remove_edge (x : string) (haystack: edges) : edges :=
  match haystack with
    | [] =>  []
    | y::h' => if (string_dec x y) then remove_edge x h' else y::(remove_edge x h')
  end.

Definition delete_node (nid: string) (g: graph) : graph := 
  let '(vertices, rels, src, dest, lambda, kappa, tau) := g in 
  let incident_outgoing : string := (src nid) in 
  let incident_incoming : string := (dest nid) in 

  let new_vertices := remove_node nid vertices in 
  let new_lambda := set_lambda lambda nid nil in
  let new_kappa := set_k kappa nid "" "" in 

  match (incident_incoming, incident_outgoing) with 
  | ("", "") => (new_vertices, rels, src, dest, new_lambda, new_kappa, tau)
  | ("", e_o) => let new_edges := remove_edge e_o rels in 
                let new_tau := set_r tau e_o "" in 
                (new_vertices, new_edges, src, dest, new_lambda, new_kappa, new_tau)
  | (e_i, "") => let new_edges := remove_edge e_i rels in 
                let new_tau := set_r tau e_i "" in
                (new_vertices, new_edges, src, dest, new_lambda, new_kappa, new_tau)
  | (e_i, e_o) => let new_edges_1 := remove_edge e_i rels in 
                let new_edges_2 := remove_edge e_o new_edges_1 in 
                let new_tau_1 := set_r tau e_i "" in
                let new_tau_2 := set_r new_tau_1 e_o "" in
                (new_vertices, new_edges_2, src, dest, new_lambda, new_kappa, new_tau_2)
end.

(* This is only a partial proof since we did some simplification here: we skipped the checking of labels, property keys and edges. *)
Theorem delete_node_partial_complete:
  forall (nid: string) (g: graph) (g': graph), In nid (get_nodes g) -> delete_node nid g = g' -> not (In nid (get_nodes g')).
Proof.
  intros.
  (* rewrite H0. *)
  destruct g in H.
  try repeat destruct p.
  simpl in H.
  destruct g' in H.
  try repeat destruct p.
  simpl in H.
  unfold delete_node.
  destruct 
  rewrite <- H.
  simpl.
  auto.
  unfold delete_node in H.

(* running a match on nodes with no labels produces 5 rows in the table *)
Example eval_match_pattern_matches_all_nodes:
  let t : table := [] in 
  length (eval_match_pattern (Some (Some "n", None, None), None) % type "n" example_graph t) = 5.
Proof. auto. Qed.

(* running a match on edges produces 5 rows in the table *)
Example eval_match_pattern_matches_all_edges:
  let t : table := [] in 
  length (eval_match_pattern (None, Some (Undirected "", Some "e", None, 1)) % type "e" example_graph t) = 5.
Proof. simpl. auto. Qed.

(* running a match query on nodes with a label and incoming edges of type  *)
Example eval_match_pattern_matches_nodes_with_label_and_incoming_edges_of_type:
  let t : table := [] in 
  length (eval_match_pattern (Some (Some "n", Some "Person", None), Some (Left_To_Right "d", None, Some "Teaches", 1)) % type "n" example_graph t) = 2.
Proof. simpl. auto. Qed.

(* running a match query on both nodes and edges, but returning edges *)
Example eval_match_pattern_matches_nodes_edges_returns_edges:
  let t : table := [] in 
  length (eval_match_pattern (Some (None, Some "Person", None), Some (Left_To_Right "d", None, None, 1)) % type "e" example_graph t) = 3.
Proof. simpl. auto. Qed.


(* running a match with label "Person" (on the example graph) produces 3 rows in the table *)
Example eval_match_pattern_matches_on_node_label:
  let t : table := [] in 
  length (eval_match_pattern ( Some (Some "n", Some "Person", None), None) % type "n" example_graph t) = 3.
Proof. simpl. auto. Qed.


(* running a match query with nonexistent node labels produces 0 rows in the table *)
Example eval_match_pattern_nomatches_on_node_label:
  let t : table := [] in 
  length (eval_match_pattern (Some (Some "n", Some "Foo", None), None) % type "n" example_graph t) = 0.
Proof. auto. Qed.

(* running a match query on edges only  *)
Example eval_match_pattern_matches_edges:
  let t : table := [] in 
  length (eval_match_pattern (None, Some (Undirected "u", Some "e", Some "Enrolls in", 1)) % type "e" example_graph t) = 1.
Proof. simpl. auto. Qed.



