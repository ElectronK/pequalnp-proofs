import PEqualNP.Defs

namespace NestedFanoTree
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
-- The leaf accounting follows the snoc argument of L_meta_7111, specialized to natural-number leaf counts.
private def leafAt (T : List ℕ) (i : ℕ) : ℕ :=
  T[i]?.getD 0

private def leafSum (T : List ℕ) (R : List ℕ) : ℕ :=
  (R.map (leafAt T)).sum

private lemma leafSum_append (T : List ℕ) (R S : List ℕ) :
    leafSum T (R ++ S) = leafSum T R + leafSum T S := by
  simp [leafSum]

private lemma leafSum_old (T : List ℕ) (F : ℕ)
    (R : List ℕ) (h : ∀ i ∈ R, i < T.length) :
    leafSum (T ++ [F]) R = leafSum T R := by
  unfold leafSum
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [leafAt, List.getElem?_append_left (h i hi)]

private lemma leafAt_last (T : List ℕ) (F : ℕ) :
    leafAt (T ++ [F]) T.length = F := by
  simp [leafAt]

private lemma snocBudget {n : ℕ} (gs : List Gate) (g : Gate)
    (T : List ℕ) (F : ℕ) (a b : ℕ)
    (len : T.length = n + gs.length) (inputs : g.inputs = [a,b])
    (oldA : a < T.length) (oldB : b < T.length)
    (newLeaves : F = leafAt T a + leafAt T b)
    (earlier : ∀ R : List ℕ,
      ((R ++ gs.flatMap Gate.inputs).filter (fun i => decide (n ≤ i))).Nodup →
      (∀ r ∈ R, r < T.length) → leafSum T R ≤ R.length + gs.length) :
    ∀ R : List ℕ,
      ((R ++ (gs ++ [g]).flatMap Gate.inputs).filter (fun i => decide (n ≤ i))).Nodup →
      (∀ r ∈ R, r < (T ++ [F]).length) →
      leafSum (T ++ [F]) R ≤ R.length + (gs ++ [g]).length := by
  intro R unique valid
  let p := fun i : ℕ => decide (n ≤ i)
  let prev := (gs.flatMap Gate.inputs).filter p
  let pair := ([a,b] : List ℕ).filter p
  have packed : (R.filter p ++ (prev ++ pair)).Nodup := by
    simpa only [p, prev, pair, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, inputs, List.filter_append] using unique
  by_cases hR : T.length ∈ R
  · obtain ⟨L, S, rfl⟩ := List.append_of_mem hR
    have pop : p T.length = true := by simp [p, len]
    have packSplit : (L.filter p ++ T.length :: (S.filter p ++ (prev ++ pair))).Nodup := by
      simpa only [List.filter_append, List.filter_cons, pop, ite_true, List.append_assoc, List.cons_append] using packed
    have htail := (List.nodup_append.mp packSplit).2.1
    have noLeft : T.length ∉ L := by
      intro h
      have disjoint := (List.nodup_append.mp packSplit).2.2
      exact disjoint _ (List.mem_filter.mpr ⟨h,pop⟩) _ (by simp) rfl
    have noRight : T.length ∉ S := by
      intro h
      have miss := (List.nodup_cons.mp htail).1
      exact miss (List.mem_append_left _ (List.mem_filter.mpr ⟨h,pop⟩))
    have validL : ∀ i ∈ L, i < T.length := by
      intro i hi
      have inR : i ∈ L ++ T.length :: S := List.mem_append_left _ hi
      have bound := valid i inR
      have different : i ≠ T.length := fun he => noLeft (he ▸ hi)
      simp at bound
      omega
    have validS : ∀ i ∈ S, i < T.length := by
      intro i hi
      have inR : i ∈ L ++ T.length :: S := List.mem_append_right _
        (List.mem_cons_of_mem _ hi)
      have bound := valid i inR
      have different : i ≠ T.length := fun he => noRight (he ▸ hi)
      simp at bound
      omega
    let R' := (L ++ S) ++ [a,b]
    have deleted : ((L.filter p ++ S.filter p) ++ (prev ++ pair)).Nodup := by
      rw [List.append_assoc]
      exact ((List.sublist_cons_self _ _).append_left _).nodup packSplit
    have swapped : ((L.filter p ++ S.filter p) ++ (pair ++ prev)).Nodup :=
      (List.Perm.append_left _ List.perm_append_comm).nodup_iff.mp deleted
    have earlierNodup : ((R' ++ gs.flatMap Gate.inputs).filter p).Nodup := by
      simpa only [R', prev, pair, List.filter_append, List.append_assoc] using swapped
    have earlierValid : ∀ i ∈ R', i < T.length := by
      intro i hi
      simp only [R', List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with (h | h) | rfl | rfl
      · exact validL i h
      · exact validS i h
      · exact oldA
      · exact oldB
    have earlierBound := earlier R' earlierNodup earlierValid
    have comparison : leafSum (T ++ [F]) (L ++ T.length :: S) = leafSum T R' := by
      rw [leafSum_append, leafSum_old _ _ _ validL]
      have one : (T.length :: S) = [T.length] ++ S := rfl
      rw [one, leafSum_append, leafSum_old _ _ _ validS]
      simp only [R', leafSum_append]
      have hsingle : leafSum (T ++ [F]) [T.length] = F := by
        simpa [leafSum] using leafAt_last T F
      rw [hsingle, newLeaves]
      simp [leafSum]
      omega
    rw [comparison]
    simp only [R', List.length_append, List.length_cons, List.length_nil] at earlierBound ⊢
    omega
  · have validOld : ∀ i ∈ R, i < T.length := by
      intro i hi
      have bound := valid i hi
      have different : i ≠ T.length := fun he => hR (he ▸ hi)
      simp at bound
      omega
    have simpler : ((R ++ gs.flatMap Gate.inputs).filter p).Nodup := by
      have initialPart : ((R.filter p ++ prev) ++ pair).Nodup := by
        simpa only [List.append_assoc] using packed
      simpa only [prev, List.filter_append] using (List.nodup_append.mp initialPart).1
    rw [leafSum_old _ _ _ validOld]
    have bound := earlier R simpler validOld
    simp
    omega


def leafStep (w : List ℕ) (g : Gate) := w ++ [(g.inputs.map fun i => w.getD i 0).sum]
def counts (n : ℕ) (gs : List Gate) := gs.foldl leafStep (List.replicate n 1)

def shaped (n : ℕ) (gs : List Gate) := ∀ j g, gs[j]?=some g →
    ∃ a b, g.inputs=[a,b] ∧ a<n+j ∧ b<n+j

theorem queryBudget (n : ℕ) (gs : List Gate) (ok : shaped n gs) :
    (counts n gs).length=n+gs.length ∧ ∀ R : List ℕ,
      ((R ++ gs.flatMap Gate.inputs).filter (fun i => decide (n ≤ i))).Nodup →
      (∀ w ∈ R,w < (counts n gs).length) → leafSum (counts n gs) R ≤ R.length+gs.length := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨by simp [counts],?_⟩
    intro R _ valid
    have ones (w) (hw : w ∈ R) : leafAt (counts n []) w = 1 := by
      have lt : w<n := by simpa [counts] using valid w hw
      simp [leafAt,counts,lt]
    have all := List.map_congr_left ones
    simp [leafSum,all]
  | append_singleton gs g ih =>
    have early : shaped n gs := by
      intro j h atj
      have bound := (List.getElem?_eq_some_iff.mp atj).choose
      apply ok j h
      rwa [List.getElem?_append_left bound]
    obtain ⟨len,prev⟩ := ih early
    have lookup : (gs++[g])[gs.length]?=some g := by simp
    obtain ⟨a,b,inputs,ha,hb⟩ := ok gs.length g lookup
    let T := counts n gs
    let F := (g.inputs.map (fun i => T.getD i 0)).sum
    have foldEq : counts n (gs++[g]) = T++[F] := by simp [T,F,counts,List.foldl_append,leafStep]
    refine ⟨?_,?_⟩
    · rw [foldEq]
      change T.length=n+gs.length at len
      simp [len,Nat.add_assoc]
    · rw [foldEq]
      apply snocBudget gs g T F a b len inputs (by simpa [T,len] using ha) (by simpa [T,len] using hb) _ prev
      simp [F,inputs,leafAt,List.getD_eq_getElem?_getD]

theorem noSharing (C : Circuit) (ao : IsAO2 14 C)
    (tree : ((C.output :: C.gates.flatMap Gate.inputs).filter (fun i => decide (14 ≤ i))).Nodup) :
    (counts 14 C.gates).getD C.output 0 ≤ C.size+1 := by
  have shape : shaped 14 C.gates := by
    intro j g atj
    have lt := (List.getElem?_eq_some_iff.mp atj).choose
    have mem := List.mem_of_getElem? atj
    obtain ⟨a,b,inp⟩ := List.length_eq_two.mp (ao.2.2 g mem)
    have eq : gateAt C j = g := by
      change C.gates.getD j _ = g
      rw [List.getD_eq_getElem _ _ lt]
      exact (List.getElem?_eq_some_iff.mp atj).choose_spec
    exact ⟨a,b,inp,ao.2.1 j lt a (by simp [eq,inp]),ao.2.1 j lt b (by simp [eq,inp])⟩
  obtain ⟨len,budget⟩ := queryBudget 14 C.gates shape
  by_cases lt : C.output<(counts 14 C.gates).length
  · have b := budget [C.output] tree (by simpa using lt)
    simpa [leafSum,leafAt,List.getD_eq_getElem?_getD,Circuit.size,Nat.add_comm] using b
  · rw [List.getD_eq_default _ _ (by omega)]
    omega

end NestedFanoTree
