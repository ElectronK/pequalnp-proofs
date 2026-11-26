import NestedFanoGeometry
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.Outside.L_meta_17808 NestedFanoDepth NestedFano.Geometry NestedFano

namespace NestedFano.CutChild

def physicalReaders (C : Circuit) (w : ℕ) :=
  (Finset.range C.size).filter (fun j => w ∈ (gateAt C j).inputs)

def eligible (C : Circuit) : Finset (Fin 14) :=
  Finset.univ.filter (fun t => (List.range (14+C.size)).any (fun w =>
    decide (2 ≤ (PEqualNP.TopForm.readers 0 C w).card) && wireVal 14 C w (fun v=>decide (v=t)))=true)

theorem reader_eq (C : Circuit) (ao : IsAO2 14 C) (w : ℕ) :
    readers (chartDag C) (mp14 w) = physicalReaders C w := by
  ext j
  simp only [PEqualNP.Outside.L_meta_17808.readers,physicalReaders,Finset.mem_filter,Finset.mem_range,length_chart,Circuit.size]
  by_cases hj : j<C.gates.length
  · obtain ⟨a,b,row,ha,hb⟩ := operands C ao j hj
    obtain ⟨aa,bb⟩ := operands_chart C hj row
    have eq (k : ℕ) : mp14 k=mp14 w ↔ w=k := by
      constructor
      · intro same
        simpa only [mp_involution] using (congrArg mp14 same).symm
      · rintro rfl;rfl
    simp [hj,aa,bb,row,eq]
  · simp [hj]

theorem perm_range (C : Circuit) (w : ℕ) : mp14 w<14+C.size ↔ w<14+C.size := by
  constructor
  · intro h
    simpa only [mp_involution] using lowers h
  · exact lowers

theorem singleton_trace (C : Circuit) (ao : IsAO2 14 C) (t : Fin 14) (w : ℕ) :
    pm14 t ∈ supp 14 (chartDag C) (mp14 w) ↔
      wireVal 14 C w (fun v=>decide (v=t))=true := by
  rw [mem_supp,chartVal C ao]
  have eq : (fun v=>single (pm14 t) (pm14 v)) = fun v=>decide (v=t) := by
    funext v
    unfold single
    by_cases h : v=t
    · subst v;simp
    · have ne : pm14 v≠pm14 t := fun z=>h (by simpa only [pm_involution] using congrArg pm14 z)
      simp [h,ne]
  rw [eq]
  rfl

theorem physical_mem (C : Circuit) (ao : IsAO2 14 C) (t : Fin 14) :
    pm14 t∈eligSet 14 (chartDag C) ↔ t∈eligible C := by
  simp only [eligSet,Finset.mem_biUnion,branchW,eligible,Finset.mem_filter,Finset.mem_range,
    Finset.mem_univ,true_and,length_chart,List.any_eq_true,List.mem_range,Bool.and_eq_true,decide_eq_true_eq]
  have pr (w : ℕ) : PEqualNP.TopForm.readers 0 C w=physicalReaders C w := by
    simp [PEqualNP.TopForm.readers,physicalReaders,Circuit.size]
  simp_rw [pr]
  constructor
  · rintro ⟨w,⟨hw,fan⟩,suppOn⟩
    have fw := reader_eq C ao (mp14 w)
    rw [mp_involution] at fw
    change 2≤(readers (chartDag C) w).card at fan
    refine ⟨mp14 w,(perm_range C w).mpr hw,fw ▸ fan,?_⟩
    apply (singleton_trace C ao t (mp14 w)).mp
    simpa only [mp_involution] using suppOn
  · rintro ⟨w,hw,fan,suppOn⟩
    refine ⟨mp14 w,⟨(perm_range C w).mpr hw,?_⟩,(singleton_trace C ao t w).mpr suppOn⟩
    change 2≤(readers (chartDag C) (mp14 w)).card
    rw [reader_eq C ao]
    exact fan

theorem card_eq (C : Circuit) (ao : IsAO2 14 C) :
    (eligSet 14 (chartDag C)).card=(eligible C).card := by
  let f : Fin 14 ≃ Fin 14 := ⟨pm14,pm14,pm_involution,pm_involution⟩
  have eq : (eligible C).map f.toEmbedding=eligSet 14 (chartDag C) := by
    ext v
    rw [Finset.mem_map]
    constructor
    · rintro ⟨t,mem,rfl⟩
      exact (physical_mem C ao t).mpr mem
    · intro h
      refine ⟨pm14 v,?_,pm_involution v⟩
      exact (physical_mem C ao (pm14 v)).mp (by simpa only [pm_involution] using h)
  rw [←eq,Finset.card_map]

theorem geometry :
    ∀ C : Circuit,
      let m := fun (j : ℕ) (v : Fin 14) =>
        (gateAt C j).op=.and ∧ gateVal 14 C j (pairInput 0 7)=true ∧
        ∀ r : Fin 2,wireVal 14 C (opnd C j r) (pairInput v v)=false
      C.size≤27 → IsAO2 14 C → (∀ j<C.size,(gateAt C j).inputs.Nodup) →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 7, (p=l ∨ p=l+1 ∨ p=l+3) ∧ x (Fin.castAdd 7 p)=true ∧ x (Fin.natAdd 7 l)=true) →
      ∀ i j, m i 0 → m j 7 → 9≤((Finset.univ : Finset (Fin 14)).filter (fun t =>
        (List.range (14+C.size)).any (fun w=>decide (2≤(PEqualNP.TopForm.readers 0 C w).card) &&
          wireVal 14 C w (fun v=>decide (v=t)))=true)).card := by
  intro C
  dsimp only
  intro small ao distinct full i j l h
  have pass : tests C := by
    intro k
    rw [Bool.eq_iff_iff,full,decide_eq_true_iff]
    exact PEqualNP.Outside.L_meta_4647_aux.T1 k
  have lo : marked C i 0 7 := l
  have hi : marked C j 7 0 := by
    refine ⟨h.1,?_,h.2.2⟩
    rw [show pairInput (7 : Fin 14) 0=pairInput (0 : Fin 14) 7 by funext a;simp [pairInput,or_comm]]
    exact h.2.1
  have nine := markedEligibilityNine C ao small pass distinct lo hi
  change 9≤(eligible C).card
  rwa [card_eq C ao] at nine

#print axioms geometry
end NestedFano.CutChild

