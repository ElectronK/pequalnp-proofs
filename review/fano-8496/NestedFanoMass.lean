import NestedFanoLive

namespace NestedFano.Mass
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover NestedFanoDepth NestedFano.Live

def leaves (C : Circuit) (w : ℕ) := (NestedFanoTree.counts 14 C.gates).getD w 0
def weight (C : Circuit) (w : ℕ) := leaves C w - 1
def base (C : Circuit) := List.ofFn (fun j : Fin C.gates.length => 14+j.val)

theorem rawLeaves (C : Circuit) (w : ℕ) (hw : w<14) : leaves C w=1 := by
  change (C.gates.foldl (stepR (fun _ ns => ns.sum) 0) (List.replicate 14 1)).getD w 0=1
  rw [R_getD_lt _ _ _ _ w (by simpa using hw)]
  exact List.getD_replicate 1 hw

theorem gateLeaves (C : Circuit) (ao : IsAO2 14 C) (j : Fin C.gates.length) :
    leaves C (14+j.val)=((C.gates[j.val]).inputs.map (leaves C)).sum := by
  have h := R_getD_gate (fun (_ : Gate) (ns : List ℕ) => ns.sum) 0 C.gates (List.replicate 14 1) j.val j.isLt
  simp only [List.length_replicate] at h
  change leaves C (14+j.val)=
    ((C.gates[j.val]).inputs.map (fun i=>if i<14+j.val then leaves C i else 0)).sum at h
  rw [h]
  congr 1
  apply List.map_congr_left
  intro i mem
  have hh : i<14+j.val := ao.2.1 j.val j.isLt i (by rwa [gateAt_eq j.isLt])
  simp [hh]

theorem positive (C : Circuit) (ao : IsAO2 14 C) (w : ℕ) (hw : w<14+C.gates.length) :
    1≤leaves C w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases raw : w<14
    · rw [rawLeaves _ _ raw]
    let j : Fin C.gates.length := ⟨w-14,by omega⟩
    have eq : 14+j.val=w := by dsimp [j]; omega
    obtain ⟨a,b,row,ha,hb⟩ := operands C ao j.val j.isLt
    rw [gateAt_eq j.isLt] at row
    have x := ih a (eq ▸ ha) (by omega)
    rw [←eq,gateLeaves C ao j,row]
    simp; omega

theorem gateWeight (C : Circuit) (ao : IsAO2 14 C) (j : Fin C.gates.length) :
    weight C (14+j.val)=((C.gates[j.val]).inputs.map (weight C)).sum+1 := by
  obtain ⟨a,b,row,ha,hb⟩ := operands C ao j.val j.isLt
  rw [gateAt_eq j.isLt] at row
  have x := positive C ao a (by omega)
  have y := positive C ao b (by omega)
  simp [weight,gateLeaves C ao j,row]
  omega

theorem weightNonzero (C : Circuit) (ao : IsAO2 14 C) (w : ℕ) (lo : 14≤w) (hi : w<14+C.gates.length) :
    1≤weight C w := by
  let j : Fin C.gates.length := ⟨w-14,by omega⟩
  have eq : 14+j.val=w := by dsimp [j];omega
  rw [←eq,gateWeight C ao j]; omega

theorem unitPrimitive (C : Circuit) (ao : IsAO2 14 C) (j : Fin C.gates.length)
    (unit : weight C (14+j.val)=1) : ∀ i∈(gateAt C j.val).inputs,i<14 := by
  rw [gateWeight C ao j] at unit
  obtain ⟨a,b,row,ha,hb⟩ := operands C ao j.val j.isLt
  have row' : (C.gates[j.val]).inputs=[a,b] := gateAt_eq j.isLt ▸ row
  simp [row'] at unit
  intro i hi
  replace hi : i=a ∨ i=b := by simpa [row] using hi
  rcases hi with rfl|rfl
  · by_contra! large; have := weightNonzero C ao i large (by omega);omega
  · by_contra! large; have := weightNonzero C ao i large (by omega);omega

theorem inputMass (f : ℕ→ℕ) (gs : List Gate) :
    (gs.map (fun g=>(g.inputs.map f).sum)).sum=((gs.flatMap Gate.inputs).map f).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [ih]

theorem mass (C : Circuit) (ao : IsAO2 14 C) :
    ((base C).map (weight C)).sum =
      ((C.gates.flatMap Gate.inputs).map (weight C)).sum+C.gates.length := by
  rw [base,←List.ofFn_comp',List.sum_ofFn]
  simp_rw [gateWeight C ao]
  rw [Finset.sum_add_distrib]
  have eq := List.ofFn_getElem_eq_map C.gates (fun g : Gate => (g.inputs.map (weight C)).sum)
  have val := congrArg List.sum eq
  rw [List.sum_ofFn,inputMass] at val
  simp [val]

theorem filterMass (C : Circuit) (items : List ℕ) :
    ((items.filter (fun i => decide (14 ≤ i))).map (weight C)).sum=(items.map (weight C)).sum := by
  induction items with
  | nil => rfl
  | cons i tail ih =>
    by_cases lo : 14 ≤ i
    · simp [lo,ih]
    · simp [lo,ih,weight,rawLeaves C i (by omega)]

theorem frontierMass (C : Circuit) (ao : IsAO2 14 C) :
    weight C C.output + ((base C).map (weight C)).sum =
      ((bag C).map (weight C)).sum + C.gates.length := by
  rw [bag,filterMass,mass C ao]
  simp; omega

theorem baseNodup (C : Circuit) : (base C).Nodup := by
  apply List.nodup_ofFn.mpr
  intro a b eq
  apply Fin.ext
  change 14+a.val=14+b.val at eq
  omega

theorem excessList (C : Circuit) (hm : Monotone2 C) (small : C.size≤27)
    (rows : ∀ k : Fin 58,C.eval (List.ofFn (boundary k))=decide (k.val<21)) :
    ∃ extra : List ℕ,(bag C).Perm (base C++extra) := by
  have sub : base C ⊆ bag C := by
    intro w hw
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hw
    exact used C hm small rows j
  obtain ⟨l,perm,inc⟩ := List.subperm_iff.mp (List.subperm_of_subset (baseNodup C) sub)
  obtain ⟨extra,split⟩ := inc.exists_perm_append
  exact ⟨extra,perm.symm.trans split⟩

theorem inBag (C : Circuit) (ao : IsAO2 14 C)
    (rows : ∀ k : Fin 58,C.eval (List.ofFn (boundary k))=decide (k.val<21))
    (w : ℕ) (hw : w∈bag C) : 14≤w ∧ w<14+C.gates.length := by
  have mem := List.mem_filter.mp hw
  refine ⟨of_decide_eq_true mem.2,?_⟩
  rcases List.mem_cons.mp mem.1 with eq|used
  · subst w
    by_contra! outside
    have pos := rows 0
    change (C.gates.foldl stepWire (List.ofFn (boundary 0))).getD C.output false=true at pos
    rw [List.getD_eq_default _ _ (by simpa [fold_length] using outside)] at pos
    contradiction
  · obtain ⟨g,hg,read⟩ := List.mem_flatMap.mp used
    obtain ⟨j,hj,atj⟩ := List.mem_iff_getElem.mp hg
    have lookup : gateAt C j=g := by rw [gateAt_eq hj,atj]
    have := ao.2.1 j hj w (lookup ▸ read)
    omega

theorem primitiveOrTree (C : Circuit) (ao : IsAO2 14 C) (small : C.size≤27)
    (rows : ∀ k : Fin 58,C.eval (List.ofFn (boundary k))=decide (k.val<21))
    (few : leaves C C.output≤29) :
    (bag C).Nodup ∨ ∃ j : Fin C.gates.length,
      (∀ w∈(gateAt C j.val).inputs,w<14) ∧ ((bag C).filter (fun w => w != 14+j.val)).Nodup := by
  have hm : Monotone2 C := fun g hg=>⟨ao.1 _ hg,(ao.2.2 _ hg).le⟩
  have lower := boundaryLower C hm rows
  obtain ⟨extra,perm⟩ := excessList C hm small rows
  have total := frontierMass C ao
  have eq := (perm.map (weight C)).sum_eq
  simp only [List.map_append,List.sum_append] at eq
  have leafSum : (extra.map (weight C)).sum≤1 := by
    change leaves C C.output-1 + _ = _ at total
    change 27≤C.gates.length at lower
    omega
  have pos (w) (hw : w∈extra) : 1≤weight C w := by
    have mem := perm.mem_iff.mpr (List.mem_append_right _ hw)
    have range := inBag C ao rows w mem
    exact weightNonzero C ao w range.1 range.2
  cases extra with
  | nil => exact Or.inl (perm.nodup_iff.mpr (by simpa using baseNodup C))
  | cons a rest =>
    cases rest with
    | nil =>
      have mem := perm.mem_iff.mpr (List.mem_append_right _ (List.mem_cons_self (a:=a) (l:=[])))
      have h := inBag C ao rows a mem
      let j : Fin C.gates.length := ⟨a-14,by omega⟩
      have ea : 14+j.val=a := by dsimp [j]; omega
      have za := pos a (by simp)
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at leafSum
      refine Or.inr ⟨j,unitPrimitive C ao j (ea ▸ (by omega : weight C a=1)),?_⟩
      have perm' := perm.filter (fun w => w != 14+j.val)
      apply perm'.nodup_iff.mpr
      simpa [ea] using ((baseNodup C).filter (fun w => w != a))
    | cons b rest =>
      have za := pos a (by simp)
      have zb := pos b (by simp)
      simp only [List.map_cons,List.sum_cons] at leafSum
      omega

end NestedFano.Mass

