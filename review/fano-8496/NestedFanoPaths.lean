import NestedFanoMass
import NestedFanoDirty

namespace NestedFano.Paths
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open NestedFanoDepth NestedFano.Live NestedFano.Mass

def seeds (t : Fin 14) := (List.range 14).map fun i => if i∈({t.val} : Finset ℕ) then 1 else 0
def occ (C : Circuit) (t : Fin 14) (w : ℕ) :=
  (C.gates.foldl (stepR (fun _ ns => ns.sum) 0) (seeds t)).getD w 0

theorem rawOcc (C : Circuit) (t : Fin 14) (w : ℕ) (hw : w<14) :
    occ C t w = if w=t.val then 1 else 0 := by
  unfold occ
  rw [R_getD_lt _ _ _ _ w (by simpa [seeds] using hw)]
  simp [seeds,List.getD_eq_getElem?_getD,hw]

theorem nodeOcc (C : Circuit) (ao : IsAO2 14 C) (t : Fin 14) (j : Fin C.gates.length) :
    occ C t (14+j.val)=((C.gates[j.val]).inputs.map (occ C t)).sum := by
  have h := R_getD_gate (fun (_ : Gate) (ns : List ℕ) => ns.sum) 0 C.gates (seeds t) j.val j.isLt
  have len : (seeds t).length=14 := by simp [seeds]
  rw [len] at h
  change occ C t (14+j.val)=
    ((C.gates[j.val]).inputs.map (fun i=>if i<14+j.val then occ C t i else 0)).sum at h
  rw [h]
  congr 1
  apply List.map_congr_left
  intro i mem
  have hh := ao.2.1 j.val j.isLt i (by rwa [gateAt_eq j.isLt])
  simp [hh]

theorem degree_le (C : Circuit) (ao : IsAO2 14 C) (t : Fin 14) (w : ℕ)
    (hw : w<14+C.gates.length) : (C.lineDegrees 14 {t.val}).getD w 0 ≤ occ C t w := by
  letI : DecidableEq GateOp := lineDegreeGateOpDecEq
  let D (g : Gate) (ns : List ℕ) := if g.op=.and then ns.sum else ns.foldr max 0
  let deg (i : ℕ) := (C.lineDegrees 14 {t.val}).getD i 0
  change deg w ≤ occ C t w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases raw : w<14
    · rw [rawOcc C t w raw]
      change (C.gates.foldl (stepR D 0) (seeds t)).getD w 0 ≤ _
      rw [R_getD_lt _ _ _ _ w (by simpa [seeds] using raw)]
      simp [seeds,List.getD_eq_getElem?_getD,raw]
    let j : Fin C.gates.length := ⟨w-14,by omega⟩
    have eq : 14+j.val=w := by dsimp [j];omega
    obtain ⟨a,b,row,ha,hb⟩ := operands C ao j.val j.isLt
    have dr := R_getD_gate D 0 C.gates (seeds t) j.val j.isLt
    have len : (seeds t).length=14 := by simp [seeds]
    rw [len,←gateAt_eq j.isLt,row] at dr
    have value (v) : (C.gates.foldl (stepR D 0) (seeds t)).getD v 0=deg v := rfl
    simp only [value] at dr
    have aa := ih a (eq ▸ ha) (by omega)
    have bb := ih b (eq ▸ hb) (by omega)
    rw [←eq,dr,nodeOcc C ao t j,←gateAt_eq j.isLt,row]
    simp [D,ha,hb]
    split <;> omega

def reads (C : Circuit) := C.output :: C.gates.flatMap Gate.inputs

theorem splitSum (C : Circuit) (t : Fin 14) (L : List ℕ) :
    (L.map (occ C t)).sum =
      ((L.filter (fun i => decide (14 ≤ i))).map (occ C t)).sum + L.count t.val := by
  induction L with
  | nil => simp
  | cons a rest ih =>
    by_cases lo : 14≤a
    · have ne : a≠t.val := by have := t.isLt; omega
      simp [lo,ne,Ne.symm ne,ih,List.count_cons]
      omega
    · have rwocc := rawOcc C t a (by omega)
      by_cases eq : a=t.val
      · subst a
        simp [lo,rwocc,ih,List.count_cons]
        omega
      · simp [lo,eq,Ne.symm eq,rwocc,ih,List.count_cons]

theorem conservation (C : Circuit) (ao : IsAO2 14 C) (t : Fin 14) :
    occ C t C.output+((base C).map (occ C t)).sum =
      ((bag C).map (occ C t)).sum+(reads C).count t.val := by
  have nodes : ((base C).map (occ C t)).sum =
      ((C.gates.flatMap Gate.inputs).map (occ C t)).sum := by
    rw [base,←List.ofFn_comp',List.sum_ofFn]
    simp_rw [nodeOcc C ao t]
    have eq := List.ofFn_getElem_eq_map C.gates (fun g : Gate => (g.inputs.map (occ C t)).sum)
    have val := congrArg List.sum eq
    rwa [List.sum_ofFn,inputMass] at val
  have h := splitSum C t (reads C)
  simpa only [reads,bag,List.map_cons,List.sum_cons,←nodes] using h

theorem splitInput (C : Circuit) (ao : IsAO2 14 C) (small : C.size≤27)
    (rows : ∀ k : Fin 58,C.eval (List.ofFn (boundary k))=decide (k.val<21))
    (t : Fin 14) (deg : 2≤C.lineDeg 14 {t.val}) :
    2≤(reads C).count t.val ∨ ∃ w,2≤(bag C).count w ∧ 0<occ C t w := by
  have hm : Monotone2 C := fun g hg=>⟨ao.1 _ hg,(ao.2.2 _ hg).le⟩
  obtain ⟨extra,p⟩ := excessList C hm small rows
  have live : C.output<14+C.gates.length := by
    by_contra! outside
    have pos := rows 0
    change (C.gates.foldl stepWire (List.ofFn (boundary 0))).getD C.output false=true at pos
    rw [List.getD_eq_default _ _ (by simpa [fold_length] using outside)] at pos
    contradiction
  have dl := degree_le C ao t C.output live
  change 2≤(C.lineDegrees 14 {t.val}).getD C.output 0 at deg
  have m := conservation C ao t
  have eq := (p.map (occ C t)).sum_eq
  simp only [List.map_append,List.sum_append] at eq
  by_contra! bad
  have zero (w) (hw : w∈extra) : occ C t w=0 := by
    have mem := p.mem_iff.mpr (List.mem_append_right _ hw)
    have interval := inBag C ao rows w mem
    have inbase : w∈base C := by
      apply List.mem_ofFn.mpr
      exact ⟨⟨w-14,by omega⟩,by dsimp;omega⟩
    have hi := List.count_pos_iff.mpr inbase
    have he := List.count_pos_iff.mpr hw
    have counts := p.count_eq w
    rw [List.count_append] at counts
    have z := bad.2 w (by omega)
    omega
  have van (L : List ℕ) (hL : ∀ x∈L,occ C t x=0) : (L.map (occ C t)).sum=0 := by
    induction L with
    | nil => rfl
    | cons x xs ih => simp [hL x (by simp),ih (fun y hy=>hL y (by simp [hy]))]
  have z := van extra zero
  omega

theorem bothSplit (C : Circuit) (ao : IsAO2 14 C) (small : C.size≤27)
    (rows : ∀ k : Fin 58,C.eval (List.ofFn (boundary k))=decide (k.val<21))
    (i j : ℕ) (inside : InCone 14 C i j)
    (live : 14+j=C.output ∨ InCone 14 C j (C.output-14))
    (low : marked C i 0 7) (high : marked C j 7 0) :
    ∀ t ∈ ([0,7] : List (Fin 14)), 2≤(reads C).count t.val ∨
      ∃ w,2≤(bag C).count w ∧ 0<occ C t w := by
  have d := NestedFanoDirty.degrees C ao i j inside live low high
  intro t ht
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl|rfl
  · exact splitInput C ao small rows 0 d.1
  · exact splitInput C ao small rows 7 d.2

end NestedFano.Paths

