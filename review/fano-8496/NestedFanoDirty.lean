import NestedFanoDepth
import NestedFanoIrredundancy
import PEqualNP.Outside.L_meta_17415

namespace NestedFanoDirty
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open NestedFanoDepth

-- The mark-to-degree argument is adapted from R_meta_1967_529.
theorem degrees (D : Circuit) (ao : IsAO2 14 D) (k1 k2 : ℕ) (hCone12 : InCone 14 D k1 k2)
    (hk2Live : 14+k2=D.output ∨ InCone 14 D k2 (D.output-14))
    (lower : marked D k1 0 7) (upper : marked D k2 7 0) :
    2≤D.lineDeg 14 {0} ∧ 2≤D.lineDeg 14 {7} := by
  obtain ⟨hk1And,hk1_07,hk1_00⟩ := lower
  obtain ⟨hk2And,hk2_70,hk2_77⟩ := upper
  have transCone (u v : ℕ) (uv : InCone 14 D u v) : ∀ w, InCone 14 D v w → InCone 14 D u w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro vw
      obtain ⟨hw,z,mem,lo,hi,eq|old⟩ := (inCone_iff D v w).mp vw
      · exact (inCone_iff D u w).mpr ⟨hw,z,mem,lo,hi,Or.inr (eq ▸ uv)⟩
      · exact (inCone_iff D u w).mpr ⟨hw,z,mem,lo,hi,Or.inr (ih (z-14) (by omega) old)⟩
  have firstLive : 14+k1=D.output ∨ InCone 14 D k1 (D.output-14) := by
    rcases hk2Live with eq|con
    · right
      rw [←eq]
      simpa using hCone12
    · exact Or.inr (transCone _ _ hCone12 _ con)

  letI : DecidableEq GateOp := lineDegreeGateOpDecEq
  let weight (g : Gate) (d : List ℕ) := if g.op=.and then d.sum else d.foldr max 0
  let degree {n} (C : Circuit) (t : Fin n) (w : ℕ) := (C.lineDegrees n {t.val}).getD w 0
  let seeds {n} (t : Fin n) := (List.range n).map fun i => if i∈({t.val} : Finset ℕ) then 1 else 0

  have degInput {n} (C : Circuit) (t : Fin n) (w : ℕ) (hw : w<n) :
      degree C t w = if w=t.val then 1 else 0 := by
    change (C.gates.foldl (stepR weight 0) (seeds t)).getD w 0=_
    have len : (seeds t).length=n := by simp [seeds]
    rw [R_getD_lt _ _ _ _ w (by omega)]
    simp [seeds,List.getD_eq_getElem?_getD,hw]

  have degGate {n} (C : Circuit) (t : Fin n) {j a b : ℕ} (hj : j<C.gates.length)
      (row : (gateAt C j).inputs=[a,b]) (ha : a<n+j) (hb : b<n+j) :
      degree C t (n+j)=if (gateAt C j).op=.and then degree C t a+degree C t b else max (degree C t a) (degree C t b) := by
    have step := R_getD_gate weight 0 C.gates (seeds t) j hj
    have length : (seeds t).length=n := by simp [seeds]
    rw [length,← gateAt_eq hj,row] at step
    have read (w) : (C.gates.foldl (stepR weight 0) (seeds t)).getD w 0=degree C t w := rfl
    simp only [read] at step
    simpa [weight,ha,hb] using step

  have degChild {n} (C : Circuit) (ao : IsAO2 n C) (t : Fin n) {j a : ℕ}
      (hj : j<C.gates.length) (ha : a∈(gateAt C j).inputs) : degree C t a ≤ degree C t (n+j) := by
    obtain ⟨p,q,row,lp,lq⟩ := operands C ao j hj
    have one : a=p ∨ a=q := by simpa [row] using ha
    rw [degGate C t hj row lp lq]
    rcases one with rfl|rfl <;> split <;> omega


  have wireVal_input (C : Circuit) (x : Fin 14→Bool) (w : ℕ) (hw : w<14) :
      wireVal 14 C w x = x ⟨w,hw⟩ := valRaw C x hw
  have boolAt (x : Fin 14→Bool) {j a b : ℕ} (hj : j<D.gates.length)
      (eq : (gateAt D j).inputs=[a,b]) : wireVal 14 D (14+j) x =
      (gateAt D j).op.eval [wireVal 14 D a x,wireVal 14 D b x] := by
    apply valAt D x hj eq
    · exact ao.2.1 j hj a (by simp [eq])
    · exact ao.2.1 j hj b (by simp [eq])
  have countMark (s t : Fin 14) (j : ℕ) (hand : (gateAt D j).op=.and)
      (live : 14+j=D.output ∨ InCone 14 D j (D.output-14))
      (on : gateVal 14 D j (pairInput s t)=true)
      (off : ∀ i : Fin 2,wireVal 14 D (opnd D j i) (pairInput s s)=false) : 2≤D.lineDeg 14 {t.val} := by
    have hj : j<D.gates.length := by
      by_contra! bad
      change (D.gates.getD j _).op=.and at hand
      rw [List.getD_eq_default _ _ bad] at hand
      cases hand
    have sensitive (w : ℕ) (hw : w<14+D.gates.length) : degree D t w=0 →
        wireVal 14 D w (pairInput s t)=wireVal 14 D w (pairInput s s) := by
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro zero
        by_cases raw : w<14
        · rw [degInput D t w raw] at zero
          have ne : (⟨w,raw⟩ : Fin 14)≠t := by
            intro eq
            have h : w=t.val := congrArg Fin.val eq
            rw [if_pos h] at zero
            omega
          rw [wireVal_input D _ w raw,wireVal_input D _ w raw]
          change decide ((⟨w,raw⟩ : Fin 14)=s ∨ (⟨w,raw⟩ : Fin 14)=t)=decide ((⟨w,raw⟩ : Fin 14)=s ∨ (⟨w,raw⟩ : Fin 14)=s)
          simp [ne]
        obtain ⟨k,rfl⟩ : ∃ k,w=14+k := ⟨w-14,by omega⟩
        have hk : k<D.gates.length := by omega
        obtain ⟨a,b,ab,ha,hb⟩ := operands D ao k hk
        have da := degChild D ao t hk (a:=a) (by simp [ab])
        have db := degChild D ao t hk (a:=b) (by simp [ab])
        rw [boolAt _ hk ab,boolAt _ hk ab,ih a ha (by omega) (by omega),ih b hb (by omega) (by omega)]
    obtain ⟨a,b,ab,ha,hb⟩ := operands D ao j hj
    change wireVal 14 D (14+j) (pairInput s t)=true at on
    rw [boolAt _ hj ab,hand] at on
    have both : wireVal 14 D a (pairInput s t)=true ∧ wireVal 14 D b (pairInput s t)=true := by
      have evaluate : ∀ x y : Bool, GateOp.and.eval [x,y]=(x && y) := by decide +kernel
      simpa only [evaluate,Bool.and_eq_true] using on
    have needs (w : ℕ) (hw : w<14+j) (yes : wireVal 14 D w (pairInput s t)=true)
        (no : wireVal 14 D w (pairInput s s)=false) : 1≤degree D t w := by
      by_contra! small
      have eq := sensitive w (by omega) (by omega)
      rw [yes,no] at eq
      cases eq
    have fa := off 0
    have fb := off 1
    change wireVal 14 D ((gateAt D j).inputs.getD 0 0) (pairInput s s)=false at fa
    change wireVal 14 D ((gateAt D j).inputs.getD 1 0) (pairInput s s)=false at fb
    rw [ab] at fa fb
    have da := needs a ha both.1 fa
    have db := needs b hb both.2 fb
    have high : 2≤degree D t (14+j) := by
      rw [degGate D t hj ab ha hb,hand]
      simp only [ite_true]
      omega
    change 2≤degree D t D.output
    rcases live with eq|con
    · simpa [←eq] using high
    have path (k : ℕ) (jk : InCone 14 D j k) : degree D t (14+j)≤degree D t (14+k) := by
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        obtain ⟨hk,w,mem,lo,hi,eq|prev⟩ := (inCone_iff D j k).mp jk
        · have step := degChild D ao t hk mem
          have e : 14+j=w := by omega
          rwa [e]
        · have step := degChild D ao t hk mem
          have prior := ih (w-14) (by omega) prev
          have e : 14+(w-14)=w := by omega
          rw [e] at prior
          exact prior.trans step
    obtain ⟨_,w,_,lo,hi,_⟩ := (inCone_iff D j _).mp con
    have e : 14+(D.output-14)=D.output := by omega
    simpa only [e] using high.trans (path _ con)

  exact ⟨countMark 7 0 k2 hk2And hk2Live hk2_70 hk2_77,
      countMark 0 7 k1 hk1And firstLive hk1_07 hk1_00⟩

def clean (C : Circuit) : Prop :=
  ∀ j, PEqualNP.ReadTwo.isAnd C j → ∀ a b : Fin 14,
    gateVal 14 C j (pairInput a b)=true → C.eval (List.ofFn (pairInput a b)) = true

theorem cleanExcluded (C : Circuit) (small : C.size≤27) (ao : IsAO2 14 C)
    (distinct : ∀ j<C.size, (gateAt C j).inputs.Nodup)
    (rows : ∀ k : Fin 58, C.eval (List.ofFn (NestedFano.boundary k)) = decide (k.val<21))
    (good : clean C) (i j : ℕ) (inside : InCone 14 C i j)
    (live : 14+j=C.output ∨ InCone 14 C j (C.output-14))
    (lower : marked C i 0 7) (upper : marked C j 7 0) : False := by
  have monotone : Monotone2 C := fun g hg => ⟨ao.1 _ hg,(ao.2.2 _ hg).le⟩
  have full := (PEqualNP.Outside.L_meta_4647_aux.main (circuitFun 14 C)).mpr
    ⟨fun x y xy => Bool.le_iff_imp.mpr (NestedFano.circuit_mono monotone
      (fun v=>Bool.le_iff_imp.mp (xy v))),rows⟩
  have shape (j : ℕ) (g : Gate) (lookup : C.gates[j]?=some g) :
      (g.op=.and ∨ g.op=.or) ∧ ∃ a b,g.inputs=[a,b] ∧ a≠b ∧ a<14+j ∧ b<14+j := by
    have lt := (List.getElem?_eq_some_iff.mp lookup).choose
    have mem := List.mem_of_getElem? lookup
    have eg : gateAt C j=g := (gateAt_eq lt).trans (List.getElem?_eq_some_iff.mp lookup).choose_spec
    obtain ⟨a,b,row,ha,hb⟩ := operands C ao j lt
    have nd := distinct j lt
    rw [row] at nd
    exact ⟨ao.1 _ mem,a,b,eg ▸ row,by simpa using nd,ha,hb⟩
  have flag := PEqualNP.Outside.L_meta_17415 C ⟨small,shape,full⟩ good (0 : Fin 7) 0 (Or.inl rfl)
  change C.lineDeg 14 {0} ≤ 1 ∨ C.lineDeg 14 {7} ≤ 1 at flag
  have deg := degrees C ao i j inside live lower upper
  omega

end NestedFanoDirty
