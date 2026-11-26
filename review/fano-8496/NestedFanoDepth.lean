import PEqualNP.Defs
namespace NestedFanoDepth
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.SingleLevel

-- List evaluation and cone recurrences from the checked R_meta_1967_529.
theorem cones_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (cs : List (List ℕ)),
    (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) cs).length = cs.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro cs; simp
  | cons g gs ih =>
    intro cs
    rw [List.foldl_cons, ih]
    dsimp only [PEqualNP.EdgeOwnership.coneStep]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
theorem cones_char : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (i j : ℕ),
    i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs,
        14 ≤ w ∧ w < 14 + j ∧
        (i = w - 14 ∨ i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []).getD (w - 14) []) := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (PEqualNP.EdgeOwnership.coneStep 14 (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []) g).getD k [] =
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []).getD k [] := by
      intro k hk
      dsimp only [PEqualNP.EdgeOwnership.coneStep]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ =
          gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - 14) (by omega)]; exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - 14) (by omega)] at h3; exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (PEqualNP.EdgeOwnership.coneStep 14
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (14 ≤ w ∧ w < 14 + gs.length))).flatMap
            (fun w => (w - 14) :: (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []).getD (w - 14) []) := by
        dsimp only [PEqualNP.EdgeOwnership.coneStep]
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e1, e2, List.mem_flatMap]
      constructor
      · rintro ⟨w, hw, hmem⟩
        rw [List.mem_filter, decide_eq_true_eq] at hw
        refine ⟨by simp, w, hw.1, hw.2.1, hw.2.2, ?_⟩
        rw [key (w - 14) (by omega)]
        simpa using hmem
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - 14) (by omega)] at h3
        exact ⟨w, List.mem_filter.mpr ⟨hw, decide_eq_true ⟨h1, h2⟩⟩, by simpa using h3⟩
    · have e3 : (PEqualNP.EdgeOwnership.coneStep 14
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []) g).getD j [] = [] := by
        apply List.getD_eq_default
        dsimp only [PEqualNP.EdgeOwnership.coneStep]
        simp only [List.length_append, List.length_singleton, hlen]
        omega
      rw [e3]
      simp only [List.not_mem_nil, false_iff, not_and]
      intro hlt
      simp only [List.length_append, List.length_singleton] at hlt
      omega

theorem inCone_iff (D : Circuit) (i j : ℕ) :
    InCone 14 D i j ↔ j < D.gates.length ∧ ∃ w ∈ (gateAt D j).inputs,
      14 ≤ w ∧ w < 14+j ∧ (i=w-14 ∨ InCone 14 D i (w-14)) := cones_char D.gates i j

theorem gateAt_eq {C : Circuit} {j : ℕ} (hj : j<C.gates.length) : gateAt C j=C.gates[j] := by
  change C.gates.getD j _=C.gates[j]
  exact List.getD_eq_getElem _ _ hj
theorem gateAt_mem {C : Circuit} {j : ℕ} (hj : j<C.gates.length) : gateAt C j∈C.gates := by
  rw [gateAt_eq hj]
  exact List.getElem_mem hj
def stepR {β : Type} (F : Gate → List β → β) (d : β) (R : List β) (g : Gate) : List β :=
  R ++ [F g (g.inputs.map fun i => R.getD i d)]

theorem R_getD_lt {β : Type} (F : Gate → List β → β) (d : β) (gs : List Gate) (w : List β)
    (i : ℕ) (hi : i < w.length) :
    (gs.foldl (stepR F d) w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepR F d w g).length := by simp [stepR]; omega
    rw [ih (stepR F d w g) hlt]
    simp [stepR, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem R_getD_ge {β : Type} (d : β) (w : List β) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem R_getD_gate {β : Type} (F : Gate → List β → β) (d : β) (gs : List Gate) (w : List β)
    (j : ℕ) (hj : j < gs.length) :
    (gs.foldl (stepR F d) w).getD (w.length + j) d =
      F (gs[j]) ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl (stepR F d) w).getD i d else d) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepR F d w g).length := by simp [stepR]
      rw [Nat.add_zero, R_getD_lt F d gs (stepR F d w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepR F d w g).getD w.length d =
          F g (g.inputs.map fun i => w.getD i d) := by
        simp [stepR, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, R_getD_lt F d gs (stepR F d w g) i (by simp [stepR]; omega)]
        simp [stepR, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact R_getD_ge d w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepR F d w g) j hj'
      have hl : (stepR F d w g).length = w.length + 1 := by simp [stepR]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

theorem operands {n} (C : Circuit) (ao : IsAO2 n C) (j : ℕ) (hj : j<C.gates.length) :
    ∃ a b,(gateAt C j).inputs=[a,b] ∧ a<n+j ∧ b<n+j := by
  obtain ⟨a,b,eq⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hj))
  exact ⟨a,b,eq,ao.2.1 j hj a (by simp [eq]),ao.2.1 j hj b (by simp [eq])⟩

def depth (C : Circuit) (w : ℕ) := (andDepths C 14).getD w 0

def tally (g : Gate) (d : List ℕ) := d.foldr max 0 + andLevel g

def logic (g : Gate) (d : List Bool) := g.op.eval d

def value (C : Circuit) (w : ℕ) (x : Fin 14 → Bool) := wireVal 14 C w x

theorem depthAt (C : Circuit) {j a b : ℕ} (hj : j<C.gates.length)
    (row : (gateAt C j).inputs=[a,b]) (ha : a<14+j) (hb : b<14+j) :
    depth C (14+j) = max (depth C a) (depth C b) + andLevel (gateAt C j) := by
  have e := R_getD_gate tally 0 C.gates (List.replicate 14 0) j hj
  rw [List.length_replicate,←gateAt_eq hj,row] at e
  have read (i) : (C.gates.foldl (stepR tally 0) (List.replicate 14 0)).getD i 0 = depth C i := rfl
  simp only [read] at e
  simpa [tally,ha,hb] using e

theorem valAt (C : Circuit) (x : Fin 14 → Bool) {j a b : ℕ} (hj : j<C.gates.length)
    (row : (gateAt C j).inputs=[a,b]) (ha : a<14+j) (hb : b<14+j) :
    value C (14+j) x = (gateAt C j).op.eval [value C a x,value C b x] := by
  have e := R_getD_gate logic false C.gates (List.ofFn x) j hj
  rw [List.length_ofFn,←gateAt_eq hj,row] at e
  have read (i) : (C.gates.foldl (stepR logic false) (List.ofFn x)).getD i false = value C i x := rfl
  simp only [read] at e
  simpa [logic,ha,hb] using e

theorem valRaw (C : Circuit) (x : Fin 14 → Bool) {w : ℕ} (h : w<14) :
    value C w x = x ⟨w,h⟩ := by
  have e := R_getD_lt logic false C.gates (List.ofFn x) w (by simpa using h)
  calc
    value C w x = (List.ofFn x).getD w false := e
    _ = x ⟨w,h⟩ := by rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]; simp [h]

theorem levelAnd {g : Gate} {a b : ℕ} (op : g.op=.and) (row : g.inputs=[a,b]) :
    andLevel g=1 := by simp [andLevel,op,row]

theorem levelOr {g : Gate} (op : g.op=.or) : andLevel g=0 := by simp [andLevel,op]

theorem andEval (a b : Bool) : GateOp.and.eval [a,b] = (a && b) := by cases a <;> cases b <;> rfl
theorem orEval (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by cases a <;> cases b <;> rfl

theorem zeroIsUnion (C : Circuit) (ao : IsAO2 14 C) (s t : Fin 14)
    (w : ℕ) (valid : w<14+C.gates.length) (zero : depth C w=0) :
    value C w (pairInput s t) = (value C w (pairInput s s) || value C w (pairInput t t)) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases raw : w<14
    · simp only [valRaw C _ raw]
      by_cases hs : (⟨w,raw⟩ : Fin 14)=s <;> by_cases ht : (⟨w,raw⟩ : Fin 14)=t <;> simp [pairInput,hs,ht]
    obtain ⟨j,rfl⟩ : ∃ j,w=14+j := ⟨w-14,by omega⟩
    have hj : j<C.gates.length := by omega
    obtain ⟨a,b,row,ha,hb⟩ := operands C ao j hj
    rw [depthAt C hj row ha hb] at zero
    rcases ao.1 _ (gateAt_mem hj) with hand | hor
    · rw [levelAnd hand row] at zero
      omega
    · have da : depth C a=0 := by omega
      have db : depth C b=0 := by omega
      have ea := ih a ha (by omega) da
      have eb := ih b hb (by omega) db
      simp only [valAt C _ hj row ha hb,hor,orEval,ea,eb]
      ac_rfl

def flows (C : Circuit) (u v : ℕ) : Prop :=
  depth C u ≤ depth C v ∧
    (depth C u = depth C v → ∀ x, value C u x = true → value C v x = true)

theorem flowsRefl (C : Circuit) (u : ℕ) : flows C u u := ⟨le_rfl,fun _ _ h=>h⟩

theorem flowsTrans {C : Circuit} {u v w : ℕ} (uv : flows C u v) (vw : flows C v w) : flows C u w := by
  rcases uv with ⟨d1,e1⟩
  rcases vw with ⟨d2,e2⟩
  exact ⟨d1.trans d2,fun eq x hx => e2 (by omega) x (e1 (by omega) x hx)⟩

theorem childFlows {C : Circuit} (ao : IsAO2 14 C) {j w : ℕ} (hj : j<C.gates.length)
    (hw : w ∈ (gateAt C j).inputs) : flows C w (14+j) := by
  obtain ⟨a,b,row,ha,hb⟩ := operands C ao j hj
  have side : w=a ∨ w=b := by simpa [row] using hw
  have de := depthAt C hj row ha hb
  rcases ao.1 _ (gateAt_mem hj) with hand | hor
  · rw [levelAnd hand row] at de
    rcases side with rfl | rfl <;> exact ⟨by omega,fun eq => by omega⟩
  · rw [levelOr hor] at de
    rcases side with rfl | rfl
    · exact ⟨by omega, fun _ x hx => by simp [valAt C x hj row ha hb,hor,orEval,hx]⟩
    · exact ⟨by omega, fun _ x hx => by rw [valAt C x hj row ha hb,hor,orEval,hx]; simp⟩

theorem coneFlows {C : Circuit} (ao : IsAO2 14 C) (i j : ℕ) (below : InCone 14 C i j) :
    flows C (14+i) (14+j) := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    obtain ⟨hj,w,hw,raw,back,route⟩ := (inCone_iff C i j).mp below
    obtain ⟨k,rfl⟩ : ∃ k,w=14+k := ⟨w-14,by omega⟩
    have next := childFlows ao hj hw
    have last : 14+k-14=k := by omega
    rw [last] at route
    rcases route with rfl | inside
    · exact next
    · exact flowsTrans (ih k (by omega) inside) next

def marked (C : Circuit) (k : ℕ) (s t : Fin 14) : Prop :=
  (gateAt C k).op = GateOp.and ∧ gateVal 14 C k (pairInput s t) = true ∧
    ∀ b : Fin 2,value C (opnd C k b) (pairInput s s) = false

private theorem markIndex {C : Circuit} {k : ℕ} {s t : Fin 14} (h : marked C k s t) : k<C.gates.length := by
  by_contra! bad
  have hand := h.1
  change (C.gates.getD k _).op=.and at hand
  rw [List.getD_eq_default _ _ bad] at hand
  cases hand

theorem shallowMarked {C : Circuit} (ao : IsAO2 14 C) {k : ℕ} {s t : Fin 14}
    (mark : marked C k s t) (shallow : depth C (14+k)≤1) :
    depth C (14+k)=1 ∧ value C (14+k) (pairInput t t)=true := by
  have hk := markIndex mark
  obtain ⟨a,b,row,ha,hb⟩ := operands C ao k hk
  obtain ⟨hand,on,off⟩ := mark
  have de := depthAt C hk row ha hb
  rw [levelAnd hand row] at de
  have da : depth C a=0 := by omega
  have db : depth C b=0 := by omega
  have ea := zeroIsUnion C ao s t a (by omega) da
  have eb := zeroIsUnion C ao s t b (by omega) db
  have offA := off 0
  have offB := off 1
  simp [opnd,row] at offA offB
  change value C (14+k) (pairInput s t)=true at on
  rw [valAt C _ hk row ha hb,hand,andEval,Bool.and_eq_true] at on
  rw [offA,Bool.false_or,on.1] at ea
  rw [offB,Bool.false_or,on.2] at eb
  refine ⟨by omega,?_⟩
  rw [valAt C _ hk row ha hb,hand,andEval,←ea,←eb]
  rfl

theorem nestedDepth {C : Circuit} (ao : IsAO2 14 C) {low high : ℕ} {s t : Fin 14}
    (nested : InCone 14 C low high) (lower : marked C low s t) (upper : marked C high t s) :
    3 ≤ depth C (14+high) := by
  by_contra! shallow
  obtain ⟨hj,w,hw,raw,back,route⟩ := (inCone_iff C low high).mp nested
  obtain ⟨k,rfl⟩ : ∃ k,w=14+k := ⟨w-14,by omega⟩
  have eql : 14+k-14=k := by omega
  rw [eql] at route
  have flow : flows C (14+low) (14+k) := by
    rcases route with rfl | below
    · exact flowsRefl _ _
    · exact coneFlows ao _ _ below
  obtain ⟨a,b,row,ha,hb⟩ := operands C ao high hj
  have side : 14+k=a ∨ 14+k=b := by simpa [row] using hw
  have de := depthAt C hj row ha hb
  rw [levelAnd upper.1 row] at de
  have upperChild : depth C (14+k) ≤ 1 := by rcases side with e | e <;> rw [e] <;> omega
  have lo := shallowMarked ao lower (flow.1.trans upperChild)
  have on := flow.2 (by have := flow.1; omega) (pairInput t t) lo.2
  have x := upper.2.2 0
  have y := upper.2.2 1
  simp [opnd,row] at x y
  rcases side with e | e
  · rw [e,x] at on; contradiction
  · rw [e,y] at on; contradiction

theorem outputDepth {C : Circuit} (ao : IsAO2 14 C) {low high : ℕ} {s t : Fin 14}
    (nested : InCone 14 C low high) (live : 14+high=C.output ∨ InCone 14 C high (C.output-14))
    (lower : marked C low s t) (upper : marked C high t s) :
    3 ≤ (andDepths C 14).getD C.output 0 := by
  have three := nestedDepth ao nested lower upper
  change 3 ≤ depth C C.output
  rcases live with eq | cone
  · simpa [←eq] using three
  · have hraw : 14 ≤ C.output := by
      obtain ⟨_,w,_,ge,lt,_⟩ := (inCone_iff _ _ _).mp cone
      omega
    have d := (coneFlows ao _ _ cone).1
    rw [show 14+(C.output-14)=C.output by omega] at d
    exact three.trans d

end NestedFanoDepth
