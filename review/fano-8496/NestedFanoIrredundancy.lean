import FanoOrdinary
import PEqualNP.Outside.L_meta_4647

namespace NestedFano

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

-- Circuit monotonicity from the project's L_meta_17808.FirstDeletion.


open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def gateBit (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def stepWire (w : List Bool) (g : Gate) : List Bool := w ++ [gateBit w g]

def WiresLE (w z : List Bool) : Prop :=
  w.length = z.length ∧ ∀ i, w.getD i false = true → z.getD i false = true

def IsMonoGate (g : Gate) : Prop := g.op = GateOp.and ∨ g.op = GateOp.or

lemma monoGate_of_mem {C : Circuit} (hC : Monotone2 C) {g : Gate} (hg : g ∈ C.gates) :
    IsMonoGate g := by
  simpa [IsMonoGate] using (hC g hg).1

lemma bit_mono {w z : List Bool} (h : WiresLE w z) {g : Gate} (hg : IsMonoGate g)
    (hw : gateBit w g = true) : gateBit z g = true := by
  rcases hg with hop | hop
  · simp only [gateBit, hop, GateOp.eval, List.all_map, List.all_eq_true,
      Function.comp_apply, id_eq] at hw ⊢
    exact fun i hi => h.2 i (hw i hi)
  · simp only [gateBit, hop, GateOp.eval, List.any_map, List.any_eq_true,
      Function.comp_apply, id_eq] at hw ⊢
    obtain ⟨i, hi, hv⟩ := hw
    exact ⟨i, hi, h.2 i hv⟩

lemma append_mono {w z : List Bool} {a b : Bool} (h : WiresLE w z)
    (hab : a = true → b = true) : WiresLE (w ++ [a]) (z ++ [b]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  rw [List.getD_eq_getElem?_getD] at hi ⊢
  by_cases hlt : i < w.length
  · rw [List.getElem?_append_left hlt] at hi
    rw [List.getElem?_append_left (by rwa [← h.1])]
    simpa only [List.getD_eq_getElem?_getD] using h.2 i
      (by simpa only [List.getD_eq_getElem?_getD] using hi)
  · rw [List.getElem?_append_right (Nat.le_of_not_gt hlt)] at hi
    rw [List.getElem?_append_right (by rw [← h.1]; omega), ← h.1]
    cases hd : i - w.length with
    | zero =>
      simp only [hd, List.getElem?_cons_zero, Option.getD_some] at hi ⊢
      exact hab hi
    | succ k => simp [hd] at hi

lemma fold_mono (gs : List Gate) (hg : ∀ g ∈ gs, IsMonoGate g)
    {w z : List Bool} (h : WiresLE w z) :
    WiresLE (gs.foldl stepWire w) (gs.foldl stepWire z) := by
  induction gs generalizing w z with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun k hk => hg k (List.mem_cons_of_mem _ hk))
      (append_mono h (bit_mono h (hg g (by simp))))

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (stepWire w g) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : Fin n) :
    (List.ofFn x).getD u.val false = x u := by
  simp [List.getD_eq_getElem?_getD]

lemma ofFn_mono {n : ℕ} {x y : Fin n → Bool} (h : ∀ u, x u = true → y u = true) :
    WiresLE (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  by_cases hlt : i < n
  · rw [ofFn_getD y ⟨i, hlt⟩]
    exact h ⟨i, hlt⟩ (by simpa only [ofFn_getD x ⟨i, hlt⟩] using hi)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hlt)] at hi
    cases hi

lemma pair_le {n : ℕ} {x : Fin n → Bool} {u v : Fin n}
    (hu : x u = true) (hv : x v = true) (k : Fin n) :
    pairInput u v k = true → x k = true := by
  simp only [pairInput, decide_eq_true_eq]
  rintro (rfl | rfl)
  · exact hu
  · exact hv

lemma circuit_mono {n : ℕ} {C : Circuit} (hC : Monotone2 C) {x y : Fin n → Bool}
    (hxy : ∀ u, x u = true → y u = true) :
    circuitFun n C x = true → circuitFun n C y = true :=
  (fold_mono C.gates (fun _ hg => monoGate_of_mem hC hg) (ofFn_mono hxy)).2 C.output



abbrev boundary (k : Fin 58) : Fin 14 → Bool := PEqualNP.Outside.L_meta_4647_aux.col k.val

theorem boundaryLower (C : Circuit) (hm : Monotone2 C)
    (tests : ∀ k : Fin 58, C.eval (List.ofFn (boundary k)) = decide (k.val < 21)) :
    27 ≤ C.size := by
  apply PEqualNP.Outside.L_meta_17808.fano27 C hm
  apply (PEqualNP.Outside.L_meta_4647_aux.main (circuitFun 14 C)).mpr
  refine ⟨?_, tests⟩
  intro x y le
  rw [Bool.le_iff_imp]
  exact circuit_mono hm (fun u => Bool.le_iff_imp.mp (le u))

def renameWire (cut fallback w : ℕ) :=
  if w < cut then w else if w = cut then fallback else w - 1

def renameGate (cut fallback : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (renameWire cut fallback)⟩

def bypass (front suffix : List Gate) (out fallback : ℕ) : Circuit :=
  let cut := 14 + front.length
  ⟨front ++ suffix.map (renameGate cut fallback), renameWire cut fallback out⟩

private theorem transfer (cut fallback : ℕ) (earlier : fallback < cut)
    (suffix : List Gate) (before after : List Bool) (contains : cut ≤ after.length)
    (len : before.length = after.length + 1)
    (eqs : ∀ i, after.getD (renameWire cut fallback i) false = before.getD i false) :
    ∀ i, ((suffix.map (renameGate cut fallback)).foldl stepWire after).getD
      (renameWire cut fallback i) false = (suffix.foldl stepWire before).getD i false := by
  induction suffix generalizing before after with
  | nil => exact eqs
  | cons g tail ih =>
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · simp [stepWire]; omega
    · simp [stepWire, len]
    · intro i
      have same : gateBit after (renameGate cut fallback g) = gateBit before g := by
        unfold gateBit renameGate
        rw [List.map_map]
        congr 1
        exact List.map_congr_left (fun j _ => eqs j)
      unfold stepWire
      rw [same]
      have small : renameWire cut fallback i < after.length ↔ i < before.length := by
        unfold renameWire; split_ifs <;> omega
      have hit : renameWire cut fallback i = after.length ↔ i = before.length := by
        unfold renameWire; split_ifs <;> omega
      rcases Nat.lt_trichotomy i before.length with lo | eq | hi
      · rw [List.getD_append _ _ _ _ (small.mpr lo), List.getD_append _ _ _ _ lo]
        exact eqs i
      · have newEq := hit.mpr eq
        rw [newEq, eq]
        simp [List.getD_eq_getElem?_getD]
      · have past : after.length < renameWire cut fallback i := by
          have nlo : ¬renameWire cut fallback i < after.length := fun h => (by omega : ¬ i < before.length) (small.mp h)
          have neq : renameWire cut fallback i ≠ after.length := fun h => (by omega : i ≠ before.length) (hit.mp h)
          omega
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private theorem initialTransfer (w : List Bool) (fallback : ℕ) (h : fallback < w.length) :
    ∀ i, w.getD (renameWire w.length fallback i) false =
      (w ++ [w.getD fallback false]).getD i false := by
  intro i
  rcases Nat.lt_trichotomy i w.length with lo | eq | hi
  · rw [List.getD_append _ _ _ _ lo, show renameWire w.length fallback i = i by simp [renameWire, lo]]
  · subst i
    simp [renameWire, List.getD_eq_getElem?_getD]
  · have hcut : renameWire w.length fallback i = i-1 := by simp [renameWire]; split_ifs <;> omega
    rw [hcut,List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by simp; omega)]

def replacedEvaluation (front suffix : List Gate) (out fallback : ℕ) (x : Fin 14 → Bool) : Bool :=
  let w := front.foldl stepWire (List.ofFn x)
  (suffix.foldl stepWire (w ++ [w.getD fallback false])).getD out false

theorem bypassEvaluation (front suffix : List Gate) (out fallback : ℕ)
    (earlier : fallback < 14 + front.length) (x : Fin 14 → Bool) :
    (bypass front suffix out fallback).eval (List.ofFn x) =
      replacedEvaluation front suffix out fallback x := by
  let w := front.foldl stepWire (List.ofFn x)
  have len : w.length = 14 + front.length := by simp [w, fold_length]
  change ((front ++ suffix.map (renameGate (14 + front.length) fallback)).foldl stepWire (List.ofFn x)).getD
    (renameWire (14 + front.length) fallback out) false = _
  rw [List.foldl_append]
  change ((suffix.map (renameGate (14 + front.length) fallback)).foldl stepWire w).getD _ false =
    (suffix.foldl stepWire (w ++ [w.getD fallback false])).getD out false
  rw [←len] at earlier ⊢
  exact transfer w.length fallback earlier suffix (w ++ [w.getD fallback false]) w
    (Nat.le_refl _) (by simp) (initialTransfer w fallback earlier) out

theorem bypassLegal (front suffix : List Gate) (g : Gate) (out fallback : ℕ)
    (hm : Monotone2 (⟨front ++ g::suffix,out⟩ : Circuit)) :
    Monotone2 (bypass front suffix out fallback) := by
  intro a ha
  change a ∈ front ++ suffix.map _ at ha
  rcases List.mem_append.mp ha with h | h
  · exact hm a (List.mem_append_left _ h)
  · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp h
    have ok := hm u (List.mem_append_right _ (List.mem_cons_of_mem _ hu))
    exact ⟨ok.1,by simpa [renameGate] using ok.2⟩

theorem observable (front suffix : List Gate) (g : Gate) (out fallback : ℕ)
    (earlier : fallback < 14 + front.length)
    (hm : Monotone2 (⟨front ++ g::suffix,out⟩ : Circuit))
    (small : (⟨front ++ g::suffix,out⟩ : Circuit).size ≤ 27) :
    ∃ k : Fin 58, replacedEvaluation front suffix out fallback (boundary k) ≠ decide (k.val < 21) := by
  classical
  by_contra! noError
  have lb := boundaryLower (bypass front suffix out fallback) (bypassLegal front suffix g out fallback hm)
    (fun k => (bypassEvaluation front suffix out fallback earlier _).trans (noError k))
  simp [bypass, Circuit.size] at lb small
  omega

end NestedFano
