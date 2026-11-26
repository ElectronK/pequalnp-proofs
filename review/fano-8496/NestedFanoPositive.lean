import NestedFanoIrredundancy

namespace NestedFano.ZeroDeletion
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The tail reindexing argument follows L_meta_17808.FirstDeletion.
private def remap (n absent i : ℕ) : ℕ :=
  if i < n then i else if i = n then absent else i - 1

private def moveGate (n absent : ℕ) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map (remap n absent)⟩

private theorem mapTail {n absent : ℕ} (gs : List Gate) (w v : List Bool)
    (hN : n ≤ v.length) (hl : w.length = v.length + 1) (room : v.length + gs.length < absent)
    (same : ∀ i, v.getD (remap n absent i) false = w.getD i false) :
    ∀ i, ((gs.map (moveGate n absent)).foldl stepWire v).getD (remap n absent i) false =
      (gs.foldl stepWire w).getD i false := by
  induction gs generalizing w v with
  | nil => exact same
  | cons g gs ih =>
    simp only [List.map_cons,List.foldl_cons]
    apply ih
    · simp [stepWire]; omega
    · simp [stepWire,hl]
    · simp [stepWire] at room ⊢; omega
    · intro i
      have computed : gateBit v (moveGate n absent g) = gateBit w g := by
        unfold moveGate gateBit
        rw [List.map_map]
        congr 1
        exact List.map_congr_left fun i _ => same i
      unfold stepWire
      rw [computed]
      by_cases pin : i = n
      · subst i
        have mark : remap n absent n = absent := by simp [remap]
        have old : n < w.length := by omega
        have clear : (v ++ [gateBit w g]).length ≤ absent := by simp; omega
        have oldFalse : w.getD n false = false := by
          rw [← same n,mark,List.getD_eq_default _ _ (by omega)]
        rw [mark,List.getD_eq_default _ _ clear,List.getD_append _ _ _ _ old,oldFalse]
      · have early : i < w.length ↔ remap n absent i < v.length := by
          unfold remap
          split_ifs <;> omega
        have hit : i = w.length ↔ remap n absent i = v.length := by
          unfold remap
          split_ifs <;> omega
        rcases Nat.lt_trichotomy i w.length with low | atEnd | high
        · rw [List.getD_append _ _ _ _ (early.mp low),List.getD_append _ _ _ _ low]
          exact same i
        · have iNew := hit.mp atEnd
          rw [atEnd] at iNew ⊢
          rw [iNew]
          simp [List.getD_eq_getElem?_getD]
        · rw [List.getD_eq_default _ _ (by
            have hi : ¬ remap n absent i < v.length := fun h => (by omega : ¬ i < w.length) (early.mpr h)
            have he : remap n absent i ≠ v.length := fun h => (by omega : i ≠ w.length) (hit.mpr h)
            simp
            omega),
            List.getD_eq_default _ _ (by simp; omega)]


private theorem erasedSlot (w : List Bool) (missing : ℕ) (room : w.length ≤ missing) :
    ∀ i,w.getD (remap w.length missing i) false = (w++[false]).getD i false := by
  intro i
  rcases Nat.lt_trichotomy i w.length with early | same | past
  · rw [List.getD_append _ _ _ _ early]
    simp [remap,early]
  · subst i
    rw [show remap w.length missing w.length = missing by simp [remap],
        List.getD_eq_default _ _ room]
    simp [List.getD_eq_getElem?_getD]
  · rw [show remap w.length missing i=i-1 by simp [remap]; split_ifs <;> omega,
      List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by simp; omega)]

def without (front tail : List Gate) (out : ℕ) : Circuit :=
  let cut := 14+front.length
  let missing := cut+tail.length+1
  ⟨front ++ tail.map (moveGate cut missing),remap cut missing out⟩

def forcedFalse (front tail : List Gate) (out : ℕ) (x : Fin 14 → Bool) :=
  let w := front.foldl stepWire (List.ofFn x)
  (tail.foldl stepWire (w++[false])).getD out false

theorem semantics (front tail : List Gate) (out : ℕ) (x : Fin 14→Bool) :
    (without front tail out).eval (List.ofFn x) = forcedFalse front tail out x := by
  let w := front.foldl stepWire (List.ofFn x)
  let cut := 14+front.length
  let missing := cut+tail.length+1
  have len : w.length=cut := by simp [w,cut,fold_length]
  change ((front++tail.map (moveGate cut missing)).foldl stepWire (List.ofFn x)).getD
    (remap cut missing out) false = _
  rw [List.foldl_append]
  change ((tail.map (moveGate cut missing)).foldl stepWire w).getD (remap cut missing out) false =
    (tail.foldl stepWire (w++[false])).getD out false
  apply mapTail tail (w++[false]) w (by omega) (by simp) (by dsimp [missing];omega)
  rw [←len]
  exact erasedSlot w missing (by dsimp [missing];omega)

theorem legal (front tail : List Gate) (g : Gate) (out : ℕ)
    (hm : Monotone2 (⟨front++g::tail,out⟩ : Circuit)) : Monotone2 (without front tail out) := by
  intro a ha
  change a ∈ front ++ tail.map _ at ha
  rcases List.mem_append.mp ha with h | h
  · exact hm a (List.mem_append_left _ h)
  · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp h
    have ok := hm u (List.mem_append_right _ (List.mem_cons_of_mem _ hu))
    exact ⟨ok.1,by simpa [moveGate] using ok.2⟩

theorem positiveWitness (front tail : List Gate) (g : Gate) (out : ℕ)
    (hm : Monotone2 (⟨front++g::tail,out⟩ : Circuit))
    (small : (⟨front++g::tail,out⟩ : Circuit).size ≤ 27)
    (rows : ∀ k : Fin 58, (⟨front++g::tail,out⟩ : Circuit).eval (List.ofFn (boundary k)) =
      decide (k.val<21)) :
    ∃ k : Fin 58, k.val<21 ∧ gateBit (front.foldl stepWire (List.ofFn (boundary k))) g=true ∧
      forcedFalse front tail out (boundary k)=false := by
  classical
  let D := without front tail out
  have fails : ∃ k : Fin 58, D.eval (List.ofFn (boundary k)) ≠ decide (k.val<21) := by
    by_contra! none
    have lb := boundaryLower D (legal front tail g out hm) none
    simp [D,without,Circuit.size] at lb small
    omega
  obtain ⟨k,err⟩ := fails
  rw [show D.eval (List.ofFn (boundary k)) = forcedFalse front tail out (boundary k) by
    exact semantics front tail out (boundary k)] at err
  let w := front.foldl stepWire (List.ofFn (boundary k))
  have original := rows k
  change ((front++g::tail).foldl stepWire (List.ofFn (boundary k))).getD out false = _ at original
  rw [List.foldl_append,List.foldl_cons] at original
  change (tail.foldl stepWire (w ++ [gateBit w g])).getD out false = _ at original
  change (tail.foldl stepWire (w ++ [false])).getD out false ≠ _ at err
  have comp := fold_mono tail (fun h hh=> monoGate_of_mem hm
      (List.mem_append_right _ (List.mem_cons_of_mem _ hh)))
    (append_mono (w := w) (z := w) ⟨rfl,fun i h=>h⟩ (a:=false) (b:=gateBit w g) (by simp))
  by_cases pos : k.val<21
  · simp [pos] at original err
    refine ⟨k,pos,?_,?_⟩
    · cases gate : gateBit w g with
      | false => rw [gate,err] at original; contradiction
      | true => rfl
    · exact err
  · simp [pos] at original err
    have h := comp.2 out err
    rw [List.getD_eq_getElem?_getD] at h
    rw [original] at h
    contradiction

end NestedFano.ZeroDeletion
