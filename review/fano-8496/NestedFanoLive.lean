import NestedFanoPositive
import FanoRestriction
import NestedFanoDepth
import NestedFanoTree

namespace NestedFano.Live
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover
open NestedFanoDepth

theorem untouched (cut : ℕ) (gs : List Gate) (w v : List Bool)
    (avoid : ∀ q∈gs,cut ∉ q.inputs) (len : w.length=v.length)
    (eq : ∀ i,i≠cut → w.getD i false=v.getD i false) :
    ∀ i,i≠cut → (gs.foldl stepWire w).getD i false=(gs.foldl stepWire v).getD i false := by
  induction gs generalizing w v with
  | nil => exact eq
  | cons g tail ih =>
    have valEq : gateBit w g=gateBit v g := by
      unfold gateBit
      congr 1
      apply List.map_congr_left
      intro i mem
      apply eq
      exact fun e => avoid g List.mem_cons_self (e ▸ mem)
    apply ih (w:=stepWire w g) (v:=stepWire v g) (fun q h=>avoid q (List.mem_cons_of_mem _ h))
    · simp [stepWire,len]
    · intro i ne
      unfold stepWire
      rw [valEq]
      by_cases hi : i=w.length
      · rw [hi,PEqualNP.Outside.L_meta_10135.Restriction.getD_snoc_eq,len,
           PEqualNP.Outside.L_meta_10135.Restriction.getD_snoc_eq]
      · rw [PEqualNP.Outside.L_meta_10135.Restriction.getD_snoc_ne _ _ _ _ hi,
            PEqualNP.Outside.L_meta_10135.Restriction.getD_snoc_ne _ _ _ _ (len ▸ hi)]
        exact eq i ne

theorem usedAfter (front tail : List Gate) (g : Gate) (out : ℕ)
    (hm : Monotone2 (⟨front++g::tail,out⟩ : Circuit))
    (small : (⟨front++g::tail,out⟩ : Circuit).size≤27)
    (rows : ∀ k : Fin 58,(⟨front++g::tail,out⟩ : Circuit).eval (List.ofFn (boundary k))=decide (k.val<21)) :
    14+front.length=out ∨ ∃ q∈tail,14+front.length ∈ q.inputs := by
  classical
  by_contra! none
  obtain ⟨k,pos,_,lost⟩ := ZeroDeletion.positiveWitness front tail g out hm small rows
  let w := front.foldl stepWire (List.ofFn (boundary k))
  have lw : w.length=14+front.length := by simp [w,fold_length]
  have agree := untouched (14+front.length) tail (w++[gateBit w g]) (w++[false]) none.2
    (by simp) (fun i ne=>by
      rw [PEqualNP.Outside.L_meta_10135.Restriction.getD_snoc_ne _ _ _ _ (by omega),
          PEqualNP.Outside.L_meta_10135.Restriction.getD_snoc_ne _ _ _ _ (by omega)]) out (Ne.symm none.1)
  have orig := rows k
  change ((front++g::tail).foldl stepWire (List.ofFn (boundary k))).getD out false = _ at orig
  rw [List.foldl_append,List.foldl_cons] at orig
  change (tail.foldl stepWire (w++[gateBit w g])).getD out false=_ at orig
  change (tail.foldl stepWire (w++[false])).getD out false=false at lost
  rw [agree,lost] at orig
  simp [pos] at orig

def bag (C : Circuit) := (C.output :: C.gates.flatMap Gate.inputs).filter (fun i => decide (14 ≤ i))

theorem used (C : Circuit) (hm : Monotone2 C) (small : C.size≤27)
    (rows : ∀ k : Fin 58,C.eval (List.ofFn (boundary k))=decide (k.val<21))
    (j : Fin C.gates.length) : (14+j.val) ∈ bag C := by
  let front := C.gates.take j.val
  let g := C.gates[j.val]
  let tail := C.gates.drop (j.val+1)
  have split : front++g::tail=C.gates := by
    change C.gates.take j.val ++ C.gates[j.val] :: C.gates.drop (j.val+1)=C.gates
    rw [← List.drop_eq_getElem_cons j.isLt,List.take_append_drop]
  have length : front.length=j.val := by simp [front,Nat.min_eq_left j.isLt.le]
  have same : (⟨front++g::tail,C.output⟩ : Circuit)=C := by rw [split]
  obtain first|⟨q,hq,hp⟩ := usedAfter front tail g C.output (same ▸ hm) (same ▸ small) (same ▸ rows)
  · apply List.mem_filter.mpr
    exact ⟨List.mem_cons.mpr (Or.inl (length ▸ first)),by simp⟩
  · apply List.mem_filter.mpr
    refine ⟨List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨q,?_,length ▸ hp⟩),by simp⟩
    rw [←split]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ hq)

end NestedFano.Live

