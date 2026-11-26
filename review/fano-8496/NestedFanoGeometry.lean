import P8Structure
import NestedFanoPaths

namespace NestedFano.Geometry
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_17808
open NestedFanoDepth NestedFano.Live NestedFano.SolReview

def ren (g : Gate) : Gate := ⟨g.op,g.inputs.map mp14⟩
def tagOp : GateOp → Bool
  | .and => true
  | _ => false
def binary (g : Gate) : Bool × ℕ × ℕ := (tagOp g.op,g.inputs.getD 0 0,g.inputs.getD 1 0)
def chartDag (C : Circuit) : Dag := (C.gates.map ren).map binary

@[simp] theorem length_chart (C : Circuit) : (chartDag C).length=C.gates.length := by simp [chartDag]

theorem pm_involution : ∀ a : Fin 14,pm14 (pm14 a)=a := by decide +kernel

theorem mp_involution (i : ℕ) : mp14 (mp14 i)=i := by
  by_cases hi : i<14
  · interval_cases i <;> rfl
  · have same := mp14_ge (by omega : 14 ≤ i)
    rw [same,same]

theorem lowers {w j : ℕ} (hw : w<14+j) : mp14 w<14+j := by
  by_cases h : w<14
  · have := mp14_lt h;omega
  · rwa [mp14_ge (by omega)]

theorem operands_chart (C : Circuit) {j a b : ℕ} (hj : j<C.gates.length)
    (row : (gateAt C j).inputs=[a,b]) :
    opA (chartDag C) j=mp14 a ∧ opB (chartDag C) j=mp14 b := by
  have hk : j<(chartDag C).length := by simpa using hj
  rw [opA_eq _ _ hk,opB_eq _ _ hk,gateAt_eq hj] at *
  simp [chartDag,ren,binary,row]

theorem strict (C : Circuit) (ao : IsAO2 14 C)
    (distinct : ∀ j<C.size,(gateAt C j).inputs.Nodup) : Strict 14 (chartDag C) := by
  intro j hj
  have hj' : j<C.gates.length := by simpa using hj
  obtain ⟨a,b,row,ha,hb⟩ := operands C ao j hj'
  obtain ⟨aa,bb⟩ := operands_chart C hj' row
  rw [aa,bb]
  have nd := distinct j hj'
  rw [row] at nd
  have ab : a≠b := by simpa using nd
  exact ⟨lowers ha,lowers hb,fun e=>ab (by simpa only [mp_involution] using congrArg mp14 e)⟩

theorem foldBinary (gs : List Gate)
    (well : ∀ g∈gs,(g.op=.and ∨ g.op=.or) ∧ ∃ a b,g.inputs=[a,b]) (w : List Bool) :
    wl (gs.map binary) w=gs.foldl stp14 w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨op,a,b,r⟩ := well g (by simp)
    rw [List.map_cons,wl_cons,List.foldl_cons,ih (fun q hq=>well q (List.mem_cons_of_mem _ hq))]
    have same : wstep w (binary g)=stp14 w g := by
      rcases op with eq|eq <;> simp [wstep,binary,stp14,tagOp,r,eq,GateOp.eval]
    rw [same]

theorem chartVal (C : Circuit) (ao : IsAO2 14 C) (y : Fin 14 → Bool) (w : ℕ) :
    val (chartDag C) y (mp14 w) = value C w (fun v=>y (pm14 v)) := by
  have well : ∀ g∈C.gates.map ren,(g.op=.and ∨ g.op=.or) ∧ ∃ a b,g.inputs=[a,b] := by
    intro g hg
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
    obtain ⟨a,b,row⟩ := List.length_eq_two.mp (ao.2.2 q hq)
    exact ⟨ao.1 q hq,mp14 a,mp14 b,by simp [ren,row]⟩
  unfold val chartDag
  rw [foldBinary _ well]
  apply fold14 C.gates (List.ofFn fun i=>y (pm14 i)) (List.ofFn y) (by simp) (by simp) _ w
  intro i
  by_cases hi : i<14
  · rw [mp14,dif_pos hi]
    interval_cases i <;> rfl
  · rw [mp14_ge (by omega),List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]

def tests (C : Circuit) := ∀ k : Fin 58,C.eval (List.ofFn (boundary k))=decide (k.val<21)

theorem size27 (C : Circuit) (ao : IsAO2 14 C) (bound : C.size≤27) (pass : tests C) :
    C.gates.length=27 := by
  have hc : Monotone2 C := fun g hg=>⟨ao.1 _ hg,(ao.2.2 _ hg).le⟩
  have lb := boundaryLower C hc pass
  change 27≤C.gates.length at lb
  change C.gates.length≤27 at bound
  omega

theorem outputLast (C : Circuit) (ao : IsAO2 14 C) (bound : C.size≤27) (pass : tests C) :
    C.output=40 := by
  have len := size27 C ao bound pass
  have hc : Monotone2 C := fun g hg=>⟨ao.1 _ hg,(ao.2.2 _ hg).le⟩
  have u := used C hc bound pass ⟨26,by omega⟩
  change 40∈bag C at u
  obtain out|rd := List.mem_cons.mp (List.mem_filter.mp u).1
  · exact out.symm
  obtain ⟨q,hq,read⟩ := List.mem_flatMap.mp rd
  obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp hq
  have hit : 40∈(gateAt C j).inputs := by rwa [gateAt_eq hj,eq]
  have := ao.2.1 j hj 40 hit
  omega

theorem correct (C : Circuit) (ao : IsAO2 14 C) (bound : C.size≤27) (pass : tests C) : Correct (chartDag C) := by
  have hc : Monotone2 C := fun g hg=>⟨ao.1 _ hg,(ao.2.2 _ hg).le⟩
  have full : ∀ x : Fin 14 → Bool,C.eval (List.ofFn x)=true ↔ FanoE x :=
    (PEqualNP.Outside.L_meta_4647_aux.main (circuitFun 14 C)).mpr
       ⟨fun x y xy=>Bool.le_iff_imp.mpr (circuit_mono hc (fun v=>Bool.le_iff_imp.mp (xy v))),pass⟩
  have eq : outW 14 (chartDag C)=mp14 C.output := by
    rw [outW,length_chart,size27 C ao bound pass,outputLast C ao bound pass];rfl
  intro y
  rw [eq,chartVal C ao]
  change C.eval (List.ofFn (fun v=>y (pm14 v)))=true ↔ HeawoodEdge y
  rw [full]
  constructor
  · rintro ⟨a,b,h,h1,h2⟩
    exact ⟨_,_,geo1 a b h,h1,h2⟩
  · rintro ⟨u,v,h,h1,h2⟩
    obtain ⟨a,b,hab,rfl,rfl⟩ := geo2 u v h
    exact ⟨a,b,hab,h1,h2⟩

theorem live (C : Circuit) (ao : IsAO2 14 C) (bound : C.size≤27) (pass : tests C)
    (distinct : ∀ j<C.size,(gateAt C j).inputs.Nodup) : StrictLive 14 (chartDag C) := by
  let D := chartDag C
  have hS : Strict 14 D := strict C ao distinct
  have hD : Correct D := correct C ao bound pass
  have hl : D.length=27 := (length_chart C).trans (size27 C ao bound pass)
  have hc : Monotone2 C := fun g hg=>⟨ao.1 _ hg,(ao.2.2 _ hg).le⟩
  change StrictLive 14 D
  refine ⟨hS,?_,fun e=>by rw [e] at hl;contradiction⟩
  intro w hw
  change w+1<14+D.length at hw
  by_contra! hf
  have hf0 : fanout D w=0 := by omega
  by_cases raw : w<14
  · obtain ⟨x,y,hxy,hno,hyes⟩ := heawood_essential ⟨w,raw⟩
    have off := (hD y).mpr hyes
    apply hno
    apply (hD x).mp
    have ne : outW 14 D≠w := by unfold outW;omega
    have key := val_unique hS y (fun u=>if u=w then y ⟨w,raw⟩ else val D x u)
      (fun i hi=>by
        by_cases e : i=w
        · subst i;simp
        · simp only [e,ite_false]
          rw [val_input D x i hi]
          exact hxy ⟨i,hi⟩ (fun h=>e (congrArg Fin.val h)))
      (fun j hj=>by
        obtain ⟨na,nb⟩ := na_no_reader hf0 j hj
        have nj : 14+j≠w := by omega
        simp only [nj,na,nb,ite_false]
        exact val_gate hS x j hj)
      (outW 14 D) (by unfold outW;omega)
    simp only [ne,ite_false] at key
    exact key ▸ off
  · let i : Fin C.gates.length := ⟨w-14,by have := size27 C ao bound pass;omega⟩
    have ei : 14+i.val=w := by dsimp [i];omega
    have u := used C hc bound pass i
    rw [ei] at u
    rcases List.mem_cons.mp (List.mem_filter.mp u).1 with e|read
    · have := outputLast C ao bound pass;omega
    obtain ⟨q,hq,mem⟩ := List.mem_flatMap.mp read
    obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp hq
    have hit : w∈(gateAt C j).inputs := by rwa [gateAt_eq hj,eq]
    obtain ⟨a,b,row,ha,hb⟩ := operands C ao j hj
    obtain ⟨aa,bb⟩ := operands_chart C hj row
    have no := na_no_reader hf0 j (by simpa [D] using hj)
    have reach : w=a ∨ w=b := by simpa [row] using hit
    rcases reach with rfl|rfl
    · exact no.1 (aa.trans (mp14_ge (by omega)))
    · exact no.2 (bb.trans (mp14_ge (by omega)))

theorem andSwitch (C : Circuit) (ao : IsAO2 14 C) {j : ℕ} {s t : Fin 14}
    (mark : marked C j s t) : hasAndDoubleSwitch (chartDag C) (pm14 t) := by
  obtain ⟨op,on,off⟩ := mark
  have hj : j<C.gates.length := by
    by_contra! outside
    change (C.gates.getD j _).op=.and at op
    rw [List.getD_eq_default _ _ outside] at op
    cases op
  obtain ⟨a,b,row,ha,hb⟩ := operands C ao j hj
  have bval := valAt C (pairInput s t) hj row ha hb
  change value C (14+j) (pairInput s t)=true at on
  rw [bval,op] at on
  have ab : value C a (pairInput s t)=true ∧ value C b (pairInput s t)=true := by
    have h : ∀ x y : Bool,GateOp.and.eval [x,y]=(x && y) := by decide +kernel
    simpa only [h,Bool.and_eq_true] using on
  have f0 := off 0
  have f1 := off 1
  change value C ((gateAt C j).inputs.getD 0 0) _=false at f0
  change value C ((gateAt C j).inputs.getD 1 0) _=false at f1
  rw [row] at f0 f1
  let pair := fun v=>pairInput s t (pm14 v)
  let single := fun v=>pairInput s s (pm14 v)
  have pull (f : Fin 14 → Bool) : (fun v=>f (pm14 (pm14 v)))=f := funext (fun v=>by rw [pm_involution])
  obtain ⟨aa,bb⟩ := operands_chart C hj row
  refine ⟨pair,single,j,by simpa using hj,?_,?_,?_⟩
  · have ht := tag_eq (chartDag C) j (by simpa using hj)
    rw [ht]
    rw [gateAt_eq hj] at op
    simp [chartDag,binary,ren,tagOp,op]
  · intro v hn
    have ne : pm14 v ≠ t := fun e=>hn (by simpa only [pm_involution] using congrArg pm14 e)
    simp [pair,single,pairInput,ne]
  · intro side
    cases side
    · change val (chartDag C) pair (opA _ _ ) ≠ val (chartDag C) single (opA _ _)
      rw [aa,chartVal C ao,chartVal C ao]
      change value C a (fun v=>pairInput s t (pm14 (pm14 v))) ≠ value C a (fun v=>pairInput s s (pm14 (pm14 v)))
      rw [pull,pull,ab.1,show value C a (pairInput s s)=false from f0]
      decide
    · change val (chartDag C) pair (opB _ _ ) ≠ val (chartDag C) single (opB _ _)
      rw [bb,chartVal C ao,chartVal C ao]
      change value C b (fun v=>pairInput s t (pm14 (pm14 v))) ≠ value C b (fun v=>pairInput s s (pm14 (pm14 v)))
      rw [pull,pull,ab.2,show value C b (pairInput s s)=false from f1]
      decide

theorem markedEligibility (C : Circuit) (ao : IsAO2 14 C) (bound : C.size≤27) (pass : tests C)
    (distinct : ∀ j<C.size,(gateAt C j).inputs.Nodup) {i j : ℕ}
    (lo : marked C i 0 7) (hi : marked C j 7 0) :
    8≤(eligSet 14 (chartDag C)).card ∧ ((eligSet 14 (chartDag C)).card=8 →
      ∃ σ : Equiv.Perm (Fin 14),IsAut σ ∧ ((σ 0).val=6 ∨ (σ 7).val=6)) := by
  apply doubleSwitchGeometry (live C ao bound pass distinct) (correct C ao bound pass)
      ((length_chart C).trans (size27 C ao bound pass)) 0 7 (by decide +kernel)
  · exact toDoubleSwitch (andSwitch C ao hi)
  · exact toDoubleSwitch (andSwitch C ao lo)

theorem markedEligibilityNine (C : Circuit) (ao : IsAO2 14 C) (bound : C.size≤27) (pass : tests C)
    (distinct : ∀ j<C.size,(gateAt C j).inputs.Nodup) {i j : ℕ}
    (lo : marked C i 0 7) (hi : marked C j 7 0) : 9≤(eligSet 14 (chartDag C)).card := by
  exact doubleAndSwitchNine (live C ao bound pass distinct) (correct C ao bound pass)
    ((length_chart C).trans (size27 C ao bound pass)) 0 7 (by decide +kernel)
    (andSwitch C ao hi) (andSwitch C ao lo)

#print axioms markedEligibilityNine

end NestedFano.Geometry

