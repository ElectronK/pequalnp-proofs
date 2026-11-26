import MultipleSharing

namespace NestedFano.SolReview

open PEqualNP.Outside.L_meta_17808 Finset

abbrev majority := sem_hw_opp (0 : Fin 14)
abbrev rareInputs : Finset (Fin 14) := {0, 1, 2, 3, 4, 5}
abbrev exceptional : Fin 14 := 6

theorem eightNeighborhoods {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (length : D.length = 27) (hi : ineligSet 14 D = rareInputs) :
    ∀ l : Fin 7, sup_Occ 14 D majority (sem_hw_nb (os_pt l)) := by
  classical
  let Iq : Finset (Fin 7) := {0,1,2,3,4,5}
  have budget : totalSurplus 14 D = 14 := by
    have id := surplus_identity h
    omega
  have eq : ineligSet 14 D = Iq.image os_pt := by rw [hi]; decide +kernel
  have plus := tri012 h hD (by rw [hi]; decide +kernel)
  have card6 : Iq.card = 6 := rfl
  have zero := (sideSevenEightNine h hD budget Iq eq (Or.inr ⟨Or.inr card6, plus⟩)).1 card6.ge
  have zle := zeroBranches_le_surplus h.1
  have hs := oneSideMissingAccounting h hD budget Iq (by decide) eq
  change (missingNeighborhoods D).card ≤ _ ∧ _ at hs
  obtain ⟨upper, _, relation⟩ := hs
  rw [card6] at upper
  rw [zero] at zle
  intro l
  by_contra missing
  have mem : l ∈ missingNeighborhoods D := mem_filter.mpr ⟨mem_univ _, missing⟩
  have pos := card_pos.mpr ⟨l, mem⟩
  have one : (missingNeighborhoods D).card = 1 := by omega
  have bad := relation pos
  rw [one, zero] at bad
  omega

def projection (D : Dag) (w : ℕ) := supp 14 D w ∩ majority

theorem fourteenProjectedValues {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (length : D.length = 27) (hi : ineligSet 14 D = rareInputs) :
    14 ≤ ((sup_big 14 D majority).image (fun j => projection D (14+j))).card := by
  classical
  let L : Finset (Finset (Fin 14)) := univ.image (fun l : Fin 7 => sem_hw_nb (os_pt l))
  have l7 : L.card = 7 := by
    rw [card_image_of_injective _ (fun a b eq => os_pt_inj (hw_nb_inj eq))]
    simp
  have tags : ∀ T ∈ L, T.card = 3 ∧ sup_Occ 14 D majority T := by
    intro T ht
    obtain ⟨l, -, rfl⟩ := mem_image.mp ht
    exact ⟨degree_three _, eightNeighborhoods h hD length hi l⟩
  have intersections : ∀ T ∈ L, ∀ U ∈ L, T ≠ U → (T ∩ U).card ≤ 1 := by
    intro T hT U hU ne
    obtain ⟨k, -, rfl⟩ := mem_image.mp hT
    obtain ⟨l, -, rfl⟩ := mem_image.mp hU
    have nb : os_pt k ≠ os_pt l := fun eq => ne (congrArg sem_hw_nb eq)
    simpa [sem_hw_nb] using sup_hw_inter (os_pt k) (os_pt l) nb univ
  obtain ⟨A, count, details⟩ := sup_aux_exists h.1 (by decide : majority.card ≤ 7) L tags intersections
  have hd : Disjoint L A := by
    rw [disjoint_left]
    intro v hv ha
    have sz := (tags v hv).1
    rcases (details v ha).2 with ⟨two, -⟩ | four | five <;> omega
  have inclusion : L ∪ A ⊆ (sup_big 14 D majority).image (fun j => projection D (14+j)) := by
    intro T mT
    have both : 2 ≤ T.card ∧ sup_Occ 14 D majority T := by
      rcases mem_union.mp mT with hL | hA
      · exact ⟨by have := (tags _ hL).1; omega, (tags _ hL).2⟩
      · refine ⟨?_, (details T hA).1⟩
        rcases (details T hA).2 with ⟨two, -⟩ | four | five <;> omega
    obtain ⟨w, mem, eq⟩ := sup_occ_big h.1 both.1 both.2
    exact mem_image.mpr ⟨w, mem, eq⟩
  have result := card_le_card inclusion
  rw [card_union_of_disjoint hd, l7] at result
  rw [l7] at count
  omega

def RarePath (D : Dag) (w : ℕ) : Prop :=
  ∃ c ∈ rareInputs, Relation.ReflTransGen (sem_step 14 D) c.val w

theorem rarePathProjectedEmpty {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hi : ineligSet 14 D = rareInputs) (zero : Bzero 14 D = 0)
    (w : ℕ) (path : RarePath D w) : projection D w = ∅ := by
  obtain ⟨c, hc, runs⟩ := path
  have bad : c ∈ ineligSet 14 D := hi ▸ hc
  obtain ⟨ch, _⟩ := pathWithoutZeroShared h hD zero c bad w runs
  have independent : ¬ sem_Edge HG (sem_ind majority) := by
    rintro ⟨a, b, edge, ha, hb⟩
    exact sem_hw_opp_indep 0 a (by simpa [sem_ind] using ha) b (by simpa [sem_ind] using hb) edge
  have cNb : ∃ p ∈ majority, Adj c p :=
    (by decide +kernel : ∀ c ∈ rareInputs, ∃ p ∈ majority, Adj c p) c hc
  obtain ⟨p, hp, cp⟩ := cNb
  have positive : sem_Edge HG (sem_ins c (sem_ind majority)) :=
    ⟨c,p,cp,sem_ins_self c _,sem_ins_ge c _ p (by simp [sem_ind,hp])⟩
  have off := (sem_dom_split h.1 (sem_heawood_comp hD) _ c w
    (sem_chain_dom h.1 ch) independent positive).1
  apply eq_empty_of_forall_notMem
  intro v hv
  obtain ⟨inS, inP⟩ := mem_inter.mp hv
  exact Bool.false_ne_true (off.symm.trans (sem_val_of_supp h.1 inS (by simp [sem_ind,inP])))

theorem pureRawOrInjectionImpossible {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    {c : Fin 14} (hc : c ∈ rareInputs)
    (j : ℕ) (hj : j < D.length) (op : tag D j = false) (side : Bool)
    (reader : src D (j,side) = exceptional.val)
    (chain : sem_Chain 14 D c.val (14+j)) : False := by
  obtain ⟨p, a, b⟩ :=
    (by decide +kernel : ∀ c ∈ rareInputs, ∃ p : Fin 14,
      hc_adjB c p = true ∧ hc_adjB exceptional p = false) c hc
  have cp := (hc_adjB_iff _ _).1 a
  have ep := sem_adjB_false.1 b
  let z := sem_two exceptional p
  let y := sem_ins c z
  have active (x : Fin 14 → Bool) (eOn : x exceptional = true) : val D x (14+j) = true := by
    rw [sem_val_gate_src h.1 x hj side, op, reader, val_input D x _ exceptional.isLt, eOn, gop_false]
    rfl
  have eOn : z exceptional = true := by simp [z,sem_two]
  have eq := sem_dom_eq h.1 z y c (sem_ins_agree c z) (14+j) (sem_chain_dom h.1 chain)
    ((active z eOn).trans (active y (sem_ins_ge c z _ eOn)).symm)
  have yYes : sem_Edge HG y := by
    exact ⟨c,p,cp,sem_ins_self c z,sem_ins_ge c z _ (by simp [z,sem_two])⟩
  have zNo : ¬ sem_Edge HG z := by
    rintro ⟨a,b,hAB,ha,hb⟩
    simp [z,sem_two] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> subst a <;> subst b
    · exact adj_irrefl _ hAB
    · exact ep hAB
    · exact ep (adj_symm hAB)
    · exact adj_irrefl _ hAB
  exact zNo ((sem_heawood_comp hD z).mp (eq.trans ((sem_heawood_comp hD y).mpr yYes)))

theorem rareGateOffOn {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hi : ineligSet 14 D = rareInputs) (zero : Bzero 14 D = 0)
    {c : Fin 14} (hc : c ∈ rareInputs) (w : ℕ)
    (path : Relation.ReflTransGen (sem_step 14 D) c.val w) :
    val D (sem_ind majority) w = false ∧ val D (sem_ins c (sem_ind majority)) w = true := by
  have bad : c ∈ ineligSet 14 D := hi ▸ hc
  obtain ⟨chain, _⟩ := pathWithoutZeroShared h hD zero c bad w path
  have independent : ¬ sem_Edge HG (sem_ind majority) := by
    rintro ⟨a, b, edge, ha, hb⟩
    exact sem_hw_opp_indep 0 a (by simpa [sem_ind] using ha) b (by simpa [sem_ind] using hb) edge
  obtain ⟨p, hp, cp⟩ :=
    (by decide +kernel : ∀ c ∈ rareInputs, ∃ p ∈ majority, Adj c p) c hc
  have positive : sem_Edge HG (sem_ins c (sem_ind majority)) :=
    ⟨c,p,cp,sem_ins_self c _,sem_ins_ge c _ p (by simp [sem_ind,hp])⟩
  exact sem_dom_split h.1 (sem_heawood_comp hD) _ c w
    (sem_chain_dom h.1 chain) independent positive

theorem rareMergeIsOr {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hi : ineligSet 14 D = rareInputs) (zero : Bzero 14 D = 0)
    (j : ℕ) (hj : j < D.length)
    (left : RarePath D (src D (j,false))) (right : RarePath D (src D (j,true))) :
    tag D j = false := by
  by_contra! andGate
  have atAnd : tag D j = true := by cases y : tag D j <;> simp [y] at andGate ⊢
  obtain ⟨a, ha, leftPath⟩ := left
  obtain ⟨b, hb, rightPath⟩ := right
  have step0 : sem_step 14 D (src D (j,false)) (14+j) := sem_step_src hj false
  have step1 : sem_step 14 D (src D (j,true)) (14+j) := sem_step_src hj true
  have onA := rareGateOffOn h hD hi zero ha _ (Relation.ReflTransGen.tail leftPath step0)
  have onB := rareGateOffOn h hD hi zero hb _ (Relation.ReflTransGen.tail rightPath step1)
  obtain ⟨ca, fa⟩ := pathWithoutZeroShared h hD zero a (hi ▸ ha) _ leftPath
  obtain ⟨cb, fb⟩ := pathWithoutZeroShared h hD zero b (hi ▸ hb) _ rightPath
  have fa1 := le_antisymm fa (sem_step_fanout step0)
  have fb1 := le_antisymm fb (sem_step_fanout step1)
  have stayR := sem_sibling_indep h.1 a hj true ca (by simpa using fa1)
    (sem_ind majority) (sem_ins a (sem_ind majority)) (sem_ins_agree a _)
  have stayL := sem_sibling_indep h.1 b hj false cb (by simpa using fb1)
    (sem_ind majority) (sem_ins b (sem_ind majority)) (sem_ins_agree b _)
  have yesA := onA.2
  have yesB := onB.2
  have off := onA.1
  rw [sem_val_gate_src h.1 _ hj true, atAnd, gop_true, Bool.and_eq_true, ← stayR] at yesA
  rw [sem_val_gate_src h.1 _ hj false, atAnd, gop_true, Bool.and_eq_true, ← stayL] at yesB
  rw [sem_val_gate_src h.1 _ hj true, atAnd, gop_true, yesA.1] at off
  simp only [Bool.not_true, yesB.1, Bool.and_self] at off
  contradiction

def RareAnchor (D : Dag) (c : Fin 14) (j : ℕ) : Prop :=
  j < D.length ∧ tag D j = true ∧ ∃ s : Bool,
    Relation.ReflTransGen (sem_step 14 D) c.val (src D (j,!s)) ∧
    projection D (src D (j,s)) = sem_hw_nb c

theorem hasRareAnchor {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hi : ineligSet 14 D = rareInputs) (zero : Bzero 14 D = 0) {c : Fin 14}
    (hc : c ∈ rareInputs) : ∃ j, RareAnchor D c j := by
  have path := sem_noempty_chain_out sem_heawood_gr h (sem_heawood_comp hD) zero (hi ▸ hc)
  obtain ⟨j, s, hj, op, chain, support⟩ := sem_exact_nbhd sem_heawood_gr h.1
    (sem_heawood_comp hD) majority (sem_hw_opp_indep 0) path
  refine ⟨j,hj,op,s,sem_rtg_mono (fun _ _ e => e.1) chain,?_⟩
  ext p
  rw [projection, mem_inter, hw_mem_nb]
  constructor
  · exact fun ph => (support p ph.2).mp ph.1
  · intro cp
    have all : ∀ c ∈ rareInputs, sem_hw_nb c ⊆ majority := by decide +kernel
    have pMaj := all c hc (hw_mem_nb.mpr cp)
    exact ⟨(support p pMaj).mpr cp,pMaj⟩

theorem rareAnchorOnlyPath {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hi : ineligSet 14 D = rareInputs) (zero : Bzero 14 D = 0)
    {c d : Fin 14} (hc : c ∈ rareInputs) (hd : d ∈ rareInputs)
    {j : ℕ} (anchor : RareAnchor D c j)
    (arrives : Relation.ReflTransGen (sem_step 14 D) d.val (14+j)) : c = d := by
  by_contra ne
  obtain ⟨hj, op, s, cPath, proj⟩ := anchor
  have dAt : ∃ t : Bool, Relation.ReflTransGen (sem_step 14 D) d.val (src D (j,t)) := by
    rcases Relation.ReflTransGen.cases_tail arrives with eq | ⟨w, path, step⟩
    · have := d.isLt
      omega
    · obtain ⟨k,t,hk,eq,srcEq⟩ := sem_step_iff.mp step
      have ke : k=j := by omega
      subst k
      exact ⟨t, srcEq.symm ▸ path⟩
  obtain ⟨t,dPath⟩ := dAt
  cases hts : t == s
  · have neq' : t = !s := by cases t <;> cases s <;> simp_all
    have de := (show ∀ c ∈ rareInputs, ∀ d ∈ rareInputs, c ≠ d →
        ∃ p ∈ majority, hc_adjB d p = true ∧ hc_adjB c p = false by decide +kernel) c hc d hd ne
    obtain ⟨p,hp,dPt,cPt⟩ := de
    have dp := (hc_adjB_iff _ _).1 dPt
    have cp := sem_adjB_false.1 cPt
    have chainGate := (pathWithoutZeroShared h hD zero d (hi ▸ hd) _ arrives).1
    have on : val D (sem_ins d (single p)) (14+j) = true :=
      (sem_dom_split h.1 (sem_heawood_comp hD) _ d _ (sem_chain_dom h.1 chainGate)
        (sem_single_no_edge sem_heawood_gr p)
        ⟨d,p,dp,sem_ins_self d _,sem_ins_ge d _ p (by simp [single])⟩).2
    rw [neq'] at dPath
    obtain ⟨dChain, fUpper⟩ := pathWithoutZeroShared h hD zero d (hi ▸ hd) _ dPath
    have step : sem_step 14 D (src D (j,!s)) (14+j) := sem_step_src hj (!s)
    have noChange := sem_sibling_indep h.1 d hj s dChain
      (le_antisymm fUpper (sem_step_fanout step)) (single p) (sem_ins d (single p)) (sem_ins_agree d _)
    rw [sem_val_gate_src h.1 _ hj s, op, gop_true, Bool.and_eq_true, ← noChange] at on
    have mem : p ∈ projection D (src D (j,s)) := mem_inter.mpr ⟨mem_supp.mpr on.1,hp⟩
    rw [proj, hw_mem_nb] at mem
    exact cp mem
  · have same : t=s := by simpa using hts
    subst t
    cases s
    · exact Bool.false_ne_true ((rareMergeIsOr h hD hi zero j hj ⟨d,hd,dPath⟩
         ⟨c,hc,cPath⟩).symm.trans op)
    · exact Bool.false_ne_true ((rareMergeIsOr h hD hi zero j hj ⟨c,hc,cPath⟩
         ⟨d,hd,dPath⟩).symm.trans op)
noncomputable def rareWires (D : Dag) : Finset ℕ := by
  classical
  exact (inner 14 D).filter (RarePath D)

noncomputable def rareMerges (D : Dag) : Finset ℕ := by
  classical
  exact (range D.length).filter
    (fun j => RarePath D (src D (j,false)) ∧ RarePath D (src D (j,true)))

theorem rareExtend {D : Dag} {a b : ℕ} (start : RarePath D a)
    (step : sem_step 14 D a b) : RarePath D b := by
  obtain ⟨c,hc,path⟩ := start
  exact ⟨c,hc,Relation.ReflTransGen.tail path step⟩

theorem rarePredecessor {D : Dag} {j : ℕ} (path : RarePath D (14+j)) :
    ∃ s : Bool, RarePath D (src D (j,s)) := by
  obtain ⟨c,hc,p⟩ := path
  rcases Relation.ReflTransGen.cases_tail p with eq | ⟨a, pa, last⟩
  · have := c.isLt
    omega
  · obtain ⟨k, side, _, eq, srcEq⟩ := sem_step_iff.mp last
    have jk : j = k := by omega
    subst k
    exact ⟨side,c,hc,srcEq.symm ▸ pa⟩

theorem rareSources {D : Dag} (length : D.length = 27) :
    sources 14 (rareWires D) = rareInputs.image (fun v : Fin 14 => v.val) := by
  classical
  ext w
  simp only [sources, rareWires, mem_filter, mem_image]
  constructor
  · rintro ⟨⟨_, c, hc, runs⟩, hw⟩
    rcases Relation.ReflTransGen.cases_tail runs with eq | ⟨_,_,step⟩
    · exact ⟨c,hc,eq.symm⟩
    · obtain ⟨j,s,hj,eq,which⟩ := sem_step_iff.mp step
      omega
  · rintro ⟨c,hc,rfl⟩
    refine ⟨⟨sb_mem_inner.mpr (by have := c.isLt; omega), c,hc,Relation.ReflTransGen.refl⟩,c.isLt⟩

theorem fiveRareMerges {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (length : D.length = 27) (hi : ineligSet 14 D = rareInputs) (zero : Bzero 14 D = 0) :
    5 ≤ (rareMerges D).card := by
  classical
  let K := rareWires D
  have asMem (w : ℕ) : w ∈ K ↔ w ∈ inner 14 D ∧ RarePath D w := by
    unfold K rareWires
    exact mem_filter
  have sub : K ⊆ inner 14 D := fun w hw => ((asMem w).mp hw).1
  have pred (j : ℕ) (jlt : j < D.length) (kj : 14+j ∈ K) :
      opA D j ∈ K ∨ opB D j ∈ K := by
    obtain ⟨s, path⟩ := rarePredecessor ((asMem _).mp kj).2
    have step := sem_step_src (n:=14) jlt s
    have lt := sem_step_lt h.1 step
    have innerS : src D (j,s) ∈ inner 14 D := sb_mem_inner.mpr (by omega)
    have both := (asMem _).mpr ⟨innerS,path⟩
    cases s
    · exact Or.inl (by simpa [src] using both)
    · exact Or.inr (by simpa [src] using both)
  have flow := carrier_flow h K sub pred
  have sources6 : (sources 14 K).card = 6 := by
    rw [rareSources length, card_image_of_injective _ Fin.val_injective]
    rfl
  have surplus0 : surplusOn D K = 0 := by
    apply sum_eq_zero
    intro w hw
    obtain ⟨c,hc,path⟩ := ((asMem _).mp hw).2
    have cap := (pathWithoutZeroShared h hD zero c (hi ▸ hc) _ path).2
    omega
  rw [sources6,surplus0,Nat.add_zero] at flow
  let root := D.length-1
  have rootEq : 14+root = outW 14 D := by unfold root outW; omega
  have exitSub : exitArcs 14 D K ⊆ ({(root,false),(root,true)} : Finset (ℕ × Bool)) := by
    rintro ⟨j,s⟩ mem
    obtain ⟨arc, srcMem, targetNotMem⟩ := mem_filter.mp mem
    have jlt : j < D.length := mem_range.mp (mem_product.mp arc).1
    have path := rareExtend ((asMem _).mp srcMem).2 (sem_step_src jlt s)
    have atRoot : j = root := by
      by_contra different
      have innerJ : 14+j ∈ inner 14 D := sb_mem_inner.mpr (by dsimp [root] at different; omega)
      exact targetNotMem ((asMem _).mpr ⟨innerJ,path⟩)
    subst j
    cases s <;> simp
  have mergeSub : merges 14 D K ⊆ rareMerges D := by
    intro j hj
    obtain ⟨jlt, _, a,b⟩ := mem_filter.mp hj
    exact mem_filter.mpr ⟨jlt, by simpa [src] using And.intro ((asMem _).mp a).2 ((asMem _).mp b).2⟩
  have pairNe : (root,false) ≠ (root,true) := fun eq => Bool.false_ne_true (congrArg Prod.snd eq)
  have boundExit : (exitArcs 14 D K).card ≤ 2 := by
    have cap := card_le_card exitSub
    rwa [card_pair pairNe] at cap
  have boundMerge := card_le_card mergeSub
  by_cases ex2 : (exitArcs 14 D K).card = 2
  · have exitEq := eq_of_subset_of_card_le exitSub (by rw [ex2,card_pair pairNe])
    have left : (root,false) ∈ exitArcs 14 D K := exitEq ▸ by simp
    have right : (root,true) ∈ exitArcs 14 D K := exitEq ▸ by simp
    have i0 : RarePath D (src D (root,false)) := ((asMem _).mp (mem_filter.mp left).2.1).2
    have i1 : RarePath D (src D (root,true)) := ((asMem _).mp (mem_filter.mp right).2.1).2
    have rootIn : root ∈ rareMerges D := mem_filter.mpr ⟨mem_range.mpr (by dsimp [root]; omega),i0,i1⟩
    have notIn : root ∉ merges 14 D K := fun seen =>
      (mem_filter.mp left).2.2 (mem_filter.mp seen).2.1
    have bigger : insert root (merges 14 D K) ⊆ rareMerges D := insert_subset rootIn mergeSub
    have count := card_le_card bigger
    rw [card_insert_of_notMem notIn] at count
    omega
  · omega
theorem rarePathAtRaw {D : Dag} {w : ℕ} (small : w < 14) (rare : RarePath D w) :
    (⟨w,small⟩ : Fin 14) ∈ rareInputs := by
  obtain ⟨c,hc,p⟩ := rare
  rcases Relation.ReflTransGen.cases_tail p with eq | ⟨_,_,step⟩
  · exact (show (⟨w,small⟩ : Fin 14) = c from Fin.ext eq).symm ▸ hc
  · obtain ⟨j,s,hj,eq,source⟩ := sem_step_iff.mp step
    omega

theorem injectionExists {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hi : ineligSet 14 D = rareInputs) (zero : Bzero 14 D = 0)
    (p : Fin 14) (ep : Adj exceptional p) :
    ∃ j, j < D.length ∧ tag D j = false ∧
      ∃ s : Bool, RarePath D (src D (j,!s)) ∧ ¬ RarePath D (src D (j,s)) ∧
        val D (sem_two exceptional p) (src D (j,s)) = true ∧
        val D (sem_ind majority) (src D (j,s)) = false := by
  classical
  let x := sem_two exceptional p
  have ex : ∃ w, RarePath D w ∧ val D x w = true := by
    have r : RarePath D (outW 14 D) :=
      ⟨0,by decide +kernel,live_reaches_out h 0 (by omega)⟩
    exact ⟨_,r,(sem_heawood_comp hD x).mpr (sem_two_edge ep)⟩
  let w := Nat.find ex
  obtain ⟨rare, trueAt⟩ := Nat.find_spec ex
  change RarePath D w at rare
  change val D x w = true at trueAt
  have notRaw : 14 ≤ w := by
    by_contra! small
    have hr := rarePathAtRaw small rare
    have rawOff : x ⟨w,small⟩ = false := by
      have distinct := (by decide +kernel : ∀ p : Fin 14, Adj exceptional p →
        ∀ v ∈ rareInputs, v ≠ exceptional ∧ v ≠ p) p ep ⟨w,small⟩ hr
      simp [x,sem_two,distinct.1,distinct.2]
    have atW := val_input D x w small
    rw [rawOff] at atW
    exact Bool.false_ne_true (atW.symm.trans trueAt)
  have inRange : w < 14+D.length := by
    by_contra! outside
    exact Bool.false_ne_true ((val_ge D x w outside).symm.trans trueAt)
  let j := w-14
  have hj : j < D.length := by dsimp [j]; omega
  have eq : 14+j = w := by dsimp [j]; omega
  have offBefore (s : Bool) (path : RarePath D (src D (j,s))) :
      val D x (src D (j,s)) = false := by
    by_contra! notFalse
    have less : src D (j,s) < w := eq ▸ sem_src_lt h.1 hj s
    have yes : val D x (src D (j,s)) = true := by
      cases v : val D x (src D (j,s)) <;> simp [v] at notFalse ⊢
    exact Nat.find_min ex less ⟨path, yes⟩
  obtain ⟨s,sRare⟩ := rarePredecessor (eq.symm ▸ rare)
  have sOff := offBefore s sRare
  have here : val D x (14+j) = true := eq.symm ▸ trueAt
  have orGate : tag D j = false := by
    by_contra! andGate
    have atAnd : tag D j = true := by cases y : tag D j <;> simp [y] at andGate ⊢
    rw [sem_val_gate_src h.1 x hj s, atAnd, gop_true, sOff] at here
    contradiction
  have otherOn : val D x (src D (j,!s)) = true := by
    rwa [sem_val_gate_src h.1 x hj s, orGate, gop_false, sOff] at here
  have otherNot : ¬ RarePath D (src D (j,!s)) := fun rr =>
    Bool.false_ne_true ((offBefore (!s) rr).symm.trans otherOn)
  obtain ⟨c,hc,cPath⟩ := sRare
  have gatePath := Relation.ReflTransGen.tail cPath (sem_step_src hj s)
  have gateOff := (rareGateOffOn h hD hi zero hc _ gatePath).1
  have otherOff : val D (sem_ind majority) (src D (j,!s)) = false := by
    rw [sem_val_gate_src h.1 _ hj s, orGate, gop_false, Bool.or_eq_false_iff] at gateOff
    exact gateOff.2
  exact ⟨j,hj,orGate,!s,by simpa using (show RarePath D (src D (j,s)) from ⟨c,hc,cPath⟩),otherNot,otherOn,otherOff⟩
theorem injectionSourceComputed {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hi : ineligSet 14 D = rareInputs) (zero : Bzero 14 D = 0) (j : ℕ)
    (hj : j < D.length) (op : tag D j = false) (s : Bool)
    (other : RarePath D (src D (j,!s))) (pure : ¬ RarePath D (src D (j,s)))
    (off : val D (sem_ind majority) (src D (j,s)) = false) :
    14 ≤ src D (j,s) := by
  by_contra! small
  let v : Fin 14 := ⟨src D (j,s),small⟩
  have notR : v ∉ rareInputs := fun hv => pure ⟨v,hv,Relation.ReflTransGen.refl⟩
  have notP : v ∉ majority := by
    intro pv
    rw [val_input D _ _ small] at off
    have t : sem_ind majority v = true := by simp [sem_ind,pv]
    exact Bool.false_ne_true (off.symm.trans t)
  have eq := (by decide +kernel : ∀ v : Fin 14, v ∉ rareInputs → v ∉ majority →
    v = exceptional) v notR notP
  obtain ⟨c,hc,path⟩ := other
  have links := Relation.ReflTransGen.tail path (sem_step_src hj (!s))
  have chain := (pathWithoutZeroShared h hD zero c (hi ▸ hc) _ links).1
  exact pureRawOrInjectionImpossible h hD hc j hj op s (congrArg Fin.val eq) chain

noncomputable def largeGates (D : Dag) : Finset ℕ := by
  classical
  exact (range D.length).filter (fun j => 2 ≤ (projection D (14+j)).card)

theorem bigSubsetLarge (D : Dag) : sup_big 14 D majority ⊆ largeGates D := by
  intro w hw
  obtain ⟨hm,size⟩ := mem_filter.mp hw
  exact mem_filter.mpr ⟨(mem_filter.mp hm).1,size⟩

theorem largeProjectionCount {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (length : D.length = 27) (hi : ineligSet 14 D = rareInputs) :
    14 ≤ ((largeGates D).image (fun j => projection D (14+j))).card :=
  (fourteenProjectedValues h hD length hi).trans (card_le_card (image_subset_image (bigSubsetLarge D)))

structure P8Layout (D : Dag) where
  anchor : Fin 14 → ℕ
  anchorOk : ∀ c ∈ rareInputs, RareAnchor D c (anchor c)
  injectGate : ℕ
  injectSide : Bool
  injectLt : injectGate < D.length
  injectOr : tag D injectGate = false
  injectRare : RarePath D (src D (injectGate,!injectSide))
  seed : ℕ
  seedInput : src D (injectGate,injectSide) = 14+seed
  seedLt : seed < D.length
  seedPure : ¬ RarePath D (14+seed)
  seedOff : val D (sem_ind majority) (14+seed) = false
  largeUnique : Set.InjOn (fun j => projection D (14+j)) (largeGates D)
  covers : ∀ j, j < D.length →
    j ∈ largeGates D ∨ (∃ c ∈ rareInputs, anchor c = j) ∨
    j ∈ rareMerges D ∨ j = injectGate ∨ j = seed

theorem p8LayoutExists {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (length : D.length = 27) (hi : ineligSet 14 D = rareInputs) (zero : Bzero 14 D = 0)
    (p : Fin 14) (ep : Adj exceptional p) : Nonempty (P8Layout D) := by
  classical
  obtain ⟨j,hj,op,s,jRare,tPure,_,tOff⟩ := injectionExists h hD hi zero p ep
  let t := src D (j,s)-14
  have notRaw := injectionSourceComputed h hD hi zero j hj op s jRare tPure tOff
  have teq : src D (j,s) = 14+t := by dsimp [t]; omega
  have tlt : t < D.length := by
    have bound := sem_src_lt h.1 hj s
    omega
  rw [teq] at tPure tOff
  have tProject : projection D (14+t) = ∅ := by
    apply eq_empty_of_forall_notMem
    intro v hv
    obtain ⟨a,b⟩ := mem_inter.mp hv
    have on := sem_val_of_supp h.1 a (x := sem_ind majority) (by simp [sem_ind,b])
    rw [tOff] at on
    contradiction
  choose! a aOk using (fun c hc => hasRareAnchor h hD hi zero (c := c) hc)
  let A := rareInputs.image a
  let L := largeGates D
  let R := rareMerges D
  have ra (k : ℕ) (mem : k ∈ A) : RarePath D (14+k) := by
    obtain ⟨c,hc,rfl⟩ := mem_image.mp mem
    obtain ⟨hk,_,u,cp,_⟩ := aOk c hc
    exact ⟨c,hc,Relation.ReflTransGen.tail cp (sem_step_src hk (!u))⟩
  have rr (k : ℕ) (mem : k ∈ R) : RarePath D (14+k) :=
    rareExtend (mem_filter.mp mem).2.1 (sem_step_src (mem_range.mp (mem_filter.mp mem).1) false)
  have rj : RarePath D (14+j) := rareExtend jRare (sem_step_src hj (!s))
  have alo (k : ℕ) (mem : k ∈ A) : k < D.length := by
    obtain ⟨c,hc,rfl⟩ := mem_image.mp mem
    exact (aOk c hc).1
  have aAnd (k : ℕ) (mem : k ∈ A) : tag D k = true := by
    obtain ⟨c,hc,rfl⟩ := mem_image.mp mem
    exact (aOk c hc).2.1
  have rOr (k : ℕ) (mem : k ∈ R) : tag D k = false := by
    obtain ⟨kl,pl,pr⟩ := mem_filter.mp mem
    exact rareMergeIsOr h hD hi zero k (mem_range.mp kl) pl pr
  have largeNonrare (k : ℕ) (mem : k ∈ L) : ¬ RarePath D (14+k) := by
    intro path
    have eq := rarePathProjectedEmpty h hD hi zero _ path
    have lower := (mem_filter.mp mem).2
    rw [eq, card_empty] at lower
    omega
  have aSix : A.card = 6 := by
    have inj : Set.InjOn a rareInputs := by
      intro c hc d hd eq
      exact rareAnchorOnlyPath h hD hi zero hc hd (aOk c hc)
        (by
          obtain ⟨r,s,side,path,z⟩ := aOk d hd
          exact eq.symm ▸ Relation.ReflTransGen.tail path (sem_step_src r (!side)))
    rw [show A = rareInputs.image a from rfl, card_image_of_injOn inj]
    rfl
  have rFive : 5 ≤ R.card := fiveRareMerges h hD length hi zero
  have disLR : Disjoint L R := disjoint_left.mpr (fun k lk rk => largeNonrare k lk (rr k rk))
  have disLA : Disjoint L A := disjoint_left.mpr (fun k lk ak => largeNonrare k lk (ra k ak))
  have disRA : Disjoint R A := disjoint_left.mpr (fun k rk ak =>
    Bool.false_ne_true ((rOr k rk).symm.trans (aAnd k ak)))
  let F := (L ∪ R) ∪ A
  have fc : F.card = L.card + R.card + A.card := by
    dsimp [F]
    rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨disLA,disRA⟩),card_union_of_disjoint disLR]
  have jNot : j ∉ F := by
    intro m
    rcases mem_union.mp m with lr | am
    · rcases mem_union.mp lr with lm | rm
      · exact largeNonrare _ lm rj
      · obtain ⟨_, q0,q1⟩ := mem_filter.mp rm
        cases s
        · exact tPure (teq ▸ q0)
        · exact tPure (teq ▸ q1)
    · exact Bool.false_ne_true (op.symm.trans (aAnd _ am))
  have tNot : t ∉ F := by
    intro m
    rcases mem_union.mp m with lr | am
    · rcases mem_union.mp lr with lm | rm
      · have many := (mem_filter.mp lm).2
        rw [tProject,card_empty] at many
        omega
      · exact tPure (rr _ rm)
    · exact tPure (ra _ am)
  have tj : t ≠ j := fun eq => tPure (eq.symm ▸ rj)
  have fit : insert t (insert j F) ⊆ range D.length := by
    intro k hk
    rcases mem_insert.mp hk with rfl | hk
    · exact mem_range.mpr tlt
    rcases mem_insert.mp hk with rfl | hk
    · exact mem_range.mpr hj
    rcases mem_union.mp hk with lr | am
    · rcases mem_union.mp lr with lm | rm
      · exact (mem_filter.mp lm).1
      · exact (mem_filter.mp rm).1
    · exact mem_range.mpr (alo _ am)
  have cardFull : (insert t (insert j F)).card = L.card + R.card + 8 := by
    rw [card_insert_of_notMem (fun m => (mem_insert.mp m).elim tj tNot),
        card_insert_of_notMem jNot,fc,aSix]
  have slots := card_le_card fit
  rw [cardFull,card_range,length] at slots
  have many := largeProjectionCount h hD length hi
  have few : (L.image (fun k => projection D (14+k))).card ≤ L.card := card_image_le
  have exactProj : (L.image (fun k => projection D (14+k))).card = L.card := by
    change 14 ≤ (L.image _).card at many
    omega
  have all : insert t (insert j F) = range D.length := by
    apply eq_of_subset_of_card_le fit
    rw [cardFull,card_range,length]
    change 14 ≤ (L.image _).card at many
    omega
  refine ⟨⟨a,aOk,j,s,hj,op,jRare,t,teq,tlt,tPure,tOff,card_image_iff.mp exactProj,?_⟩⟩
  intro k kl
  have mem : k ∈ insert t (insert j F) := all ▸ mem_range.mpr kl
  rcases mem_insert.mp mem with rfl | km
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  rcases mem_insert.mp km with rfl | km
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases mem_union.mp km with lr | am
  · rcases mem_union.mp lr with lm | rm
    · exact Or.inl lm
    · exact Or.inr (Or.inr (Or.inl rm))
  · exact Or.inr (Or.inl (mem_image.mp am))
theorem projectionAnd {D : Dag} (h : Strict 14 D) {j : ℕ} (hj : j < D.length)
    (op : tag D j = true) (s : Bool) :
    projection D (14+j) = projection D (src D (j,s)) ∩ projection D (src D (j,!s)) := by
  ext v
  unfold projection
  rw [sem_supp_and h hj op]
  cases s <;> simp [src] <;> tauto

theorem projectionOr {D : Dag} (h : Strict 14 D) {j : ℕ} (hj : j < D.length)
    (op : tag D j = false) (s : Bool) :
    projection D (14+j) = projection D (src D (j,s)) ∪ projection D (src D (j,!s)) := by
  ext v
  unfold projection
  rw [sem_supp_or h hj op]
  cases s <;> simp [src] <;> tauto

theorem pointProjection {D : Dag} (p : Fin 14) (hp : p ∈ majority) :
    projection D p.val = {p} := by
  simp [projection, supp_input, hp]

theorem exceptionalProjection (D : Dag) : projection D exceptional.val = ∅ := by
  have excl : exceptional ∉ majority := by decide +kernel
  rw [projection, show supp 14 D exceptional.val = {exceptional} from supp_input D exceptional]
  simp [excl]

theorem layoutSeedProjection {D : Dag} (h : Strict 14 D) (layout : P8Layout D) :
    projection D (14+layout.seed) = ∅ := by
  apply eq_empty_of_forall_notMem
  intro v hv
  obtain ⟨inS,inP⟩ := mem_inter.mp hv
  have on := sem_val_of_supp h inS (x := sem_ind majority) (by simp [sem_ind,inP])
  exact Bool.false_ne_true (layout.seedOff.symm.trans on)

theorem layoutPureWire {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hi : ineligSet 14 D = rareInputs) (zero : Bzero 14 D = 0)
    (layout : P8Layout D) (w : ℕ) (lt : w < 14+D.length) (nr : ¬ RarePath D w) :
    (∃ p ∈ majority, w = p.val) ∨ w = exceptional.val ∨
      (∃ k ∈ largeGates D, w = 14+k) ∨ w = 14+layout.seed := by
  classical
  by_cases raw : w < 14
  · let v : Fin 14 := ⟨w,raw⟩
    have notRare : v ∉ rareInputs := fun r => nr ⟨v,r,Relation.ReflTransGen.refl⟩
    have cover := (by decide +kernel : ∀ v : Fin 14, v ∉ rareInputs →
      v ∈ majority ∨ v = exceptional) v notRare
    rcases cover with m | e
    · exact Or.inl ⟨v,m,rfl⟩
    · exact Or.inr (Or.inl (congrArg Fin.val e))
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, w = 14+k := ⟨w-14,by omega⟩
    have kl : k < D.length := by omega
    rcases layout.covers k kl with lg | ⟨c,hc,eq⟩ | merge | i | t
    · exact Or.inr (Or.inr (Or.inl ⟨k,lg,rfl⟩))
    · obtain ⟨hj, _, s, path, _⟩ := layout.anchorOk c hc
      exact (nr (eq ▸ ⟨c,hc,Relation.ReflTransGen.tail path (sem_step_src hj (!s))⟩)).elim
    · exact (nr (rareExtend (mem_filter.mp merge).2.1 (sem_step_src kl false))).elim
    · exact (nr (i.symm ▸ rareExtend layout.injectRare (sem_step_src layout.injectLt (!layout.injectSide)))).elim
    · exact Or.inr (Or.inr (Or.inr (by rw [t])))

theorem largeGatePureInputs {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hi : ineligSet 14 D = rareInputs) (zero : Bzero 14 D = 0)
    (layout : P8Layout D) {j : ℕ} (jl : j ∈ largeGates D) (s : Bool) :
      (∃ p ∈ majority, src D (j,s) = p.val) ∨
      ∃ k ∈ largeGates D, src D (j,s) = 14+k := by
  have jlt := mem_range.mp (mem_filter.mp jl).1
  have pl : 2 ≤ (projection D (14+j)).card := (mem_filter.mp jl).2
  have pure : ¬ RarePath D (14+j) := by
    intro ra
    rw [rarePathProjectedEmpty h hD hi zero _ ra,card_empty] at pl
    omega
  have usable (d : Bool) : ¬ RarePath D (src D (j,d)) :=
    fun path => pure (rareExtend path (sem_step_src jlt d))
  have packed (d : Bool) := layoutPureWire h hD hi zero layout _ (by
    have := sem_src_lt h.1 jlt d; omega) (usable d)
  have zeroImpossible (bad : projection D (src D (j,s)) = ∅) : False := by
    cases op : tag D j
    · have eq := projectionOr h.1 jlt op s
      rw [bad,empty_union] at eq
      have otherLarge : 2 ≤ (projection D (src D (j,!s))).card := eq ▸ pl
      rcases packed (!s) with ⟨p,hp,eqp⟩ | ee | ⟨k,hk,e⟩ | tt
      · rw [eqp,pointProjection p hp,card_singleton] at otherLarge
        omega
      · rw [ee,exceptionalProjection,card_empty] at otherLarge
        omega
      · have same : j = k := layout.largeUnique jl hk (eq.trans (congrArg (projection D) e))
        have lt := sem_src_lt h.1 jlt (!s)
        omega
      · rw [tt,layoutSeedProjection h.1 layout,card_empty] at otherLarge
        omega
    · rw [projectionAnd h.1 jlt op s,bad,empty_inter,card_empty] at pl
      omega
  rcases packed s with point | e | big | t
  · exact Or.inl point
  · exact (zeroImpossible (e.symm ▸ exceptionalProjection D)).elim
  · exact Or.inr big
  · exact (zeroImpossible (t.symm ▸ layoutSeedProjection h.1 layout)).elim

theorem largeDoesNotReadExceptional {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hi : ineligSet 14 D = rareInputs) (zero : Bzero 14 D = 0)
    (layout : P8Layout D) (x y : Fin 14 → Bool)
    (agree : ∀ v : Fin 14, v ≠ exceptional → x v = y v) :
    ∀ j ∈ largeGates D, val D x (14+j) = val D y (14+j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro jl
    have jl' := mem_range.mp (mem_filter.mp jl).1
    have valSame (s : Bool) : val D x (src D (j,s)) = val D y (src D (j,s)) := by
      rcases largeGatePureInputs h hD hi zero layout jl s with ⟨p,hp,eq⟩ | ⟨k,kl,eq⟩
      · have ex : p ≠ exceptional := by
          intro eq
          subst p
          exact (by decide +kernel : exceptional ∉ majority) hp
        rw [eq,val_input D x _ p.isLt,val_input D y _ p.isLt,agree p ex]
      · have less := sem_src_lt h.1 jl' s
        rw [eq]
        exact ih k (by omega) kl
    rw [sem_val_gate_src h.1 x jl' false,sem_val_gate_src h.1 y jl' false,valSame false,valSame (!false)]
theorem p8NoExceptionalAndSwitch {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (length : D.length = 27) (hi : ineligSet 14 D = rareInputs)
    (p : Fin 14) (ep : Adj exceptional p)
    (x y : Fin 14 → Bool) (agree : ∀ v : Fin 14, v ≠ exceptional → x v = y v)
    (j : ℕ) (hj : j < D.length) (andGate : tag D j = true) :
    ∃ s : Bool, val D x (src D (j,s)) = val D y (src D (j,s)) := by
  classical
  have q : (eligSet 14 D).card = 8 := by
    have ic := inelig_card_add 14 D
    rw [hi,show rareInputs.card=6 from rfl] at ic
    omega
  have zero := (smallEligibleGeometry h hD length q.le).1
  obtain ⟨l⟩ := p8LayoutExists h hD length hi zero p ep
  have lg := largeDoesNotReadExceptional h hD hi zero l x y agree
  have same (w : ℕ) :
      ((∃ v ∈ majority, w = v.val) ∨ ∃ k ∈ largeGates D, w = 14+k) →
        val D x w = val D y w := by
    rintro (⟨v,hv,rfl⟩ | ⟨k,hk,rfl⟩)
    · have ne : v ≠ exceptional := by
        intro eq
        exact (by decide +kernel : exceptional ∉ majority) (eq ▸ hv)
      rw [val_input D x _ v.isLt, val_input D y _ v.isLt, agree v ne]
    · exact lg k hk
  rcases l.covers j hj with major | ⟨c,hc,ae⟩ | merge | inj | seed
  · exact ⟨false, same _ (largeGatePureInputs h hD hi zero l major false)⟩
  · obtain ⟨ak, ao, s, chain, proj⟩ := l.anchorOk c hc
    rw [ae] at ak ao chain proj
    have support : 2 ≤ (projection D (src D (j,s))).card := by
      have card : (sem_hw_nb c).card = 3 := degree_three c
      rw [proj,card]
      decide
    have pure : ¬ RarePath D (src D (j,s)) := by
      intro path
      rw [rarePathProjectedEmpty h hD hi zero _ path,card_empty] at support
      omega
    have lt := sem_src_lt h.1 hj s
    rcases layoutPureWire h hD hi zero l _ (by omega) pure with point | e | big | t
    · obtain ⟨v,hv,eq⟩ := point
      rw [eq,pointProjection v hv,card_singleton] at support
      omega
    · rw [e,exceptionalProjection,card_empty] at support
      omega
    · exact ⟨s, same _ (Or.inr big)⟩
    · rw [t,layoutSeedProjection h.1 l,card_empty] at support
      omega
  · obtain ⟨_,left,right⟩ := mem_filter.mp merge
    exact (Bool.false_ne_true ((rareMergeIsOr h hD hi zero j hj left right).symm.trans andGate)).elim
  · exact (Bool.false_ne_true (l.injectOr.symm.trans (inj ▸ andGate))).elim
  · subst j
    have noBoth : ∃ s : Bool, src D (l.seed,s) ≠ exceptional.val := by
      by_cases first : src D (l.seed,false) = exceptional.val
      · refine ⟨true,?_⟩
        intro second
        exact sem_src_ne h.1 hj false (first.trans second.symm)
      · exact ⟨false,first⟩
    obtain ⟨s,ne⟩ := noBoth
    have pure : ¬ RarePath D (src D (l.seed,s)) :=
      fun path => l.seedPure (rareExtend path (sem_step_src hj s))
    have lt := sem_src_lt h.1 hj s
    rcases layoutPureWire h hD hi zero l _ (by omega) pure with point | e | big | t
    · exact ⟨s,same _ (Or.inl point)⟩
    · exact (ne e).elim
    · exact ⟨s,same _ (Or.inr big)⟩
    · omega
def hasAndDoubleSwitch (D : Dag) (u : Fin 14) : Prop :=
  ∃ (x y : Fin 14 → Bool) (j : ℕ), j < D.length ∧ tag D j = true ∧
    (∀ v, v ≠ u → x v = y v) ∧
    ∀ s : Bool, val D x (src D (j,s)) ≠ val D y (src D (j,s))

theorem toDoubleSwitch {D : Dag} {u : Fin 14} (h : hasAndDoubleSwitch D u) :
    hasDoubleSwitch D u := by
  obtain ⟨x,y,j,hj,_,agree,switches⟩ := h
  exact ⟨x,y,j,hj,agree,switches⟩

theorem relabelAndSwitch (σ : Equiv.Perm (Fin 14)) {D : Dag} (h : Strict 14 D)
    {u : Fin 14} (switch : hasAndDoubleSwitch D u) : hasAndDoubleSwitch (relabel σ D) (σ u) := by
  obtain ⟨x,y,j,hj,tagj,agree,sw⟩ := switch
  let xx : Fin 14 → Bool := fun v => x (σ.symm v)
  let yy : Fin 14 → Bool := fun v => y (σ.symm v)
  refine ⟨xx,yy,j,by rwa [relabel_length],by rwa [tr_tag σ D j hj],?_,?_⟩
  · intro v ne
    apply agree
    intro eq
    exact ne (by rw [← eq]; simp)
  · intro s
    have operand : src (relabel σ D) (j,s) = liftP σ (src D (j,s)) := by
      cases s
      · simp [src,tr_opA σ D j hj]
      · simp [src,tr_opB σ D j hj]
    rw [operand,relabel_val σ h,relabel_val σ h]
    simpa [xx,yy] using sw s

theorem doubleAndSwitchNine {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (length : D.length = 27) (u v : Fin 14) (uv : Adj u v)
    (a : hasAndDoubleSwitch D u) (b : hasAndDoubleSwitch D v) :
    9 ≤ (eligSet 14 D).card := by
  classical
  have eight := (doubleSwitchGeometry h hD length u v uv (toDoubleSwitch a) (toDoubleSwitch b)).1
  by_contra! much
  have eqEight : (eligSet 14 D).card = 8 := by omega
  obtain ⟨zero,σ,aut,geom⟩ := smallEligibleGeometry h hD length (by omega)
  obtain ⟨hn,hDn,lenE,_,_,_,eqE,_⟩ := heawood_relabel σ aut h hD
  let E := relabel σ D
  have coordinates : ∀ w : Fin 14, w ∈ eligSet 14 E ↔ 6 ≤ w.val := by
    intro w
    rw [eqE,mem_image]
    constructor
    · rintro ⟨t,ht,rfl⟩
      have lo := (geom t).mp ht
      rw [eqEight] at lo
      exact lo
    · intro lo
      refine ⟨σ.symm w, (geom _).mpr ?_,by simp⟩
      rwa [eqEight,Equiv.apply_symm_apply]
  have rareEq : ineligSet 14 E = rareInputs := by
    ext w
    rw [sem_mem_inelig,coordinates]
    simpa [not_le] using
      (by decide +kernel : ∀ w : Fin 14, w.val < 6 ↔ w ∈ rareInputs) w
  have eligible (t : Fin 14) (sw : hasAndDoubleSwitch D t) : t ∈ eligSet 14 D := by
    obtain ⟨x,y,j,hj,_,same,switches⟩ := sw
    exact switchedOperandsEligible h hD zero t x y same j hj switches
  have aLo := (coordinates (σ u)).mp (by
    rw [eqE]
    exact mem_image_of_mem σ (eligible u a))
  have bLo := (coordinates (σ v)).mp (by
    rw [eqE]
    exact mem_image_of_mem σ (eligible v b))
  have adjE := (aut u v).mpr uv
  have either := (by decide +kernel : ∀ p q : Fin 14, Adj p q → 6 ≤ p.val → 6 ≤ q.val →
    p = exceptional ∨ q = exceptional) (σ u) (σ v) adjE aLo bLo
  have impossible (other : Fin 14) (edge : Adj exceptional other)
      (switch : hasAndDoubleSwitch E exceptional) : False := by
    obtain ⟨x,y,j,hj,tagj,agree,switches⟩ := switch
    obtain ⟨s,solid⟩ := p8NoExceptionalAndSwitch hn hDn (lenE.trans length) rareEq
      other edge x y agree j hj tagj
    exact switches s solid
  rcases either with here | there
  · have sw := relabelAndSwitch σ h.1 a
    rw [here] at sw adjE
    exact impossible (σ v) adjE sw
  · have sw := relabelAndSwitch σ h.1 b
    rw [there] at sw adjE
    exact impossible (σ u) (adj_symm adjE) sw
end NestedFano.SolReview









