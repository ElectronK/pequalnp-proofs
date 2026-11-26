import FanoOrdinary

namespace NestedFano.SolReview

open PEqualNP.Outside.L_meta_17808 Finset

noncomputable def zeroBranches (D : Dag) : Finset ℕ :=
  (inner 14 D).filter (fun w => 2 ≤ fanout D w ∧ ¬ (supp 14 D w).Nonempty)

theorem mem_zeroBranches {D : Dag} {w : ℕ} (h : Strict 14 D) :
    w ∈ zeroBranches D ↔ 2 ≤ fanout D w ∧ supp 14 D w = ∅ := by
  classical
  constructor
  · intro hw
    have m := (mem_filter.mp hw).2
    exact ⟨m.1, not_nonempty_iff_eq_empty.mp m.2⟩
  · rintro ⟨f, empty⟩
    exact mem_filter.mpr ⟨sb_mem_inner.mpr (lt_of_fanout_pos h (by omega)), f, by simp [empty]⟩

theorem zeroBranches_le_surplus {D : Dag} (h : Strict 14 D) :
    (zeroBranches D).card ≤ Bzero 14 D :=
  bz_card h _ (fun _ hw => (mem_zeroBranches h).mp hw)

theorem zeroBranch_fanout_two {D : Dag} (h : Strict 14 D)
    (tight : Bzero 14 D = (zeroBranches D).card) (w : ℕ)
    (f : 2 ≤ fanout D w) (empty : supp 14 D w = ∅) : fanout D w = 2 := by
  classical
  have mem := (mem_zeroBranches h).mpr ⟨f, empty⟩
  have bound : ((zeroBranches D).erase w).card ≤
      ∑ v ∈ (zeroBranches D).erase w, (fanout D v - 1) := by
    simpa using sum_le_sum (f := fun _ : ℕ => (1 : ℕ)) (fun v hv => by
      have df := ((mem_zeroBranches h).mp (mem_erase.mp hv).2).1
      omega)
  have count := card_erase_add_one mem
  have sumEq := sum_erase_add (f := fun v => fanout D v - 1) _ mem
  have incl : zeroBranches D ⊆ (inner 14 D).filter (fun w => ¬ (supp 14 D w).Nonempty) := by
    intro v hv
    obtain ⟨a, b⟩ := (mem_zeroBranches h).mp hv
    exact sem_bzero_mem h a b
  have sub := sum_le_sum_of_subset (f := fun v => fanout D v - 1) incl
  change _ ≤ Bzero 14 D at sub
  omega

theorem missedSharedInjection {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (P : Finset (Fin 14))
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ Adj a b) (J : Finset (Fin 14))
    (hJ : ∀ i ∈ J, i ∈ ineligSet 14 D ∧ sem_hw_nb i ⊆ P ∧ ¬ sup_Occ 14 D P (sem_hw_nb i))
    : ∃ β : Fin 14 → ℕ,
      (∀ i ∈ J, sem_Chain 14 D i.val (β i) ∧
        2 ≤ fanout D (β i) ∧ supp 14 D (β i) = ∅) ∧ Set.InjOn β J := by
  classical
  have hG := sem_heawood_gr
  have hC := sem_heawood_comp hD
  have hocc : ∀ i ∈ J, ∀ q, (∀ a ∈ P, (a ∈ supp 14 D q ↔ Adj i a)) → False := by
    intro i hi q hq
    refine (hJ i hi).2.2 ⟨q, ?_⟩
    ext a
    rw [mem_inter, hw_mem_nb]
    exact ⟨fun h1 => (hq a h1.2).1 h1.1,
      fun h1 => ⟨(hq a ((hJ i hi).2.1 (hw_mem_nb.2 h1))).2 h1, (hJ i hi).2.1 (hw_mem_nb.2 h1)⟩⟩
  have hb : ∀ i ∈ J, ∃ b, sem_Chain 14 D i.val b ∧ 2 ≤ fanout D b ∧ supp 14 D b = ∅ := by
    intro i hi
    rcases sem_inelig_reach hG h hC (hJ i hi).1 with hch | hb
    · obtain ⟨j, s, -, -, -, hq⟩ := sem_exact_nbhd hG h.1 hC P hP hch
      exact (hocc i hi _ hq).elim
    · exact hb

  choose! β hβ using hb
  have inj : Set.InjOn β J := by
    intro i hi j hj eq
    by_contra ne
    obtain ⟨x, ha, hx⟩ := nbr_diff_exists j i (Ne.symm ne)
    obtain ⟨k, s, -, -, -, -, hq⟩ := sem_shared_exact hG h.1 hC P hP (hβ i hi).1
      (sem_chain_dom h.1 (eq ▸ (hβ j hj).1)) ⟨x, (hJ j hj).2.1 (hw_mem_nb.2 ha), ha, hx⟩
    exact hocc i hi _ hq
  exact ⟨β,hβ,inj⟩

theorem missedSharedCount {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (P : Finset (Fin 14))
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ Adj a b) (J : Finset (Fin 14))
    (hJ : ∀ i ∈ J, i ∈ ineligSet 14 D ∧ sem_hw_nb i ⊆ P ∧ ¬ sup_Occ 14 D P (sem_hw_nb i))
    : J.card ≤ (zeroBranches D).card := by
  classical
  obtain ⟨β,hβ,inj⟩ := missedSharedInjection h hD P hP J hJ
  rw [← card_image_of_injOn inj]
  apply card_le_card
  intro w hw
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hw
  exact (mem_zeroBranches h.1).mpr (hβ i hi).2

noncomputable def missingNeighborhoods (D : Dag) : Finset (Fin 7) := by
  classical
  exact univ.filter (fun k : Fin 7 => ¬ sup_Occ 14 D (sem_hw_opp 0) (sem_hw_nb (os_pt k)))

theorem oneSideExactMissingAccounting {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (budget : totalSurplus 14 D = 14) (Iq : Finset (Fin 7)) (qmin : 4 ≤ Iq.card)
    (hI : ineligSet 14 D = Iq.image os_pt)
    : let M := missingNeighborhoods D
      M.card ≤ (zeroBranches D).card + (7 - Iq.card) ∧
      Bzero 14 D + ((M.image os_pt).biUnion (fun c => sem_hw_nb c ∩ sem_hw_opp 0)).card
        ≤ 2*M.card := by
  classical
  let q := Iq.card
  have qmax : q ≤ 7 := (card_le_univ Iq).trans (by decide)
  have hPe : sem_hw_opp 0 ⊆ eligSet 14 D := by
    intro a ha
    by_contra hne
    have am := sem_mem_inelig.2 hne
    rw [hI] at am
    obtain ⟨k, -, rfl⟩ := mem_image.mp am
    have small : (os_pt k).val < 7 := k.isLt
    simp only [sem_hw_opp, mem_filter, mem_univ, true_and] at ha
    have large : ¬ (os_pt k).val < 7 := by simpa using ha
    omega
  let Oc := univ.filter (fun k : Fin 7 => sup_Occ 14 D (sem_hw_opp 0) (sem_hw_nb (os_pt k)))
  let Mi := univ.filter (fun k : Fin 7 => ¬ sup_Occ 14 D (sem_hw_opp 0) (sem_hw_nb (os_pt k)))
  have hIq : ∀ k ∈ Iq, os_pt k ∈ ineligSet 14 D := fun k hk => hI ▸ mem_image_of_mem os_pt hk
  have hcnt := hw_count h hD (sem_hw_opp 0) (Subset.refl _) hPe (Oc.image os_pt)
    (Mi.image os_pt) (Iq.image os_pt)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := mem_image.1 hi
      exact ⟨os_nb_sub k, (mem_filter.1 hk).2⟩)
    (fun c hc => by
      obtain ⟨k, hk, rfl⟩ := mem_image.1 hc
      refine ⟨fun hc' => ?_, Or.inr ⟨os_nb_sub k, (mem_filter.1 hk).2⟩⟩
      obtain ⟨k', hk', hkk⟩ := mem_image.1 hc'
      rw [os_pt_inj hkk] at hk'
      exact (mem_filter.1 hk).2 (mem_filter.1 hk').2)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := mem_image.1 hi
      exact ⟨hIq k hk, os_nb_sub k⟩)
  have hlost := missedSharedCount h hD (sem_hw_opp 0) (sem_hw_opp_indep 0) ((Mi ∩ Iq).image os_pt)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := mem_image.1 hi
      have hm := mem_inter.1 hk
      exact ⟨hIq k hm.2, os_nb_sub k, (mem_filter.1 hm.1).2⟩)
  rw [card_image_of_injective _ os_pt_inj] at hlost
  rw [card_image_of_injective _ os_pt_inj, card_image_of_injective _ os_pt_inj] at hcnt
  have hsplit : Oc.card + Mi.card = 7 := by
    simpa using card_filter_add_card_filter_not (s := (univ : Finset (Fin 7)))
      (fun k => sup_Occ 14 D (sem_hw_opp 0) (sem_hw_nb (os_pt k)))
  have hcq : Iq.card = q := rfl
  have hMI : Mi.card ≤ (Mi ∩ Iq).card + (7 - q) := by
    have eq := card_inter_add_card_sdiff Mi Iq
    have cap := card_le_card (sdiff_subset_sdiff (subset_univ Mi) (Subset.refl Iq))
    rw [card_univ_sdiff, hcq, Fintype.card_fin] at cap
    omega
  have P7 : (sem_hw_opp 0).card = 7 := by decide
  have hel := inelig_card_add 14 D
  have hiq : (ineligSet 14 D).card = q := by
    rw [hI, card_image_of_injective _ os_pt_inj, hcq]
  have split := totalSurplus_split 14 D

  rw [P7, hcq] at hcnt
  rw [hiq] at hel
  change Mi.card ≤ _ ∧
    Bzero 14 D + ((Mi.image os_pt).biUnion (fun c => sem_hw_nb c ∩ sem_hw_opp 0)).card
      ≤ 2*Mi.card
  exact ⟨by omega, by omega⟩

theorem oneSideMissingAccounting {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (budget : totalSurplus 14 D = 14) (Iq : Finset (Fin 7)) (qmin : 4 ≤ Iq.card)
    (hI : ineligSet 14 D = Iq.image os_pt)
    : let m := (missingNeighborhoods D).card
      m ≤ (zeroBranches D).card + (7 - Iq.card) ∧
      (m = 0 → Bzero 14 D = 0) ∧
      (0 < m → Bzero 14 D + min (m+2) 7 ≤ 2*m) := by
  classical
  let M := missingNeighborhoods D
  obtain ⟨upper, exactBound⟩ := oneSideExactMissingAccounting h hD budget Iq qmin hI
  change M.card ≤ _ at upper
  change Bzero 14 D + ((M.image os_pt).biUnion (fun c => sem_hw_nb c ∩ sem_hw_opp 0)).card ≤
    2*M.card at exactBound
  change M.card ≤ (zeroBranches D).card + (7 - Iq.card) ∧
    (M.card = 0 → Bzero 14 D = 0) ∧
    (0 < M.card → Bzero 14 D + min (M.card+2) 7 ≤ 2*M.card)
  refine ⟨upper, ?_, ?_⟩
  · intro none
    omega
  · intro positive
    have geo := os_union M (card_pos.mp positive)
    omega

theorem oneSideBranchAccounting {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (budget : totalSurplus 14 D = 14) (Iq : Finset (Fin 7)) (qmin : 4 ≤ Iq.card)
    (hI : ineligSet 14 D = Iq.image os_pt) :
    ∃ m ≤ (zeroBranches D).card + (7 - Iq.card),
      (m = 0 → Bzero 14 D = 0) ∧
      (0 < m → Bzero 14 D + min (m+2) 7 ≤ 2*m) :=
  ⟨(missingNeighborhoods D).card, oneSideMissingAccounting h hD budget Iq qmin hI⟩

theorem mixedNineBranchAccounting {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (budget : totalSurplus 14 D = 14) (hI : ineligSet 14 D = {0, 1, 2, 5, 11}) :
    0 < Bzero 14 D ∧ Bzero 14 D ≤ 2 ∧ Bzero 14 D = (zeroBranches D).card := by
  classical
  have hel := inelig_card_add 14 D
  rw [hI, show ({0, 1, 2, 5, 11} : Finset (Fin 14)).card = 5 from rfl] at hel
  have hcap : ∀ i ∈ ({0, 1, 2, 5} : Finset (Fin 14)), i ∈ ineligSet 14 D := by rw [hI]; decide
  have hstar := mx_star h hD hcap
  have hLl : mx_L ⊆ sem_hw_opp 0 := by decide
  have hPe : mx_L ⊆ eligSet 14 D := by
    intro a ha
    by_contra hne
    have h1 := sem_mem_inelig.2 hne
    rw [hI] at h1
    exact mx_el a ha h1
  let Oc := ({0, 1, 2, 5} : Finset (Fin 14)).filter (fun i => sup_Occ 14 D mx_L (sem_hw_nb i))
  let Mc := ({0, 1, 2, 5} : Finset (Fin 14)).filter (fun i => ¬ sup_Occ 14 D mx_L (sem_hw_nb i))
  have hcnt := hw_count h hD mx_L hLl hPe Oc {3, 4, 6} {0, 1, 2, 5}
    (fun i hi => ⟨mx_cap i (Finset.mem_filter.1 hi).1, (Finset.mem_filter.1 hi).2⟩)
    (fun c hc => ⟨fun hc' => (mx_ctr c hc).1 (Finset.mem_filter.1 hc').1, Or.inl (mx_ctr c hc).2⟩)
    (fun i hi => ⟨hcap i hi, mx_cap i hi⟩)
  have hlost := missedSharedCount h hD mx_L
    (fun a ha b hb => sem_hw_opp_indep 0 a (hLl ha) b (hLl hb)) Mc
    (fun i hi => ⟨hcap i (Finset.mem_filter.1 hi).1, mx_cap i (Finset.mem_filter.1 hi).1,
      (Finset.mem_filter.1 hi).2⟩)
  have hsplit : Oc.card + Mc.card = 4 :=
    Finset.card_filter_add_card_filter_not (s := ({0, 1, 2, 5} : Finset (Fin 14)))
      (fun i => sup_Occ 14 D mx_L (sem_hw_nb i))
  rw [mx_lab, show ({0, 1, 2, 5} : Finset (Fin 14)).card = 4 from rfl,
    show mx_L.card = 6 from rfl] at hcnt
  have h4 := totalSurplus_split 14 D
  have counts := zeroBranches_le_surplus h.1
  omega


theorem relabel_zeroBranches (σ : Equiv.Perm (Fin 14)) {D : Dag} (h : Strict 14 D) :
    zeroBranches (relabel σ D) = zeroBranches D := by
  ext w
  rw [mem_zeroBranches (relabel_strict σ h), mem_zeroBranches h]
  by_cases small : w < 14
  · let x : Fin 14 := ⟨w, small⟩
    have a : supp 14 D w = {x} := supp_input D x
    have b : supp 14 (relabel σ D) w = {x} := supp_input (relabel σ D) x
    rw [a, b]
    simp
  · have large : 14 ≤ w := by omega
    have f := relabel_fanout σ D w
    have s := relabel_supp σ h w
    rw [tr_liftP_ge σ large] at f s
    rw [f, s]
    simp

theorem sideSevenEightNine {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (budget : totalSurplus 14 D = 14) (Iq : Finset (Fin 7))
    (hi : ineligSet 14 D = Iq.image os_pt)
    (hq : (Iq.card = 7 ∧ (0 : Fin 7) ∈ Iq) ∨
      ((Iq.card = 5 ∨ Iq.card = 6) ∧
        (eligSet 14 D).card + 2 ≤ Bplus 14 D)) :
    (6 ≤ Iq.card → Bzero 14 D = 0) ∧ Bzero 14 D = (zeroBranches D).card := by
  classical
  have p := inelig_card_add 14 D
  rw [hi, card_image_of_injective _ os_pt_inj] at p
  have split := totalSurplus_split 14 D
  have zle := zeroBranches_le_surplus h.1
  obtain ⟨m, hm, none, some⟩ := oneSideBranchAccounting h hD budget Iq
    (by rcases hq with h7 | ⟨h5 | h6, -⟩ <;> omega) hi
  have cap : Bzero 14 D ≤ Iq.card - 2 ∨ Iq.card = 7 ∧ Bzero 14 D ≤ 6 := by
    rcases hq with ⟨seven, zero⟩ | ⟨q, b⟩
    · right
      have key := tight_le h hD (h0 := by rw [hi]; exact mem_image_of_mem os_pt zero)
      have lt : (eligSet 14 D).card < Bplus 14 D := by
        by_contra! le
        exact key le
      omega
    · exact Or.inl (by omega)
  by_cases zm : m = 0
  · have zero := none zm
    omega
  have rel := some (by omega)
  by_cases sm : m + 2 ≤ 7
  · rw [min_eq_left sm] at rel
    omega
  · rw [min_eq_right (by omega)] at rel
    omega

theorem triWithOneZeroBranch {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hz : (zeroBranches D).card ≤ 1)
    {T J : Finset (Fin 14)} (hOK : tOK T J = true) (hJ : ∀ i ∈ J, i ∈ ineligSet 14 D) :
    (eligSet 14 D).card + 3 ≤ Bplus 14 D := by
  classical
  have hG := sem_heawood_gr
  have hC := sem_heawood_comp hD
  obtain ⟨b, hb⟩ := exists_pureBranch h hD
  obtain ⟨pos, hpos⟩ := k4_assigned hG h hC
  obtain ⟨hJ', hA'⟩ := tri_hyp hOK hJ
  obtain ⟨-, -, ⟨hT3, hJ3⟩, hside, hinj, -⟩ := tOK_iff hOK
  have hM : ∀ i ∈ J, ∃ M, sup_Occ 14 D T M ∧ sem_hw_nb i ∩ T ⊆ M ∧
      (sup_Occ 14 D (sem_hw_opp 0) (sem_hw_nb i) → M = sem_hw_nb i ∩ T) := by
    intro i hi
    by_cases hx : sup_Occ 14 D (sem_hw_opp 0) (sem_hw_nb i)
    · obtain ⟨w, hw⟩ := hx
      have : supp 14 D w ∩ T = sem_hw_nb i ∩ T := by
        rw [← hw, Finset.inter_assoc, Finset.inter_eq_right.2 (hside i hi).1]
      exact ⟨_, ⟨w, rfl⟩, this ▸ Finset.Subset.refl _, fun _ => this⟩
    · exact ⟨supp 14 D (src D (pos i)) ∩ T, ⟨_, rfl⟩, fun a ha => by
        rw [Finset.mem_inter, hw_mem_nb] at ha
        exact Finset.mem_inter.2 ⟨(hpos.1 i (hJ i hi)).2.2.1 a ha.1, ha.2⟩,
        fun hc => absurd hc hx⟩
  choose! M hM using hM
  have hlost := missedSharedCount h hD (sem_hw_opp 0) (sem_hw_opp_indep 0)
    (J.filter (fun i => ¬ sup_Occ 14 D (sem_hw_opp 0) (sem_hw_nb i))) (fun i hi => by
      rw [Finset.mem_filter] at hi
      exact ⟨hJ i hi.1, (hside i hi.1).2.2.1, hi.2⟩)
  have hMinj : Set.InjOn M J := by
    intro i hi j hj hij
    by_contra hne
    have key : ∀ i ∈ J, ∀ j ∈ J, M i = M j → i ≠ j →
        ¬ sup_Occ 14 D (sem_hw_opp 0) (sem_hw_nb i) := by
      intro i hi j hj hij hne hx
      exact hne (hinj i hi j hj (by
        rw [← (hM i hi).2.2 hx, hij]; exact (hM j hj).2.1)).symm
    have h1 : i ∈ J.filter (fun i => ¬ sup_Occ 14 D (sem_hw_opp 0) (sem_hw_nb i)) :=
      Finset.mem_filter.2 ⟨hi, key i hi j hj hij hne⟩
    have h2 : j ∈ J.filter (fun i => ¬ sup_Occ 14 D (sem_hw_opp 0) (sem_hw_nb i)) :=
      Finset.mem_filter.2 ⟨hj, key j hj i hi hij.symm (Ne.symm hne)⟩
    have := Finset.one_lt_card.2 ⟨i, h1, j, h2, hne⟩
    omega
  have := tri_occ hG h hC b hb hpos T J (tA T) hJ' hA' (J.image M) (fun X hX => by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hX
    have := Finset.card_le_card (hM i hi).2.1
    rw [(hside i hi).2.2.2] at this
    exact ⟨this, (hM i hi).1⟩)
  rw [Finset.card_image_of_injOn hMinj] at this
  omega

theorem pathWithoutZeroShared {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (zero : Bzero 14 D = 0) (u : Fin 14) (bad : u ∈ ineligSet 14 D)
    (w : ℕ) (path : Relation.ReflTransGen (sem_step 14 D) u.val w) :
    sem_Chain 14 D u.val w ∧ fanout D w ≤ 1 := by
  have absent (b : ℕ) (f : 2 ≤ fanout D b) (empty : supp 14 D b = ∅) : False := by
    have cap := bz_card h.1 ({b} : Finset ℕ) (fun v hv => by
      rw [mem_singleton.mp hv]
      exact ⟨f, empty⟩)
    rw [card_singleton, zero] at cap
    omega
  rcases sem_path_chain path with chain | ⟨b, cb, fb⟩
  · refine ⟨chain, ?_⟩
    by_contra! f
    exact absent w (by omega) (sem_branch_empty sem_heawood_gr h.1
      (sem_heawood_comp hD) bad chain (by omega))
  · exact (absent b fb (sem_branch_empty sem_heawood_gr h.1
      (sem_heawood_comp hD) bad cb fb)).elim

theorem changedWithoutZeroShared {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (zero : Bzero 14 D = 0) (u : Fin 14) (bad : u ∈ ineligSet 14 D)
    (x y : Fin 14 → Bool) (same : ∀ v, v ≠ u → x v = y v)
    (w : ℕ) (diff : val D x w ≠ val D y w) :
    sem_Chain 14 D u.val w ∧ fanout D w ≤ 1 := by
  exact pathWithoutZeroShared h hD zero u bad w
    (sem_rtg_mono (fun _ _ step => step.1) (sem_changed_path h.1 x y u same w diff))
theorem switchedOperandsEligible {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (zero : Bzero 14 D = 0) (u : Fin 14) (x y : Fin 14 → Bool)
    (same : ∀ v, v ≠ u → x v = y v) (j : ℕ) (hj : j < D.length)
    (switches : ∀ s : Bool, val D x (src D (j,s)) ≠ val D y (src D (j,s))) :
    u ∈ eligSet 14 D := by
  by_contra no
  have bad := sem_mem_inelig.mpr no
  obtain ⟨chain, upper⟩ := changedWithoutZeroShared h hD zero u bad x y same
    (src D (j,true)) (switches true)
  have step : sem_step 14 D (src D (j,true)) (14+j) := sem_step_src hj true
  have lo := sem_step_fanout step
  have one : fanout D (src D (j,true)) = 1 := le_antisymm upper lo
  have indep := sem_sibling_indep h.1 u hj false chain (by simpa using one) x y same
  exact switches false indep
theorem smallEligibleGeometry {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (length : D.length = 27) (small : (eligSet 14 D).card ≤ 8) :
    Bzero 14 D = 0 ∧ ∃ σ : Equiv.Perm (Fin 14), IsAut σ ∧
      ∀ v : Fin 14, v ∈ eligSet 14 D ↔ 14 - (eligSet 14 D).card ≤ (σ v).val := by
  classical
  have ic := inelig_card_add 14 D
  have id := surplus_identity h
  have cv := elig_isCover h hD
  have ne : (ineligSet 14 D).Nonempty := card_pos.mp (by omega)
  obtain ⟨σ, aut, canon, cc⟩ := indep_classification_card _
    ((heawood_cover_iff_indep D).mp cv) ne
  obtain ⟨hn, hDn, _, total, bp, bz, he, hi⟩ := heawood_relabel σ aut h hD
  let E := relabel σ D
  have totalE : totalSurplus 14 E = 14 := by change totalSurplus 14 E = _ at total; omega
  have ie : ineligSet 14 E ∈ canonI := hi ▸ canon
  have cardE : (ineligSet 14 E).card = (ineligSet 14 D).card := by rw [hi, cc]
  have edge : ∀ v : Fin 14, (σ v) ∈ eligSet 14 E ↔ v ∈ eligSet 14 D := by
    intro v
    rw [he, mem_image]
    constructor
    · rintro ⟨w, hw, eq⟩
      exact σ.injective eq ▸ hw
    · intro hv
      exact ⟨v, hv, rfl⟩
  have report (q : ℕ) (Iq : Finset (Fin 7))
      (hc : (ineligSet 14 E).card = q) (cq : Iq.card = q) (q6 : 6 ≤ q)
      (eq : ineligSet 14 E = Iq.image os_pt)
      (chart : ∀ i : Fin 14, i ∈ Iq.image os_pt ↔ i.val < q)
      (case : (Iq.card = 7 ∧ (0 : Fin 7) ∈ Iq) ∨
        ((Iq.card = 5 ∨ Iq.card = 6) ∧ (eligSet 14 E).card + 2 ≤ Bplus 14 E)) :
      Bzero 14 D = 0 ∧ ∃ τ : Equiv.Perm (Fin 14), IsAut τ ∧
        ∀ v : Fin 14, v ∈ eligSet 14 D ↔ 14 - (eligSet 14 D).card ≤ (τ v).val := by
    have zs := (sideSevenEightNine hn hDn totalE Iq eq case).1 (by omega)
    refine ⟨bz ▸ zs, σ, aut, ?_⟩
    intro v
    rw [← edge]
    have qeq : 14 - (eligSet 14 D).card = q := by omega
    rw [qeq]
    have a := chart (σ v)
    rw [← eq, sem_mem_inelig, not_iff_comm] at a
    simpa [not_lt] using a.symm
  rcases canonI_by_card _ ie with ⟨hc, eq⟩ | ⟨hc, eq⟩ | ⟨hc, _⟩ | ⟨hc, _⟩ |
    ⟨hc, _⟩ | ⟨hc, _⟩ | ⟨hc, _⟩
  · exact report 7 univ hc (by decide) (by decide)
      (by rw [eq]; decide +kernel) (by decide +kernel) (Or.inl (by decide))
  · have bound := tri012 hn hDn (by rw [eq]; decide +kernel)
    exact report 6 {0,1,2,3,4,5} hc (by decide) (by decide)
      (by rw [eq]; decide +kernel) (by decide +kernel) (Or.inr ⟨Or.inr rfl, bound⟩)
  all_goals omega

theorem adjacencyForbidsSevenEligible {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (length : D.length = 27) (seven : (eligSet 14 D).card = 7)
    (u v : Fin 14) (uv : Adj u v) (hu : u ∈ eligSet 14 D) (hv : v ∈ eligSet 14 D) : False := by
  obtain ⟨_, σ, aut, geom⟩ := smallEligibleGeometry h hD length (by omega)
  have u' := (geom u).mp hu
  have v' := (geom v).mp hv
  rw [seven] at u' v'
  exact (by decide +kernel : ∀ a b : Fin 14, 7 ≤ a.val → 7 ≤ b.val → ¬ Adj a b)
    (σ u) (σ v) u' v' ((aut u v).mpr uv)
def hasDoubleSwitch (D : Dag) (u : Fin 14) : Prop :=
  ∃ (x y : Fin 14 → Bool) (j : ℕ), j < D.length ∧
    (∀ v, v ≠ u → x v = y v) ∧
    ∀ s : Bool, val D x (src D (j,s)) ≠ val D y (src D (j,s))

theorem doubleSwitchGeometry {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (length : D.length = 27) (u v : Fin 14) (uv : Adj u v)
    (swU : hasDoubleSwitch D u) (swV : hasDoubleSwitch D v) :
    8 ≤ (eligSet 14 D).card ∧
    ((eligSet 14 D).card = 8 → ∃ σ : Equiv.Perm (Fin 14), IsAut σ ∧
      ((σ u).val = 6 ∨ (σ v).val = 6)) := by
  have lower := cover_card_ge_seven _ (elig_isCover h hD)
  have elig (w : Fin 14) (sw : hasDoubleSwitch D w) (zero : Bzero 14 D = 0) :
      w ∈ eligSet 14 D := by
    obtain ⟨x,y,j,hj,same,switches⟩ := sw
    exact switchedOperandsEligible h hD zero w x y same j hj switches
  constructor
  · by_contra! tooSmall
    have seven : (eligSet 14 D).card = 7 := by omega
    have empty := (smallEligibleGeometry h hD length (by omega)).1
    exact adjacencyForbidsSevenEligible h hD length seven u v uv (elig u swU empty) (elig v swV empty)
  · intro eight
    obtain ⟨empty, σ, aut, chart⟩ := smallEligibleGeometry h hD length (by omega)
    refine ⟨σ, aut, ?_⟩
    have a := (chart u).mp (elig u swU empty)
    have b := (chart v).mp (elig v swV empty)
    rw [eight] at a b
    exact (by decide +kernel : ∀ p q : Fin 14, Adj p q → 6 ≤ p.val → 6 ≤ q.val →
      p.val = 6 ∨ q.val = 6) (σ u) (σ v) ((aut u v).mpr uv) a b
theorem nineEligibleZeroBranches {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (length : D.length = 27) (nine : (eligSet 14 D).card = 9) :
    Bzero 14 D = (zeroBranches D).card := by
  classical
  have ic := inelig_card_add 14 D
  have id := surplus_identity h
  have cv := elig_isCover h hD
  have ne : (ineligSet 14 D).Nonempty := card_pos.mp (by omega)
  obtain ⟨σ, aut, canon, cc⟩ := indep_classification_card _
    ((heawood_cover_iff_indep D).mp cv) ne
  obtain ⟨hn, hDn, _, total, _, bz, _, hi⟩ := heawood_relabel σ aut h hD
  let E := relabel σ D
  have totalE : totalSurplus 14 E = 14 := by change totalSurplus 14 E = _ at total; omega
  have ie : ineligSet 14 E ∈ canonI := hi ▸ canon
  have cardE : (ineligSet 14 E).card = 5 := by rw [hi, cc]; omega
  rw [← bz, ← relabel_zeroBranches σ h.1]
  rcases canonI_by_card _ ie with ⟨hc, _⟩ | ⟨hc, _⟩ | ⟨hc, line | mixed⟩ |
    ⟨hc, _⟩ | ⟨hc, _⟩ | ⟨hc, _⟩ | ⟨hc, _⟩
  · omega
  · omega
  · have bound := tri012 hn hDn (by rw [line]; decide +kernel)
    exact (sideSevenEightNine hn hDn totalE {0,1,2,3,4}
      (by rw [line]; decide +kernel) (Or.inr ⟨Or.inl rfl, bound⟩)).2
  · exact (mixedNineBranchAccounting hn hDn totalE mixed).2.2
  all_goals omega

theorem nineEligibleEmptyFanoutTwo {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (length : D.length = 27) (nine : (eligSet 14 D).card = 9)
    (w : ℕ) (fan : 2 ≤ fanout D w) (empty : supp 14 D w = ∅) :
    fanout D w = 2 :=
  zeroBranch_fanout_two h.1 (nineEligibleZeroBranches h hD length nine) w fan empty
theorem mixedElevenSmallBplus {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (bound : Bplus 14 D ≤ 12) (hI : ineligSet 14 D = {0, 1, 11}) : False := by
  classical
  have hG := sem_heawood_gr
  have hC := sem_heawood_comp hD
  obtain ⟨b, hbm⟩ := sem_exists_minBranch hG h.1 hC
  have hb := sem_minBranch_pure hbm
  obtain ⟨pos, hpos⟩ := k4_assigned hG h hC
  have hin : ∀ i ∈ ({0, 1, 11} : Finset (Fin 14)), i ∈ ineligSet 14 D := by
    rw [hI]; exact fun _ hi => hi
  have h0 := hin 0 (by decide)
  have h1 := hin 1 (by decide)
  have h11 := hin 11 (by decide)
  have hel : ∀ x : Fin 14, x ∉ ({0, 1, 11} : Finset (Fin 14)) → x ∈ eligSet 14 D := by
    intro x hx
    by_contra hc
    exact hx (hI ▸ sem_mem_inelig.2 hc)
  have hne : ∀ x ∈ eligSet 14 D, ∀ i ∈ ineligSet 14 D, x ≠ i :=
    fun x hx i hi hxi => sem_mem_inelig.1 hi (hxi ▸ hx)
  have edge : ∀ x y : Fin 14, Adj x y → x ∈ eligSet 14 D → y ∈ eligSet 14 D →
      ∃ e ∈ sem_W 14 D x, sem_bar e ∈ sem_W 14 D y ∧
        (∀ i ∈ ineligSet 14 D, e ≠ pos i ∧ sem_bar e ≠ pos i) ∧
        x ∉ supp 14 D (src D (sem_bar e)) := by
    intro x y hxy hx hy
    obtain ⟨e, he, heb, -, hs, -⟩ := sem_edge_slots hG h.1 hC hxy
    exact ⟨e, he, heb, fun i hi => ⟨fun hc => hne y hy i hi (as_priv hpos hi (hc ▸ heb)),
      fun hc => hne x hx i hi (as_priv hpos hi (by rw [← hc, sem_bar_bar]; exact he))⟩, hs⟩
  have k0 := (hpos.1 0 h0).2.2.1
  have k1 := (hpos.1 1 h1).2.2.1
  have e7 := hel 7 (by decide)
  have e3 := hel 3 (by decide)
  obtain ⟨H, hH7, hH3, hHf, -⟩ := edge 7 3 (by decide) e7 e3
  have a07 := as_mem hpos h0 (a := 7) (by decide)
  have a17 := as_mem hpos h1 (a := 7) (by decide)
  have p01 : pos 0 ≠ pos 1 := fun hc => absurd (hpos.2 0 h0 1 h1 hc) (by decide)
  obtain ⟨t71, t72⟩ := pc_three a07 a17 hH7 p01 (hHf 0 h0).1.symm (hHf 1 h1).1.symm
  have c7 := cc_el h hD b hb e7
  have hr := card_residual h.1 b hb
  have hp := inelig_card_add 14 D
  rw [hI, show ({0, 1, 11} : Finset (Fin 14)).card = 3 from rfl] at hp
  have hsplit := totalSurplus_split 14 D
  have hr7 : (ru D b 7).card ≤ (residualUnits 14 D b).card := Finset.card_filter_le _ _
  have lw : ∀ (u : Σ _ : ℕ, ℕ) (x : Fin 14),
      (∀ v ∈ residualUnits 14 D b, x ∈ supp 14 D v.1 → v = u) →
      (sem_W 14 D x).card + (merges 14 D (carrierT 14 D {x})).card ≤ 3 ∧
        (x ∉ supp 14 D u.1 → (sem_W 14 D x).card ≤ 2) := by
    intro u x hu
    have q1 := cc_le h hD b hb x
    have q2 : (ru D b x).card ≤ 1 := Finset.card_le_one.2 (fun a ha c hc =>
      (hu a (mem_ru.1 ha).1 (mem_ru.1 ha).2).trans (hu c (mem_ru.1 hc).1 (mem_ru.1 hc).2).symm)
    refine ⟨by omega, fun hn => ?_⟩
    have : (ru D b x).card = 0 := Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2
      (fun v hv hxv => hn (hu v hv hxv ▸ hxv)))
    omega
  have nB : (ru D b 7).card ≠ 2 := by omega
  obtain ⟨u1, hu1⟩ := Finset.card_pos.1 (show 0 < (ru D b 7).card by omega)
  obtain ⟨hu1r, h7u1⟩ := mem_ru.1 hu1
  have huniq : ∀ v ∈ residualUnits 14 D b, 7 ∈ supp 14 D v.1 → v = u1 := fun v hv h7v =>
    Finset.card_le_one.1 (show (ru D b 7).card ≤ 1 by omega) v (mem_ru.2 ⟨hv, h7v⟩) u1 hu1
  have hW7 := t72 (by omega)
  have hW7' := fun e he => or_left_comm.1 (hW7 e he)
  have colab : ∀ t, t ∈ supp 14 D u1.1 → t ≠ 7 →
      t ∈ supp 14 D (src D (pos 0)) ∧ t ∈ supp 14 D (src D (pos 1)) := by
    intro t ht ht7
    have hte := res_elig hu1r ht
    obtain ⟨e0, he0⟩ := ri_gen hG h hC b hb (Ne.symm ht7) e7
      (fun v hv h7v => by rw [huniq v hv h7v]; exact ht) ⟨h7u1, ht⟩
    have mk : ∀ i j : Fin 14, j ∈ ineligSet 14 D → j ∈ ({0, 1} : Finset (Fin 14)) →
        (∀ e ∈ sem_W 14 D 7, e = pos i ∨ e = pos j ∨ e = H) →
        t ∈ supp 14 D (src D (pos i)) → t ∈ supp 14 D (src D H) → False := by
      intro i j hj hj01 hW hti htH
      obtain ⟨q, hq1, hq7, hq2⟩ := pc_q j hj01 t (hne t hte j hj)
      obtain ⟨e, he, n1, n2⟩ := sem_hw_cover_free h hD (x := 7) (Ne.symm ht7)
        (Ne.symm hq7) (sem_adjB_false.1 hq2)
      rcases hW e he with rfl | rfl | rfl
      · exact n1 hti
      · exact n2 ((hpos.1 j hj).2.2.1 q ((hc_adjB_iff _ _).1 hq1))
      · exact n1 htH
    by_cases c0 : pos 0 = e0
    · exact (mk 1 0 h0 (by decide) hW7'
        (he0 _ a17 (fun hc => p01 (c0.trans hc.symm)))
        (he0 _ hH7 (fun hc => (hHf 0 h0).1 (hc.trans c0.symm)))).elim
    · have a0 := he0 _ a07 c0
      by_cases c1 : pos 1 = e0
      · exact (mk 0 1 h1 (by decide) hW7 a0
          (he0 _ hH7 (fun hc => (hHf 1 h1).1 (hc.trans c1.symm)))).elim
      · exact ⟨a0, he0 _ a17 c1⟩
  have nR : (residualUnits 14 D b).card ≠ 1 := by
    intro hR
    have L := fun x => lw u1 x (fun v hv _ => Finset.card_le_one.1 hR.le v hv u1 hu1r)
    have asg : ∀ i ∈ ineligSet 14 D, ∀ t, t ∈ supp 14 D (src D (pos i)) →
        pos i ∈ sem_W 14 D t := fun i hi t ht => sem_mem_W.2 ⟨(hpos.1 i hi).1, ht, by
          rw [(hpos.1 i hi).2.1]; exact Finset.notMem_empty t⟩
    have e4 := hel 4 (by decide)
    have a4 := as_mem hpos h11 (a := 4) (by decide)
    have a10 := as_mem hpos h0 (a := 10) (by decide)
    obtain ⟨e1, he1, hb1, hf1, -⟩ := edge 4 10 (by decide) e4 (hel 10 (by decide))
    obtain ⟨e2, he2, hb2, hf2, -⟩ := edge 4 13 (by decide) e4 (hel 13 (by decide))
    have n4 : 4 ∉ supp 14 D u1.1 := by
      intro h4
      obtain ⟨q0, q1⟩ := colab 4 h4 (by decide)
      rcases (pc_three (asg 0 h0 4 q0) (asg 1 h1 4 q1) he1 p01 (hf1 0 h0).1.symm
        (hf1 1 h1).1.symm).2 (by have := (L 4).1; omega) _ a4 with hc | hc | hc
      · exact absurd (hpos.2 11 h11 0 h0 hc) (by decide)
      · exact absurd (hpos.2 11 h11 1 h1 hc) (by decide)
      · exact (hf1 11 h11).1 hc.symm
    have h12 : e1 = e2 := by
      by_contra hc
      have := (pc_three a4 he1 he2 (hf1 11 h11).1.symm (hf2 11 h11).1.symm hc).1
      have := (L 4).2 n4
      omega
    rw [← h12] at hb2
    obtain ⟨e, he, n7, n13⟩ := sem_hw_cover_free h hD (x := 10) (a := 7) (b := 13)
      (by decide) (by decide) (by decide)
    have d1 : sem_bar e1 ≠ e := fun hc => n13 (hc ▸ (sem_mem_W.1 hb2).2.1)
    have d2 : pos 0 ≠ e := fun hc => n7 (hc ▸ k0 7 (by decide))
    by_cases h10 : 10 ∈ supp 14 D u1.1
    · rcases (pc_three hb1 a10 (asg 1 h1 10 (colab 10 h10 (by decide)).2) (hf1 0 h0).2
        (hf1 1 h1).2 p01).2 (by have := (L 10).1; omega) e he with hc | hc | hc
      · exact d1 hc.symm
      · exact d2 hc.symm
      · exact n7 (hc ▸ k1 7 (by decide))
    · have := (pc_three hb1 a10 he (hf1 0 h0).2 d1 d2).1
      have := (L 10).2 h10
      omega
  omega

theorem mixed22SmallBplusRaw {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hI : ineligSet 14 D = pe_I) (bound : Bplus 14 D ≤ 12)
    (raw : ∀ w, 2 ≤ fanout D w → (supp 14 D w).Nonempty → w < 14) :
    False := by
  classical
  obtain ⟨b, hb⟩ := exists_pureBranch h hD
  obtain ⟨pos, hpos⟩ := k4_assigned sem_heawood_gr h (sem_heawood_comp hD)
  have hK : pe_K D b pos := ⟨h, hD, hb, hpos, hI⟩
  obtain ⟨H, hH3, hH7, -, -, -⟩ := sem_edge_slots sem_heawood_gr h.1
    (sem_heawood_comp hD) (x := 3) (y := 7) (by decide)
  have l3 := pe_el hK 3 (by decide)
  have l7 := pe_el hK 7 (by decide)
  have hJ7 := pe_J hK (x := 7) {0, 1} (by decide)
  have hJ3 := pe_J hK (x := 3) {11, 12} (by decide)
  have c7 := pe_cnt hpos _ hJ7 {sem_bar H} (fun e he => by
    rw [mem_singleton.1 he]
    exact ⟨hH7, fun i hi => pe_np2 hpos (hJ7 i hi).1 l3 hH3⟩)
  have c3 := pe_cnt hpos _ hJ3 {H} (fun e he => by
    rw [mem_singleton.1 he]
    exact ⟨hH3, fun i hi => pe_np1 hpos (hJ3 i hi).1 l7 hH7⟩)
  rw [card_singleton, show ({0, 1} : Finset (Fin 14)).card = 2 from rfl] at c7
  rw [card_singleton, show ({11, 12} : Finset (Fin 14)).card = 2 from rfl] at c3

  let hG := sem_heawood_gr
  let hC := sem_heawood_comp hD
  have hel := pe_el hK
  have cunit (x : Fin 14) (hx : x ∈ eligSet 14 D) (hc : 3 ≤ (sem_W 14 D x).card) :
      ∃ u ∈ residualUnits 14 D b, supp 14 D u.1 = {x} := by
    have eq := cc_el h hD b hb hx
    obtain ⟨u, hu⟩ := card_pos.mp (show 0 < (ru D b x).card by omega)
    obtain ⟨res, sx⟩ := mem_ru.mp hu
    have small : u.1 < 14 := raw u.1 (res_fan res) ⟨x, sx⟩
    let y : Fin 14 := ⟨u.1, small⟩
    have eq' : supp 14 D u.1 = {y} := supp_input D y
    rw [eq', mem_singleton] at sx
    exact ⟨u, res, sx.symm ▸ eq'⟩
  obtain ⟨uc, huc', sc⟩ := cunit 3 l3 (by omega)
  obtain ⟨uk, huk, sk⟩ := cunit 7 l7 (by omega)
  have huc : uc ∈ residualUnits 14 D b ∧ (3 : Fin 14) ∈ supp 14 D uc.1 :=
    ⟨huc', by rw [sc]; simp⟩
  have hne : uc ≠ uk := by
    intro eq
    rw [eq, sk] at sc
    have different : (7 : Fin 14) ≠ 3 := by decide
    exact different (singleton_injective sc)
  have rcard := card_residual h.1 b hb
  have ic := inelig_card_add 14 D
  rw [hI, show pe_I.card = 4 from rfl] at ic
  have lowerCard := one_lt_card.mpr ⟨uc,huc',uk,huk,hne⟩
  have hR2 : (residualUnits 14 D b).card = 2 := by omega
  have co3 : ∀ t : Fin 14, 3 ≠ t → t ∈ supp 14 D uc.1 →
      ∀ k ∈ ({11, 12} : Finset (Fin 14)), pos k ∈ sem_W 14 D t := by
    intro t ne mem
    rw [sc, mem_singleton] at mem
    exact (ne mem.symm).elim
  have co7 : ∀ t : Fin 14, 7 ≠ t → t ∈ supp 14 D uk.1 →
      ∀ k ∈ ({0, 1} : Finset (Fin 14)), pos k ∈ sem_W 14 D t := by
    intro t ne mem
    rw [sk, mem_singleton] at mem
    exact (ne mem.symm).elim
  have hres : ({uc, uk} : Finset (Σ _ : ℕ, ℕ)) = residualUnits 14 D b :=
    eq_of_subset_of_card_le (fun u hu => by
      rcases mem_insert.1 hu with hu | hu
      · rw [hu]; exact huc.1
      · rw [mem_singleton.1 hu]; exact huk) (by rw [card_pair hne, hR2])
  have hρ : ∀ x : Fin 14, (ru D b x).card ≤
      (if x ∈ supp 14 D uc.1 then 1 else 0) + if x ∈ supp 14 D uk.1 then 1 else 0 :=
    fun x => by
      have := card_filter (fun u : Σ _ : ℕ, ℕ => x ∈ supp 14 D u.1) {uc, uk}
      rw [sum_pair hne, hres] at this
      exact this.le
  obtain ⟨F, hF1, hF2, -⟩ := sem_edge_slots hG h.1 hC (x := 4) (y := 10) (by decide)
  have P4 := pe_one hK (x := 4) (i := 11) {11, 12} {0, 1} (by decide) (co3 4 (by decide))
    (co7 4 (by decide)) (hρ 4) ⟨hF1, fun k hk => pe_np1 hpos hk (hel 10 (by decide)) hF2⟩
  have P10 := pe_one hK (x := 10) (i := 0) {0, 1} {11, 12} (by decide) (co7 10 (by decide))
    (co3 10 (by decide)) (by rw [Nat.add_comm]; exact hρ 10)
    ⟨hF2, fun k hk => pe_np2 hpos hk (hel 4 (by decide)) hF1⟩
  obtain ⟨e, he1, he2, -⟩ := sem_edge_slots hG h.1 hC (x := 4) (y := 13) (by decide)
  rcases P4 e he1 with h1 | h1
  · rw [h1] at he2
    obtain ⟨e', he', h4, h5⟩ := sem_hw_cover_free h hD (x := 10) (a := 7) (b := 13)
      (by decide) (by decide) (by decide)
    rcases P10 e' he' with h6 | h6
    · exact h5 (h6 ▸ (sem_mem_W.1 he2).2.1)
    · obtain ⟨k, hk, rfl⟩ := mem_image.1 h6
      exact h4 (sem_mem_W.1 (hJ7 k hk).2).2.1
  · obtain ⟨k, hk, rfl⟩ := mem_image.1 h1
    exact pe_np1 hpos (hJ3 k hk).1 (hel 13 (by decide)) he2 rfl

theorem soleZeroTripleOrbit {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (length : D.length = 27)
    (sole : ∃ s, supp 14 D s = ∅ ∧ (∀ w, 14 ≤ w → 2 ≤ fanout D w → w = s))
    (bz : 2 ≤ Bzero 14 D) :
    ∃ σ : Equiv.Perm (Fin 14), IsAut σ ∧ ineligSet 14 (relabel σ D) = {0,1,3} := by
  classical
  obtain ⟨s, hs, only⟩ := sole
  have id := surplus_identity h
  have ct := inelig_card_add 14 D
  have sp := totalSurplus_split 14 D
  have cv := elig_isCover h hD
  have seven := cover_card_ge_seven _ cv
  have nine : 9 ≤ (eligSet 14 D).card := by
    by_contra! small
    have eq := (smallEligibleGeometry h hD length (by omega)).1
    omega
  have ne : (ineligSet 14 D).Nonempty := by
    obtain ⟨b, hb⟩ := exists_pureBranch h hD
    have cap := elig_le_Bplus h.1 b hb
    exact card_pos.mp (by omega)
  obtain ⟨σ, aut, canon, ic⟩ := indep_classification_card _
    ((heawood_cover_iff_indep D).mp cv) ne
  obtain ⟨hn, hDn, _, total, plusEq, zeroEq, _, ie⟩ := heawood_relabel σ aut h hD
  let E := relabel σ D
  have canon' : ineligSet 14 E ∈ canonI := ie ▸ canon
  have iE : (ineligSet 14 E).card = (ineligSet 14 D).card := by rw [ie, ic]
  have icE := inelig_card_add 14 E
  have cap : Bplus 14 E ≤ 12 := by
    change Bplus 14 E = _ at plusEq
    omega
  have raw (w : ℕ) (f : 2 ≤ fanout E w) (sm : (supp 14 E w).Nonempty) : w < 14 := by
    by_contra! large
    have ren := relabel_fanout σ D w
    rw [tr_liftP_ge σ large] at ren
    have eq := only w large (ren ▸ f)
    have ss := relabel_supp σ h.1 w
    rw [tr_liftP_ge σ large, eq, hs, image_empty] at ss
    exact sm.ne_empty (eq.symm ▸ ss)
  have one : (zeroBranches E).card ≤ 1 := by
    apply card_le_one.mpr
    intro u hu v hv
    have eqs (w : ℕ) (hw : w ∈ zeroBranches E) : w = s := by
      obtain ⟨f, empty⟩ := (mem_zeroBranches hn.1).mp hw
      have large : 14 ≤ w := by
        by_contra! small
        let k : Fin 14 := ⟨w, small⟩
        have eq : supp 14 E w = {k} := supp_input E k
        rw [eq] at empty
        exact singleton_ne_empty k empty
      have ren := relabel_fanout σ D w
      rw [tr_liftP_ge σ large] at ren
      exact only w large (ren ▸ f)
    exact (eqs u hu).trans (eqs v hv).symm
  have in0 : (0 : Fin 14) ∈ ineligSet 14 E := by
    obtain ⟨k, hk, eq⟩ := hc_rep_of_mem canon'
    have tab : ∀ l : Fin 15, l ≠ 0 → (0 : Fin 14) ∈ hc_rep l := by decide +kernel
    rw [← eq]
    exact tab k hk
  have gt : (eligSet 14 E).card < Bplus 14 E := by
    by_contra! ng
    exact tight_le hn hDn ng in0
  have tri (ht : ∀ i ∈ ({0,1,2} : Finset (Fin 14)), i ∈ ineligSet 14 E) :
      (eligSet 14 E).card + 3 ≤ Bplus 14 E :=
    triWithOneZeroBranch hn hDn one (by decide +kernel : tOK {7,8,13} {0,1,2} = true) ht
  rcases canonI_by_card _ canon' with ⟨qc, _⟩ | ⟨qc, _⟩ | ⟨qc, _⟩ |
    ⟨qc, a | a | a | a⟩ | ⟨qc, a | a | a⟩ | ⟨qc, _⟩ | ⟨qc, _⟩
  · omega
  · omega
  · have p9 : (eligSet 14 D).card = 9 := by omega
    have zEq := nineEligibleZeroBranches h hD length p9
    have ren := relabel_zeroBranches σ h.1
    change zeroBranches E = _ at ren
    have ce := congrArg Finset.card ren
    omega
  · have b := tri (by rw [a]; decide +kernel); omega
  · have b := tri (by rw [a]; decide +kernel); omega
  · have b := tri (by rw [a]; decide +kernel); omega
  · exact (mixed22SmallBplusRaw hn hDn a cap raw).elim
  · have b := tri (by rw [a]; decide +kernel); omega
  · exact ⟨σ, aut, a⟩
  · exact (mixedElevenSmallBplus hn hDn cap a).elim
  · omega
  · omega
end NestedFano.SolReview











