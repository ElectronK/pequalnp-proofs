import Mathlib.Tactic.FinCases
import PEqualNP.Defs

-- The signed four-input search is adapted from the checked L-meta-9564 and L-meta-8633.
-- Two input restrictions leave a five-clique. After its first binary gate, choose
-- a restriction that saves another gate, then apply the four-input certificate.

namespace PEqualNP.Outside.L_meta_10640.Signed

-- The signed live-wire search follows L-meta-8463 and L-meta-1449, Apache-2.0.

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

set_option maxRecDepth 100000 in
theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

set_option maxRecDepth 100000 in
theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

set_option maxRecDepth 100000 in
theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

set_option maxRecDepth 100000 in
theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

-- Oppositely labeled assignments are paired across the upper and lower halves.
abbrev W := BitVec 110
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 55 := ((x >>> 55) ^^^ x).setWidth 55
def cuts (ws : List W) : BitVec 55 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 55) ++ (0 : BitVec 55)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 100000 in
theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

set_option maxRecDepth 100000 in
theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 55) (w : W) : Prop :=
  w.getLsbD (55+i.val) ≠ w.getLsbD i.val

set_option maxRecDepth 100000 in
theorem ops_differs (i : Fin 55) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 55+i.val < 110 := by omega
  have hi' : i.val < 110 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

set_option maxRecDepth 100000 in
theorem cuts_spec (ws : List W) (i : Fin 55) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

set_option maxRecDepth 100000 in
theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 55)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

set_option maxRecDepth 100000 in
theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

set_option maxRecDepth 100000 in
theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

set_option maxRecDepth 100000 in
theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

set_option maxRecDepth 100000 in
theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

set_option maxRecDepth 100000 in
theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) ws

set_option maxRecDepth 100000 in
theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

set_option maxRecDepth 100000 in
theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

set_option maxRecDepth 100000 in
theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 100000 in
theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 100000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 110 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 110)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

set_option maxRecDepth 100000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))



def rows : List W := [0x1ffc0055bab756eadd5b, 0xffe0000066dcdb9b736e6d, 0x7ff0000000078ef1de3bc778e, 0x3ff800000000007f0fe1fc3f87f0]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem reject : search 6 rows = false := by decide +kernel

end PEqualNP.Outside.L_meta_10640.Signed

namespace PEqualNP.Outside.L_meta_10640.Credit

abbrev Signal (α : Type) := α → Bool

def fixed {α : Type} (b : Bool) : Signal α := fun _ => b

def inverse {α : Type} (f : Signal α) : Signal α := fun x => !f x

def combine {α : Type} (tag : Bool) (a b : Signal α) : Signal α :=
  if tag then fun x => a x && b x else fun x => a x || b x

def pull {α β : Type} (q : β → α) (f : Signal α) : Signal β := fun x => f (q x)

def Constant {α : Type} (f : Signal α) := ∃ b, f = fixed b

def Available {α : Type} (s : Set (Signal α)) (f : Signal α) : Prop :=
  Constant f ∨ ∃ u ∈ s, f = u ∨ f = inverse u

theorem member {α : Type} {s : Set (Signal α)} {f} (h : f ∈ s) : Available s f :=
  Or.inr ⟨f, h, Or.inl rfl⟩

theorem availConst {α : Type} (s : Set (Signal α)) (c : Bool) : Available s (fixed c) :=
  Or.inl ⟨c, rfl⟩

theorem inverse_inverse {α : Type} (f : Signal α) : inverse (inverse f) = f := by
  funext x
  simp [inverse]

theorem availNeg {α : Type} {s : Set (Signal α)} {f} (h : Available s f) :
    Available s (inverse f) := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact availConst s (!b)
  · exact Or.inr ⟨_, hu, Or.inr rfl⟩
  · rw [inverse_inverse]
    exact member hu

theorem availInsert {α : Type} {s : Set (Signal α)} {f} (g) (h : Available s f) :
    Available (insert g s) f := by
  rcases h with hc | ⟨u, hu, he⟩
  · exact Or.inl hc
  · exact Or.inr ⟨u, Set.mem_insert_of_mem _ hu, he⟩

theorem pullCombine {α β : Type} (q : β → α) (tag) (a b : Signal α) :
    pull q (combine tag a b) = combine tag (pull q a) (pull q b) := by
  cases tag <;> rfl

theorem availMap {α β : Type} {s : Set (Signal α)} {t : Set (Signal β)} {q : β → α}
    (hs : ∀ u ∈ s, Available t (pull q u)) {f} (h : Available s f) :
    Available t (pull q f) := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact availConst _ _
  · exact hs _ hu
  · exact availNeg (hs _ hu)

theorem cheap {α : Type} {s : Set (Signal α)} (tag) {a b}
    (ha : Available s a) (hb : Available s b) (hc : Constant a ∨ Constant b) :
    Available s (combine tag a b) := by
  rcases hc with ⟨v, rfl⟩ | ⟨v, rfl⟩ <;> cases v <;> cases tag <;>
    simp [combine, fixed] <;>
    first | exact ha | exact hb

inductive Program {α : Type} : Set (Signal α) → Signal α → Nat → Prop where
  | done {s f} (h : Available s f) : Program s f 0
  | gate {s f a b k} (tag : Bool) (ha : Available s a) (hb : Available s b)
      (tail : Program (insert (combine tag a b) s) f k) : Program s f (k + 1)

def Simple {α β : Type} (q : β → α) (x y : α) (f : Signal α) :=
  f x = f y ∨ Constant (pull q f)

theorem simpleNeg {α β : Type} {q : β → α} {x y : α} {f : Signal α}
    (h : Simple q x y f) : Simple q x y (inverse f) := by
  rcases h with hs | ⟨b, he⟩
  · exact Or.inl (congrArg Bool.not hs)
  · exact Or.inr ⟨!b, congrArg inverse he⟩

theorem simpleAvailable {α β : Type} {q : β → α} {x y : α} {s : Set (Signal α)}
    (hs : ∀ u ∈ s, Simple q x y u) {f} (h : Available s f) : Simple q x y f := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl rfl
  · exact hs _ hu
  · exact simpleNeg (hs _ hu)

theorem restrictProgram {α β : Type} (q : β → α) (x y : α) {s : Set (Signal α)} {f k}
    (p : Program s f k) (t : Set (Signal β))
    (hs : ∀ u ∈ s, Available t (pull q u)) :
    ∃ j, j ≤ k ∧ Program t (pull q f) j ∧
      (j = k → (∀ u ∈ s, Simple q x y u) → Simple q x y f) := by
  induction p generalizing t with
  | done h =>
    exact ⟨0, le_rfl, .done (availMap hs h), fun _ h' => simpleAvailable h' h⟩
  | @gate s f a b k tag ha hb tail ih =>
    have pa := availMap hs ha
    have pb := availMap hs hb
    by_cases hc : Constant (pull q a) ∨ Constant (pull q b)
    · have mid : Available t (pull q (combine tag a b)) := by
        rw [pullCombine]
        exact cheap tag pa pb hc
      obtain ⟨j, hj, prog, _⟩ := ih t (fun v hv => by
        rcases Set.mem_insert_iff.mp hv with rfl | hu
        · exact mid
        · exact hs _ hu)
      exact ⟨j, by omega, prog, fun he => by omega⟩
    · let c := combine tag (pull q a) (pull q b)
      obtain ⟨j, hj, prog, active⟩ := ih (insert c t) (fun v hv => by
        rcases Set.mem_insert_iff.mp hv with rfl | hu
        · rw [pullCombine]
          exact member (Set.mem_insert _ _)
        · exact availInsert _ (hs _ hu))
      refine ⟨j+1, by omega, .gate tag pa pb prog, ?_⟩
      intro he ss
      apply active (by omega)
      intro u hu
      rcases Set.mem_insert_iff.mp hu with rfl | mem
      · have sta : a x = a y := (simpleAvailable ss ha).resolve_right (fun h => hc (.inl h))
        have stb : b x = b y := (simpleAvailable ss hb).resolve_right (fun h => hc (.inr h))
        left
        cases tag <;> simp [combine, sta, stb]
      · exact ss _ mem

theorem strictRestriction {α β : Type} (q : β → α) (x y : α) {s : Set (Signal α)} {f k}
    (p : Program s f k) (t : Set (Signal β))
    (hs : ∀ u ∈ s, Available t (pull q u)) (hi : ∀ u ∈ s, Simple q x y u)
    (hf : ¬ Simple q x y f) : ∃ j < k, Program t (pull q f) j := by
  obtain ⟨j, hj, hp, hh⟩ := restrictProgram q x y p t hs
  exact ⟨j, lt_of_le_of_ne hj (fun he => hf (hh he hi)), hp⟩

end PEqualNP.Outside.L_meta_10640.Credit

namespace PEqualNP.Outside.L_meta_10640.Credit

open PEqualNP.CircuitLowerBounds

def paid (g : Gate) : Bool :=
  match g.op, g.inputs with
  | .and, _ :: _ :: _ => true
  | .or, _ :: _ :: _ => true
  | _, _ => false

def Legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def readWire {α : Type} (w : List (Signal α)) (i : Nat) := w.getD i (fixed false)

def gateVal {α : Type} (w : List (Signal α)) (g : Gate) : Signal α :=
  fun x => g.op.eval (g.inputs.map fun i => readWire w i x)

def extend {α : Type} (w : List (Signal α)) (g : Gate) := w ++ [gateVal w g]

theorem readAvailable {α : Type} {s : Set (Signal α)} {w : List (Signal α)}
    (hw : ∀ u ∈ w, Available s u) (i : Nat) : Available s (readWire w i) := by
  by_cases h : i < w.length
  · apply hw
    simp [readWire, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  · rw [readWire, List.getD_eq_default _ _ (by omega)]
    exact availConst s false

theorem classify {α : Type} {s : Set (Signal α)} (w : List (Signal α)) (g : Gate)
    (hg : Legal g) (hw : ∀ u ∈ w, Available s u) :
    if paid g then ∃ t a b, Available s a ∧ Available s b ∧ gateVal w g = combine t a b
    else Available s (gateVal w g) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hlen
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨k, rest⟩⟩⟩
  · rcases hop with rfl | rfl | rfl <;> simp [paid, gateVal, GateOp.eval] <;>
      first | exact availConst s true | exact availConst s false
  · rcases hop with rfl | rfl | rfl
    · change Available s (gateVal w ⟨.and, [i]⟩)
      rw [show gateVal w ⟨.and, [i]⟩ = readWire w i by funext x; simp [gateVal, GateOp.eval]]
      exact readAvailable hw i
    · change Available s (gateVal w ⟨.or, [i]⟩)
      rw [show gateVal w ⟨.or, [i]⟩ = readWire w i by funext x; simp [gateVal, GateOp.eval]]
      exact readAvailable hw i
    · exact availNeg (readAvailable hw i)
  · rcases hop with rfl | rfl | rfl
    · simp only [paid, ite_true]
      exact ⟨true, readWire w i, readWire w j, readAvailable hw i, readAvailable hw j,
        by funext x; simp [gateVal, GateOp.eval, combine]⟩
    · simp only [paid, ite_true]
      exact ⟨false, readWire w i, readWire w j, readAvailable hw i, readAvailable hw j,
        by funext x; simp [gateVal, GateOp.eval, combine]⟩
    · simp [paid, gateVal, GateOp.eval]
      exact availNeg (readAvailable hw i)
  · simp at hlen

theorem rawProgram {α : Type} (gs : List Gate) (o : Nat) (hg : ∀ g ∈ gs, Legal g)
    (w : List (Signal α)) (s : Set (Signal α)) (hw : ∀ u ∈ w, Available s u) :
    Program s (readWire (gs.foldl extend w) o) (gs.filter paid).length := by
  induction gs generalizing w s with
  | nil =>
    exact .done (readAvailable hw o)
  | cons g gs ih =>
    have hclass := classify w g (hg g (by simp)) hw
    have tail := ih (fun v hv => hg v (by simp [hv])) (extend w g)
    cases hp : paid g
    · simp only [hp, Bool.false_eq_true, ite_false] at hclass
      simp only [List.foldl_cons, List.filter_cons_of_neg (by simp [hp] : ¬paid g = true)]
      apply tail s
      intro v hv
      rcases List.mem_append.mp hv with h | h
      · exact hw _ h
      · obtain rfl := List.mem_singleton.mp h
        exact hclass
    · simp only [hp, ite_true] at hclass
      obtain ⟨tag,a,b,ha,hb,eq⟩ := hclass
      simp only [List.foldl_cons, List.filter_cons_of_pos (by simp [hp] : paid g = true), List.length_cons]
      apply Program.gate tag ha hb
      apply tail (insert (combine tag a b) s)
      intro v hv
      rcases List.mem_append.mp hv with h | h
      · exact availInsert _ (hw _ h)
      · obtain rfl := List.mem_singleton.mp h
        rw [eq]
        exact member (Set.mem_insert _ _)

def input {n : Nat} (i : Fin n) : Signal (Fin n → Bool) := fun x => x i

def stock (n : Nat) : Set (Signal (Fin n → Bool)) := Set.range (@input n)

theorem readValues {α : Type} (w : List (Signal α)) (x : α) (i : Nat) :
    (w.map (fun f => f x)).getD i false = readWire w i x := by
  change (w.map (fun f => f x)).getD i ((fixed false : Signal α) x) = _
  rw [List.getD_map]
  rfl

theorem evalValues {α : Type} (gs : List Gate) (w : List (Signal α)) (x : α) :
    (gs.foldl extend w).map (fun f => f x) =
      gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)])
        (w.map fun f => f x) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, extend, List.map_append, List.map_cons, List.map_nil,
      gateVal, readValues]

theorem programOf {n : Nat} (gs : List Gate) (o : Nat) (f : Signal (Fin n → Bool))
    (hg : ∀ g ∈ gs, Legal g) (he : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = f x) :
    Program (stock n) f (gs.filter paid).length := by
  let w := List.ofFn (@input n)
  have hw : ∀ u ∈ w, Available (stock n) u := by
    intro u hu
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
    exact member ⟨i, rfl⟩
  have h := rawProgram gs o hg w (stock n) hw
  have ident : readWire (gs.foldl extend w) o = f := by
    funext x
    rw [← readValues, evalValues]
    have init : (w.map fun p => p x) = List.ofFn x := by
      simp [w, List.map_ofFn, Function.comp_def, input]
    rw [init, ← he x]
    rfl
  rwa [ident] at h

def zeroAt {n : Nat} (i : Fin n) (x : Fin n → Bool) := Function.update x i false

theorem dropInput {n : Nat} (i : Fin n) {k : Nat} {f : Signal (Fin n → Bool)}
    (p : Program (stock n) f k) (x : Fin n → Bool)
    (hf : ¬ Simple (zeroAt i) (zeroAt i x) x f) :
    ∃ j < k, Program (stock n) (pull (zeroAt i) f) j := by
  apply strictRestriction (zeroAt i) (zeroAt i x) x p (stock n) _ _ hf
  · rintro _ ⟨v, rfl⟩
    by_cases eq : v = i
    · subst v
      rw [show pull (zeroAt i) (input i) = fixed false by funext y; simp [pull, zeroAt, input, fixed]]
      exact availConst _ _
    · rw [show pull (zeroAt i) (input v) = input v by funext y; simp [pull, zeroAt, input, Function.update_of_ne eq]]
      exact member ⟨v,rfl⟩
  · rintro _ ⟨v, rfl⟩
    by_cases eq : v = i
    · subst v
      exact Or.inr ⟨false, by funext y; simp [pull, zeroAt, input, fixed]⟩
    · exact Or.inl (by simp [zeroAt, input, Function.update_of_ne eq])

theorem notSimple {α β : Type} (q : β → α) (f : Signal α) (x y : α) (a b : β)
    (hc : f x ≠ f y) (hn : f (q a) ≠ f (q b)) : ¬ Simple q x y f := by
  rintro (hs | ⟨c, hb⟩)
  · exact hc hs
  · apply hn
    exact (congrFun hb a).trans (congrFun hb b).symm

end PEqualNP.Outside.L_meta_10640.Credit

namespace PEqualNP.Outside.L_meta_10640.Bridge

open PEqualNP.Outside.L_meta_10640.Credit PEqualNP.Outside.L_meta_10640.Signed

abbrev X4 := Fin 4 → Bool

def sample (k : Fin 110) (i : Fin 4) : Bool := (rows.getD i.val 0)[k.val]

def Agrees (f : Signal X4) (w : W) := ∀ k : Fin 110, w[k.val] = f (sample k)

def Represents (av : Finset W) (f : Signal X4) := ∃ w, holds av w ∧ Agrees f w

theorem onesBit : ∀ k : Fin 110, (~~~(0 : W))[k.val] = true := by decide +kernel

theorem representAvailable {s : Set (Signal X4)} {av : Finset W}
    (hs : ∀ u ∈ s, Represents av u) {f} (hf : Available s f) : Represents av f := by
  rcases hf with ⟨c,rfl⟩ | ⟨u,hu,rfl | rfl⟩
  · cases c
    · exact ⟨0, Or.inl rfl, fun _ => by simp [fixed]⟩
    · exact ⟨~~~0, Or.inr (Or.inl rfl), onesBit⟩
  · exact hs _ hu
  · obtain ⟨w, hw, hv⟩ := hs _ hu
    exact ⟨~~~w, holds_not hw, fun k => by simp [inverse, ← hv k]⟩

theorem simulate {s : Set (Signal X4)} {f k} (p : Program s f k) :
    ∀ (_target : ∀ i : Fin 110, f (sample i) = (~~~goal)[i.val])
      (av : Finset W), (∀ u ∈ s, Represents av u) →
      ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t k av := by
  induction p with
  | done h =>
    intro target av hs
    obtain ⟨w,hw,hv⟩ := representAvailable hs h
    have eq : w = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      exact (hv ⟨i,hi⟩).trans (target ⟨i,hi⟩)
    rw [eq] at hw
    rcases hw with hz | ho | ⟨t,ht,he | he⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) hz)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ho)
    · exact ⟨t, .inr he.symm, ht⟩
    · exact ⟨t, .inl (by simpa using congrArg (fun v : W => ~~~v) he.symm), ht⟩
  | @gate s f a b k tag ha hb tail ih =>
    intro target av hs
    obtain ⟨u,hu,ua⟩ := representAvailable hs ha
    obtain ⟨v,hv,vb⟩ := representAvailable hs hb
    let z := if tag then u &&& v else u ||| v
    have rz : reachable av z := by
      cases tag <;> first | exact or_reach hu hv | exact and_reach hu hv
    have az : Agrees (combine tag a b) z := by
      intro i
      cases tag <;> simp [z, combine, ua i, vb i]
    have follow (av' : Finset W) (old : ∀ u ∈ s, Represents av' u) (new : holds av' z) :=
      ih target av' (fun q hq => by
        rcases Set.mem_insert_iff.mp hq with rfl | h
        · exact ⟨z, new, az⟩
        · exact old _ h)
    rcases rz with same | ⟨x,hx,y,hy,ne,res,op,new⟩
    · obtain ⟨t,ht,run⟩ := follow av hs same
      exact ⟨t,ht,Or.inl run⟩
    · have old (q) (hq : q ∈ s) : Represents (insert res av) q := by
        obtain ⟨w,hw,eq⟩ := hs q hq
        exact ⟨w,holds_insert hw,eq⟩
      obtain ⟨t,ht,run⟩ := follow (insert res av) old new
      exact ⟨t,ht,Or.inr ⟨x,hx,y,hy,ne,res,op,run⟩⟩

def clique4 (x : X4) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 3) || (x 2 && x 3)

theorem targetRows : ∀ i : Fin 110, clique4 (sample i) = (~~~goal)[i.val] := by decide +kernel

theorem inRows : ∀ i : Fin 4, rows.getD i.val 0 ∈ rows.toFinset := by decide +kernel

theorem seven {k : Nat} (p : Program (Set.range (fun (i : Fin 4) (x : X4) => x i)) clique4 k) :
    7 ≤ k := by
  by_contra! short
  obtain ⟨t,ht,run⟩ := simulate p targetRows rows.toFinset (fun f hf => by
    obtain ⟨i,rfl⟩ := hf
    exact ⟨rows.getD i.val 0, .inr (.inr ⟨_,inRows i,.inl rfl⟩), fun _ => rfl⟩)
  have lift {j q : Nat} (h : j ≤ q) (hp : build basicOps t j rows.toFinset) :
      build basicOps t q rows.toFinset := by
    induction h with
    | refl => exact hp
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 6 rows (by decide) (lift (by omega) run)))

end PEqualNP.Outside.L_meta_10640.Bridge

namespace PEqualNP.Outside.L_meta_10640.Five

open PEqualNP.Outside.L_meta_10640.Credit
open PEqualNP.Outside.L_meta_10640.Bridge

abbrev X5 := Fin 5 → Bool

def clique5 (x : X5) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 3) || (x 1 && x 4) || (x 2 && x 3) || (x 2 && x 4) || (x 3 && x 4)

def lit5 (i : Fin 12) : Signal X5 := ![fixed false, fixed true, input 0, input 1, input 2, input 3, input 4,
    inverse (input 0), inverse (input 1), inverse (input 2), inverse (input 3), inverse (input 4)] i

def lit4 (i : Fin 10) : Signal X4 := ![fixed false, fixed true, input 0, input 1, input 2, input 3,
    inverse (input 0), inverse (input 1), inverse (input 2), inverse (input 3)] i

theorem possible {a : Signal X5} (ha : Available (stock 5) a) : ∃ j, a = lit5 j := by
  rcases ha with ⟨b,rfl⟩ | ⟨u, ⟨i,rfl⟩, rfl | rfl⟩
  · cases b
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
  · fin_cases i <;> first
      | exact ⟨2, rfl⟩
      | exact ⟨3, rfl⟩
      | exact ⟨4, rfl⟩
      | exact ⟨5, rfl⟩
      | exact ⟨6, rfl⟩
  · fin_cases i <;> first
      | exact ⟨7, rfl⟩
      | exact ⟨8, rfl⟩
      | exact ⟨9, rfl⟩
      | exact ⟨10, rfl⟩
      | exact ⟨11, rfl⟩

theorem lit4Avail (j : Fin 10) : Available (stock 4) (lit4 j) := by
  fin_cases j <;> first
    | exact availConst _ false
    | exact availConst _ true
    | exact member (s := stock 4) ⟨(0 : Fin 4), rfl⟩
    | exact member (s := stock 4) ⟨(1 : Fin 4), rfl⟩
    | exact member (s := stock 4) ⟨(2 : Fin 4), rfl⟩
    | exact member (s := stock 4) ⟨(3 : Fin 4), rfl⟩
    | exact availNeg (member (s := stock 4) ⟨(0 : Fin 4), rfl⟩)
    | exact availNeg (member (s := stock 4) ⟨(1 : Fin 4), rfl⟩)
    | exact availNeg (member (s := stock 4) ⟨(2 : Fin 4), rfl⟩)
    | exact availNeg (member (s := stock 4) ⟨(3 : Fin 4), rfl⟩)

def index4 (v i : Fin 5) : Fin 4 := ⟨(if i < v then i.val else i.val - 1) % 4, Nat.mod_lt _ (by decide)⟩

def erase (v : Fin 5) (z : X4) (i : Fin 5) : Bool :=
  if i = v then false else z (index4 v i)

def single (p : Fin 5) (i : Fin 5) : Bool := decide (i = p)

def double (p v : Fin 5) (i : Fin 5) : Bool := decide (i = p ∨ i = v)

def codes : List Nat :=
  [   5, 30, 5, 55, 80, 105, 130, 30, 155, 180, 205, 230, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30,
   5, 30, 5, 55, 85, 115, 145, 30, 160, 180, 205, 230, 55, 30, 55, 55, 86, 116, 146, 30, 30, 176, 201, 226,
   80, 30, 85, 86, 80, 117, 147, 30, 26, 30, 202, 227, 105, 30, 115, 116, 117, 105, 148, 30, 26, 27, 30, 228,
   130, 30, 145, 146, 147, 148, 130, 30, 26, 27, 28, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30,
   155, 30, 160, 30, 26, 26, 26, 30, 155, 26, 26, 26, 180, 30, 180, 176, 30, 27, 27, 30, 26, 180, 27, 27,
   205, 30, 205, 201, 202, 30, 28, 30, 26, 27, 205, 28, 230, 30, 230, 226, 227, 228, 30, 30, 26, 27, 28, 230,
   5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 30, 5, 55, 80, 105, 130, 30, 155, 180, 205, 230,
   5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 55, 5, 55, 1, 1, 1, 60, 5, 1, 1, 1,
   5, 80, 5, 1, 80, 2, 2, 80, 76, 5, 2, 2, 5, 105, 5, 1, 2, 105, 3, 105, 101, 102, 5, 3,
   5, 130, 5, 1, 2, 3, 130, 130, 126, 127, 128, 5, 5, 30, 5, 60, 80, 105, 130, 30, 155, 185, 215, 245,
   5, 155, 5, 5, 76, 101, 126, 155, 155, 186, 216, 246, 5, 180, 5, 1, 5, 102, 127, 185, 186, 180, 217, 247,
   5, 205, 5, 1, 2, 5, 128, 215, 216, 217, 205, 248, 5, 230, 5, 1, 2, 3, 5, 245, 246, 247, 248, 230]

def code (t : Bool) (a b : Fin 12) :=
  codes.getD ((if t then 144 else 0) + 12*a.val + b.val) 0

def vertex (c : Nat) : Fin 5 := ⟨c%5, Nat.mod_lt _ (by decide)⟩
def other (c : Nat) : Fin 5 := ⟨(c/5)%5, Nat.mod_lt _ (by decide)⟩
def imageLit (c : Nat) : Fin 10 := ⟨(c/25)%10, Nat.mod_lt _ (by decide)⟩

theorem certificate : ∀ (t : Bool) (a b : Fin 12),
    let c := code t a b
    let v := vertex c
    let p := other c
    let j := imageLit c
    let g := combine t (lit5 a) (lit5 b)
    p ≠ v ∧ (∀ z, g (erase v z) = lit4 j z) ∧
      (g (single p) = g (double p v) ∨ j = 0 ∨ j = 1) := by decide +kernel

theorem cofactor : ∀ v z, clique5 (erase v z) = clique4 z := by decide +kernel
theorem changed : ∀ p v, p ≠ v → clique5 (single p) ≠ clique5 (double p v) := by decide +kernel
theorem varies : ∀ v, clique5 (erase v (fun _ => false)) ≠ clique5 (erase v (fun _ => true)) := by decide +kernel
theorem notLit : ∀ j, ∃ x, clique5 x ≠ lit5 j x := by decide +kernel

theorem nine {k : Nat} (h : Program (stock 5) clique5 k) : 9 ≤ k := by
  cases h with
  | done known =>
    obtain ⟨j,eq⟩ := possible known
    obtain ⟨x,hx⟩ := notLit j
    exact False.elim (hx (congrFun eq x))
  | gate t ha hb tail =>
    obtain ⟨a,rfl⟩ := possible ha
    obtain ⟨b,rfl⟩ := possible hb
    let c := code t a b
    let v := vertex c
    let p := other c
    let j := imageLit c
    let g := combine t (lit5 a) (lit5 b)
    obtain ⟨hp,hform,hfirst⟩ := certificate t a b
    have img : pull (erase v) g = lit4 j := funext hform
    have mapped : ∀ u ∈ insert g (stock 5), Available (stock 4) (pull (erase v) u) := by
      intro u hu
      rcases Set.mem_insert_iff.mp hu with rfl | ⟨i, rfl⟩
      · rw [img]
        exact lit4Avail j
      · by_cases he : i = v
        · subst i
          rw [show pull (erase v) (input v) = fixed false by funext z; simp [pull, erase, input, fixed]]
          exact availConst _ _
        · rw [show pull (erase v) (input i) = input (index4 v i) by funext z; simp [pull, erase, input, he]]
          exact member ⟨_, rfl⟩
    have simple : ∀ u ∈ insert g (stock 5), Simple (erase v) (single p) (double p v) u := by
      intro u hu
      rcases Set.mem_insert_iff.mp hu with rfl | ⟨i,rfl⟩
      · rcases hfirst with eq | eq | eq
        · exact Or.inl eq
        · exact Or.inr ⟨false, img.trans (show lit4 j = fixed false by change j = 0 at eq; rw [eq]; rfl)⟩
        · exact Or.inr ⟨true, img.trans (show lit4 j = fixed true by change j = 1 at eq; rw [eq]; rfl)⟩
      · by_cases he : i = v
        · subst i
          exact Or.inr ⟨false, by funext z; simp [pull, erase, input, fixed]⟩
        · exact Or.inl (by simp [input, single, double, he])
    have bad := notSimple (erase v) clique5 (single p) (double p v) (fun _ => false) (fun _ => true)
      (changed p v hp) (varies v)
    obtain ⟨m,hm,prog⟩ := strictRestriction (erase v) (single p) (double p v) tail (stock 4) mapped simple bad
    rw [show pull (erase v) clique5 = clique4 from funext (cofactor v)] at prog
    have h4 := seven prog
    omega

end PEqualNP.Outside.L_meta_10640.Five

namespace PEqualNP.Outside.L_meta_10640.Main

open PEqualNP.Outside.L_meta_10640.Credit PEqualNP.Outside.L_meta_10640.Five
open PEqualNP.CircuitLowerBounds

abbrev X7 := Fin 7 → Bool

def graph (x : X7) : Bool := (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 4 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)

def listed (x : X7) : Bool := decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)

theorem same : ∀ x, listed x = graph x := by decide +kernel

def point (m : Nat) : X7 := fun i => m.testBit i.val

def f1 := pull (zeroAt (1 : Fin 7)) graph

def f13 := pull (zeroAt (3 : Fin 7)) f1

theorem firstChange : ¬ Simple (zeroAt (1 : Fin 7)) (zeroAt 1 (point 10)) (point 10) graph :=
  notSimple _ _ _ _ (point 0) (point 5) (by decide +kernel) (by decide +kernel)

theorem secondChange : ¬ Simple (zeroAt (3 : Fin 7)) (zeroAt 3 (point 72)) (point 72) f1 :=
  notSimple _ _ _ _ (point 0) (point 5) (by decide +kernel) (by decide +kernel)

def embed5 (y : X5) : X7 := ![y 0, false, y 1, false, y 2, y 3, y 4]

theorem embedGraph : ∀ y, f13 (embed5 y) = clique5 y := by decide +kernel

theorem embedStock : ∀ u ∈ stock 7, Available (stock 5) (pull embed5 u) := by
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> first
    | exact availConst _ false
    | exact member (s := stock 5) ⟨(0 : Fin 5), rfl⟩
    | exact member (s := stock 5) ⟨(1 : Fin 5), rfl⟩
    | exact member (s := stock 5) ⟨(2 : Fin 5), rfl⟩
    | exact member (s := stock 5) ⟨(3 : Fin 5), rfl⟩
    | exact member (s := stock 5) ⟨(4 : Fin 5), rfl⟩

theorem eleven {k} (p : Program (stock 7) graph k) : 11 ≤ k := by
  obtain ⟨m,hm,first⟩ := dropInput 1 p (point 10) firstChange
  obtain ⟨r,hr,second⟩ := dropInput 3 first (point 72) secondChange
  change Program (stock 7) f13 r at second
  obtain ⟨j,hj,p5,_⟩ := restrictProgram embed5 (point 0) (point 0) second (stock 5) embedStock
  rw [show pull embed5 f13 = clique5 from funext embedGraph] at p5
  have h5 := nine p5
  omega

def witness : List Gate :=
  [⟨.or, [1,6]⟩, ⟨.or, [4,5]⟩, ⟨.or, [2,5]⟩, ⟨.or, [0,4]⟩,
   ⟨.or, [0,2]⟩, ⟨.or, [8,6]⟩, ⟨.or, [3,8]⟩, ⟨.and, [13,7]⟩,
   ⟨.and, [10,9]⟩, ⟨.and, [11,12]⟩, ⟨.or, [14,15]⟩, ⟨.or, [17,16]⟩]

theorem witnessOK : ∀ g ∈ witness, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem witnessValues : ∀ x : X7, Circuit.eval ⟨witness,18⟩ (List.ofFn x) = listed x := by decide +kernel

end PEqualNP.Outside.L_meta_10640.Main

open PEqualNP.Outside.L_meta_10640.Credit PEqualNP.Outside.L_meta_10640.Main in
theorem PEqualNP.Outside.L_meta_10640 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fits _ computes
  by_cases hn : ∃ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g,hg,op⟩ := hn
    have lower := eleven (programOf gates o graph fits (fun x => (computes x).trans (same x)))
    have fewer : (gates.filter paid).length < gates.length :=
      (List.length_filter_lt_length_iff_exists (p := paid)).mpr
        ⟨g,hg,by simp [paid,op]⟩
    have hw : witness.length = 12 := rfl
    exact ⟨witness,18,witnessOK,by omega,witnessValues⟩
  · refine ⟨gates,o,?_,le_rfl,computes⟩
    intro g hg
    refine ⟨?_, (fits g hg).2⟩
    rcases (fits g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hn ⟨g,hg,h⟩)
