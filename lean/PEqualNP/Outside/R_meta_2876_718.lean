import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_2876_718
    (synthesize : let seeds := ([95229015649944073, 63038587928642, 256463372304, 4292497062825988, 8521482511360, 14003410187716736, 55389823206179104, 189297016294080519, 155696362464215096, 218994303131713984, 183565875465424384, 229736628136996864, 270286071508729856, 288160007409369088] : List ℕ)
      ∃ (F : Finset ℕ), F.card ≤ 25 ∧
        Relation.ReflTransGen (fun (S T : Finset ℕ) =>
        ∃ a, (a ∈ seeds ∨ a ∈ S) ∧ ∃ b, (b ∈ seeds ∨ b ∈ S) ∧
          ∃ c, c ∉ S ∧ (c = a ||| b ∨ c = a &&& b) ∧ T = insert c S) ∅ F ∧
        ∃ (u v : ℕ) (k : Fin 16), u ∈ F ∧ v ∈ F ∧
          let tag := ([64, 256, 448, 1429, 1557, 2389, 3669, 1494, 1558, 1750, 1942, 2390, 2902, 1688, 1880, 2008] : List ℕ).getD k.val 0
          let i := tag % 64
          let j := tag / 64
          u.testBit i ≠ v.testBit i ∧ u.testBit i = v.testBit j ∧
            v.testBit i = u.testBit j ∧
            (if k.val < 3 then u ||| v else u &&& v) = 2097151)
    (linearize : ∀ (seeds : List ℕ) (F : Finset ℕ),
      Relation.ReflTransGen (fun (S T : Finset ℕ) =>
        ∃ a, (a ∈ seeds ∨ a ∈ S) ∧ ∃ b, (b ∈ seeds ∨ b ∈ S) ∧
          ∃ c, c ∉ S ∧ (c = a ||| b ∨ c = a &&& b) ∧ T = insert c S) ∅ F →
        ∃ g : List (Bool × ℕ × ℕ), g.length = F.card ∧
          ∀ c ∈ F, ∃ w : ℕ, seeds.length ≤ w ∧ w < seeds.length + g.length ∧
            (g.foldl (fun (ws : List ℕ) (p : Bool × ℕ × ℕ) =>
          let u := ws.getD p.2.1 0
          let v := ws.getD p.2.2 0
          ws ++ [if p.1 then u ||| v else u &&& v]) seeds).getD w 0 = c)
    (compile : ∀ (g : List (Bool × ℕ × ℕ)) (s : List ℕ),
      ∃ D : Circuit, Monotone2 D ∧ D.size = g.length ∧
        ∀ j w : ℕ, ((g.foldl (fun (ws : List ℕ) (p : Bool × ℕ × ℕ) =>
          let u := ws.getD p.2.1 0
          let v := ws.getD p.2.2 0
          ws ++ [if p.1 then u ||| v else u &&& v]) s).getD w 0).testBit j =
          (D.wires (s.map fun n => n.testBit j)).getD w false)
    (boundary : let P := fun (x : Fin 14 → Bool) =>
      ∃ u v : Fin 14, (([1408, 8832, 12544, 6272, 11264, 5632, 2816] : List ℕ).getD u.val 0).testBit v.val = true ∧ x u = true ∧ x v = true
      let row := fun (j : ℕ) (i : Fin 14) => (([95229015649944073, 63038587928642, 256463372304, 4292497062825988, 8521482511360, 14003410187716736, 55389823206179104, 189297016294080519, 155696362464215096, 218994303131713984, 183565875465424384, 229736628136996864, 270286071508729856, 288160007409369088] : List ℕ).getD i.val 0).testBit j
      ∀ x : Fin 14 → Bool,
        (Minimal P x → ∃ j : Fin 21, x = row j.val) ∧
        (Maximal (fun y => ¬ P y) x → ∃ j : Fin 37, x = row (21 + j.val))) :
    have x1 : (Fin (14 : ℕ) → Bool) → Prop := fun (x1 : Fin (14 : ℕ) → Bool) => ∃ (x2 : Fin (14 : ℕ)) (x3 : Fin (14 : ℕ)), ([(1408 : ℕ), (8832 : ℕ), (12544 : ℕ), (6272 : ℕ), (11264 : ℕ), (5632 : ℕ), (2816 : ℕ)].getD ↑x2 (0 : ℕ)).testBit ↑x3 = Bool.true ∧ x1 x2 = Bool.true ∧ x1 x3 = Bool.true; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.GateOp) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ × ℕ),   PEqualNP.MetaComplexity.Monotone2 x2 ∧     x2.size ≤ (25 : ℕ) ∧       (14 : ℕ) ≤ x4 ∧         x4 < x5 ∧           x5 < (14 : ℕ) + x2.size ∧             (x3 = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x6 ∈ [((129 : ℕ), (130 : ℕ)), ((129 : ℕ), (260 : ℕ)), ((129 : ℕ), (544 : ℕ))] ∨ x3 = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x6 ∈ [((127 : ℕ), (244 : ℕ)), ((127 : ℕ), (432 : ℕ)), ((127 : ℕ), (3716 : ℕ)), ((127 : ℕ), (16256 : ℕ)), ((244 : ℕ), (314 : ℕ)), ((244 : ℕ), (432 : ℕ)), ((244 : ℕ), (792 : ℕ)), ((244 : ℕ), (1290 : ℕ)), ((244 : ℕ), (3716 : ℕ)), ((244 : ℕ), (7426 : ℕ)), ((432 : ℕ), (660 : ℕ)), ((432 : ℕ), (1220 : ℕ)), ((432 : ℕ), (1548 : ℕ))]) ∧               have x7 : ℕ → (Fin (14 : ℕ) → Bool) → Bool := fun (x7 : ℕ) (x8 : Fin (14 : ℕ) → Bool) => (x2.wires (List.ofFn x8)).getD x7 Bool.false;               have x8 : Fin (14 : ℕ) → Bool := fun (x8 : Fin (14 : ℕ)) => x6.1.testBit ↑x8;               have x9 : Fin (14 : ℕ) → Bool := fun (x9 : Fin (14 : ℕ)) => x6.2.testBit ↑x9;               have x10 : (Fin (14 : ℕ) → Bool) → Bool := fun (x10 : Fin (14 : ℕ) → Bool) => x3.eval [x7 x4 x10, x7 x5 x10];               x7 x4 x8 ≠ x7 x5 x8 ∧ x7 x4 x8 = x7 x5 x9 ∧ x7 x5 x8 = x7 x4 x9 ∧ (∀ (x11 : Fin (14 : ℕ) → Bool), Minimal x1 x11 → x3 = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (x11 = x8 ∨ x11 = x9) ∨ x10 x11 = Bool.true) ∧ ∀ (x11 : Fin (14 : ℕ) → Bool), Maximal (fun (x12 : Fin (14 : ℕ) → Bool) => ¬x1 x12) x11 → x3 = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x11 = x8 ∨ x11 = x9) ∨ x10 x11 = Bool.false := by
  let cols := ([95229015649944073, 63038587928642, 256463372304, 4292497062825988, 8521482511360, 14003410187716736, 55389823206179104, 189297016294080519, 155696362464215096, 218994303131713984, 183565875465424384, 229736628136996864, 270286071508729856, 288160007409369088] : List ℕ)
  let row := fun (j : ℕ) (i : Fin 14) => (cols.getD i.val 0).testBit j
  let tag := fun (k : Fin 16) => ([64, 256, 448, 1429, 1557, 2389, 3669, 1494, 1558, 1750, 1942, 2390, 2902, 1688, 1880, 2008] : List ℕ).getD k.val 0
  let anchors := fun (k : Fin 16) => ([(129, 130), (129, 260), (129, 544), (127, 244), (127, 432), (127, 3716), (127, 16256), (244, 314), (244, 432), (244, 792), (244, 1290), (244, 3716), (244, 7426), (432, 660), (432, 1220), (432, 1548)] : List (ℕ × ℕ)).getD k.val (0, 0)
  let kind := fun (k : Fin 16) => if k.val < 3 then GateOp.or else GateOp.and
  have masks : ∀ (k : Fin 16) (i : Fin 14),
      (anchors k).1.testBit i.val = row (tag k % 64) i ∧
      (anchors k).2.testBit i.val = row (tag k / 64) i := by decide
  have allowed (k : Fin 16) :
      (kind k = GateOp.or ∧ anchors k ∈ ([(129, 130), (129, 260), (129, 544)] : List (ℕ × ℕ))) ∨
      (kind k = GateOp.and ∧ anchors k ∈ ([(127, 244), (127, 432), (127, 3716), (127, 16256), (244, 314), (244, 432), (244, 792), (244, 1290), (244, 3716), (244, 7426), (432, 660), (432, 1220), (432, 1548)] : List (ℕ × ℕ))) := by
    fin_cases k <;> first | exact Or.inl ⟨rfl, by decide⟩ | exact Or.inr ⟨rfl, by decide⟩
  have yesBit : ∀ j : Fin 21, (2097151 : ℕ).testBit j.val = true := by decide
  have noBit : ∀ j : Fin 37, (2097151 : ℕ).testBit (21 + j.val) = false := by decide
  obtain ⟨F, budget, reach, u₀, v₀, k, hu, hv, diff₀, crossA₀, crossB₀, result₀⟩ := synthesize
  obtain ⟨g, count, supports⟩ := linearize cols F reach
  obtain ⟨D, mono, size, reads⟩ := compile g cols
  let ws := g.foldl (fun (ws : List ℕ) (p : Bool × ℕ × ℕ) =>
          let u := ws.getD p.2.1 0
          let v := ws.getD p.2.2 0
          ws ++ [if p.1 then u ||| v else u &&& v]) cols
  obtain ⟨a₀, ha₁, ha₂, hasA⟩ := supports u₀ hu
  obtain ⟨b₀, hb₁, hb₂, hasB⟩ := supports v₀ hv
  change ws.getD a₀ 0 = u₀ at hasA
  change ws.getD b₀ 0 = v₀ at hasB
  have ab : a₀ ≠ b₀ := by
    rintro rfl
    exact diff₀ (congrArg (fun z : ℕ => z.testBit (tag k % 64)) (hasA.symm.trans hasB))
  have ordered : ∃ (a b u v : ℕ), 14 ≤ a ∧ a < b ∧ b < 14 + g.length ∧
      ws.getD a 0 = u ∧ ws.getD b 0 = v ∧
      u.testBit (tag k % 64) ≠ v.testBit (tag k % 64) ∧
      u.testBit (tag k % 64) = v.testBit (tag k / 64) ∧
      v.testBit (tag k % 64) = u.testBit (tag k / 64) ∧
      (if k.val < 3 then u ||| v else u &&& v) = 2097151 := by
    rcases lt_or_gt_of_ne ab with lt | gt
    · exact ⟨a₀, b₀, u₀, v₀, ha₁, lt, hb₂, hasA, hasB, diff₀, crossA₀, crossB₀, result₀⟩
    · refine ⟨b₀, a₀, v₀, u₀, hb₁, gt, ha₂, hasB, hasA, Ne.symm diff₀, crossB₀, crossA₀, ?_⟩
      simpa only [Nat.or_comm v₀ u₀, Nat.and_comm v₀ u₀] using result₀
  obtain ⟨a, b, u, v, first, order, last, hA, hB, diff, crossA, crossB, result⟩ := ordered
  have inputEq (j : ℕ) : List.ofFn (row j) = cols.map (fun n => n.testBit j) := by rfl
  have wire (w j : ℕ) : (D.wires (List.ofFn (row j))).getD w false =
      (ws.getD w 0).testBit j := by
    rw [inputEq]
    exact (reads j w).symm
  have out (j : ℕ) : (kind k).eval [(D.wires (List.ofFn (row j))).getD a false,
      (D.wires (List.ofFn (row j))).getD b false] = (2097151 : ℕ).testBit j := by
    rw [wire, wire, hA, hB]
    change (kind k).eval [u.testBit j, v.testBit j] = (2097151 : ℕ).testBit j
    have val : (if k.val < 3 then u ||| v else u &&& v) = 2097151 := result
    rw [← val]
    by_cases h : k.val < 3
    · simp only [kind, if_pos h, Nat.testBit_or]
      cases u.testBit j <;> cases v.testBit j <;> rfl
    · simp only [kind, if_neg h, Nat.testBit_and]
      cases u.testBit j <;> cases v.testBit j <;> rfl
  have leftRow : (fun i : Fin 14 => (anchors k).1.testBit i.val) = row (tag k % 64) :=
    funext fun i => (masks k i).1
  have rightRow : (fun i : Fin 14 => (anchors k).2.testBit i.val) = row (tag k / 64) :=
    funext fun i => (masks k i).2
  refine ⟨D, kind k, a, b, anchors k, mono, by omega, first, order,
    size ▸ last, allowed k, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [leftRow, wire, hA, hB] using (show u.testBit (tag k % 64) ≠ v.testBit (tag k % 64) from diff)
  · simpa only [leftRow, rightRow, wire, hA, hB] using (show u.testBit (tag k % 64) = v.testBit (tag k / 64) from crossA)
  · simpa only [leftRow, rightRow, wire, hA, hB] using (show v.testBit (tag k % 64) = u.testBit (tag k / 64) from crossB)
  · intro x hx
    obtain ⟨j, rfl⟩ := (boundary x).1 hx
    exact Or.inr ((out j.val).trans (yesBit j))
  · intro x hx
    obtain ⟨j, rfl⟩ := (boundary x).2 hx
    exact Or.inr ((out (21 + j.val)).trans (noBit j))
