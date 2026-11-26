import PEqualNP.Defs

namespace NestedFanoWitness

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover

def circuit : Circuit := ⟨[
  ⟨.or, [3, 6]⟩,
  ⟨.or, [4, 14]⟩,
  ⟨.and, [10, 15]⟩,
  ⟨.or, [0, 1]⟩,
  ⟨.and, [7, 17]⟩,
  ⟨.or, [3, 18]⟩,
  ⟨.and, [7, 19]⟩,
  ⟨.or, [9, 20]⟩,
  ⟨.or, [2, 5]⟩,
  ⟨.or, [19, 22]⟩,
  ⟨.and, [21, 23]⟩,
  ⟨.or, [1, 5]⟩,
  ⟨.or, [6, 25]⟩,
  ⟨.and, [12, 26]⟩,
  ⟨.or, [24, 27]⟩,
  ⟨.or, [0, 6]⟩,
  ⟨.or, [2, 29]⟩,
  ⟨.and, [13, 30]⟩,
  ⟨.or, [1, 2]⟩,
  ⟨.or, [4, 32]⟩,
  ⟨.and, [8, 33]⟩,
  ⟨.or, [31, 34]⟩,
  ⟨.or, [28, 35]⟩,
  ⟨.or, [16, 36]⟩,
  ⟨.or, [0, 4]⟩,
  ⟨.or, [5, 38]⟩,
  ⟨.and, [11, 39]⟩,
  ⟨.or, [37, 40]⟩], 41⟩

def rows : List ℕ := [16771220242439, 15270196031782968, 58150373818816, 94946423956573696, 54820275478360064, 3870282840506368, 133412159488, 182572334459126281, 218716039641305168, 189725234880873600, 156548607028504576, 229736628137050114, 270286071509155872, 288160007408582916]

def marked (k : ℕ) (single : Fin 14) : Prop :=
  (gateAt circuit k).op = GateOp.and ∧
  gateVal 14 circuit k (pairInput (0 : Fin 14) 7) = true ∧
  ∀ b : Fin 2, wireVal 14 circuit (opnd circuit k b) (pairInput single single) = false

private instance (k : ℕ) (s : Fin 14) : Decidable (marked k s) := by
  letI : DecidableEq GateOp := gateOpDecEq
  unfold marked
  infer_instance

def leafCount : ℕ :=
  (circuit.gates.foldl (fun (w : List ℕ) g =>
      w ++ [(g.inputs.map (fun k => w.getD k 0)).sum]) (List.replicate 14 1)).getD circuit.output 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2500000 in
theorem verified :
    circuit.size = 28 ∧ IsAO2 14 circuit ∧
    (∀ j : Fin 28, (gateAt circuit j.val).inputs.Nodup) ∧
    leafCount = 32 ∧
    (∀ k : Fin 58, circuit.eval (List.ofFn fun v : Fin 14 =>
      (rows.getD v.val 0).testBit k.val) = decide (k.val < 21)) ∧
    InCone 14 circuit 6 10 ∧
    (14 + 10 = circuit.output ∨ InCone 14 circuit 10 (circuit.output-14)) ∧
    marked 6 (0 : Fin 14) ∧ marked 10 (7 : Fin 14) := by
  decide +kernel

end NestedFanoWitness
