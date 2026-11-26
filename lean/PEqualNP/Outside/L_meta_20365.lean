import PEqualNP.Defs
import PEqualNP.Library.Helpers.Replay

namespace PEqualNP.Outside.L_meta_20365_aux

open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨GateOp.or, [2, 11]⟩,
  ⟨GateOp.or, [0, 16]⟩,
  ⟨GateOp.or, [0, 12]⟩,
  ⟨GateOp.or, [15, 1]⟩,
  ⟨GateOp.or, [6, 8]⟩,
  ⟨GateOp.or, [7, 14]⟩,
  ⟨GateOp.or, [5, 9]⟩,
  ⟨GateOp.or, [22, 20]⟩,
  ⟨GateOp.or, [20, 18]⟩,
  ⟨GateOp.or, [13, 3]⟩,
  ⟨GateOp.or, [21, 22]⟩,
  ⟨GateOp.or, [23, 16]⟩,
  ⟨GateOp.or, [12, 19]⟩,
  ⟨GateOp.or, [23, 4]⟩,
  ⟨GateOp.or, [19, 4]⟩,
  ⟨GateOp.and, [25, 27]⟩,
  ⟨GateOp.and, [28, 21]⟩,
  ⟨GateOp.and, [17, 26]⟩,
  ⟨GateOp.and, [29, 10]⟩,
  ⟨GateOp.and, [24, 30]⟩,
  ⟨GateOp.or, [31, 32]⟩,
  ⟨GateOp.or, [36, 33]⟩,
  ⟨GateOp.or, [37, 34]⟩,
  ⟨GateOp.or, [38, 35]⟩], 39⟩

end PEqualNP.Outside.L_meta_20365_aux

set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.L_meta_20365 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10998964658842522050 : ℕ).testBit (8 * u.val + v.val)) 24 := by
  refine ⟨PEqualNP.Outside.L_meta_20365_aux.circuit, PEqualNP.Library.Helpers.Replay.monotone2B_sound (by decide +kernel), by decide +kernel, ?_⟩
  decide +kernel
