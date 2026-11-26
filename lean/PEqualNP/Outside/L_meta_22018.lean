import PEqualNP.Defs
import PEqualNP.Library.Helpers.Replay

namespace PEqualNP.Outside.L_meta_22018_aux

open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.not, [1]⟩,
    ⟨.and, [0, 6]⟩,
    ⟨.not, [0]⟩,
    ⟨.and, [1, 8]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [10, 5]⟩,
    ⟨.not, [11]⟩,
    ⟨.and, [2, 12]⟩,
    ⟨.or, [7, 9]⟩,
    ⟨.or, [14, 13]⟩], 15⟩

end PEqualNP.Outside.L_meta_22018_aux

theorem PEqualNP.Outside.L_meta_22018 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (20413 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨PEqualNP.Outside.L_meta_22018_aux.circuit,
    PEqualNP.Library.Helpers.Replay.fanInTwoB_sound (by decide +kernel),
    by decide +kernel, by decide +kernel⟩
