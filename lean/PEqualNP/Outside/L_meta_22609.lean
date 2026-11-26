import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22609_aux

open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.or, [1, 8]⟩,
    ⟨.or, [6, 5]⟩,
    ⟨.or, [0, 11]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [2, 7]⟩,
    ⟨.or, [14, 9]⟩,
    ⟨.and, [13, 15]⟩,
    ⟨.or, [16, 4]⟩,
    ⟨.or, [14, 12]⟩,
    ⟨.or, [3, 10]⟩,
    ⟨.and, [18, 19]⟩,
    ⟨.or, [17, 20]⟩], 21⟩

end PEqualNP.Outside.L_meta_22609_aux

theorem PEqualNP.Outside.L_meta_22609 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (4029433 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  exact ⟨PEqualNP.Outside.L_meta_22609_aux.circuit,
    by
      intro gate hgate
      simp only [PEqualNP.Outside.L_meta_22609_aux.circuit, List.mem_cons, List.not_mem_nil, or_false] at hgate
      rcases hgate with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp,
    by decide +kernel, by decide +kernel⟩
