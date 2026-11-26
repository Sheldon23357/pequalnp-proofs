import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21166 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (47863 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [5, 6]⟩, ⟨.or, [9, 4]⟩, ⟨.or, [10, 8]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [9, 7]⟩, ⟨.and, [14, 2]⟩, ⟨.or, [13, 15]⟩, ⟨.and, [4, 3]⟩, ⟨.or, [16, 17]⟩], 18⟩
  refine ⟨C, ?_, by decide +kernel, by decide +kernel⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
