import PEqualNP.Defs

-- Circuit transported by a bipartite graph isomorphism from upstream public contribution L_meta_19961.
theorem PEqualNP.Outside.L_meta_20251 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14662300726579244910 : ℕ).testBit (8 * u.val + v.val)) 30 := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [15, 0]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [5, 11]⟩, ⟨.or, [11, 4]⟩, ⟨.or, [7, 13]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [8, 6]⟩, ⟨.or, [10, 4]⟩, ⟨.or, [21, 12]⟩, ⟨.or, [5, 3]⟩, ⟨.or, [14, 17]⟩, ⟨.or, [1, 16]⟩, ⟨.or, [26, 27]⟩, ⟨.or, [25, 28]⟩, ⟨.or, [22, 16]⟩, ⟨.or, [20, 3]⟩, ⟨.and, [20, 28]⟩, ⟨.or, [30, 32]⟩, ⟨.or, [21, 25]⟩, ⟨.and, [23, 29]⟩, ⟨.or, [24, 1]⟩, ⟨.or, [27, 12]⟩, ⟨.and, [34, 37]⟩, ⟨.or, [31, 14]⟩, ⟨.or, [33, 18]⟩, ⟨.and, [40, 39]⟩, ⟨.and, [22, 36]⟩, ⟨.or, [38, 35]⟩, ⟨.or, [42, 41]⟩, ⟨.or, [44, 43]⟩], 45⟩
  refine ⟨C, ?_, by decide +kernel, by decide +kernel⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
