import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_228

theorem one_le_rank {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (M : Matrix α β ℚ) (x : α) (y : β) (h : M x y ≠ 0) : 1 ≤ M.rank := by
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  have hb : LinearMap.range M.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h0
  have hv : M.mulVecLin (Pi.single y 1) ∈ LinearMap.range M.mulVecLin := ⟨_, rfl⟩
  rw [hb, Submodule.mem_bot] at hv
  have hx := congrFun hv x
  simp [Matrix.mulVecLin_apply, Matrix.mulVec_single] at hx
  exact h hx

theorem pos_of_dep (n : ℕ) (f : (Fin n → Bool) → Bool) (τ : (Fin n → Bool) → (Fin n → Bool) → ℕ)
    (hτ : PEqualNP.MetaComplexity.IsTyping n f τ) (i : Fin n) (x : Fin n → Bool)
    (hx : f x ≠ f (Function.update x i (!x i))) :
    1 ≤ ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix n f τ i b).rank := by
  have key : ∀ u v : Fin n → Bool, f u = true → f v = false → (∀ j, j ≠ i → u j = v j) →
      1 ≤ ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix n f τ i b).rank := by
    intro u v hu hv hdiff
    obtain ⟨j, hj, hne⟩ := hτ u v hu hv
    have hji : j = i := by
      by_contra h
      exact hne (hdiff j h)
    subst hji
    have h1 : 1 ≤ (PEqualNP.MetaComplexity.typedMatrix n f τ j (u j)).rank :=
      one_le_rank _ u v (by simp [PEqualNP.MetaComplexity.typedMatrix, hu, hv, hj])
    have h2 : (PEqualNP.MetaComplexity.typedMatrix n f τ j (u j)).rank ≤
        ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix n f τ j b).rank :=
      Finset.single_le_sum (f := fun b => (PEqualNP.MetaComplexity.typedMatrix n f τ j b).rank)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    omega
  have hupd : ∀ j, j ≠ i → x j = Function.update x i (!x i) j := by
    intro j h
    simp [Function.update_apply, h]
  cases hfx : f x <;> cases hfx' : f (Function.update x i (!x i))
  · rw [hfx, hfx'] at hx
    exact absurd rfl hx
  · exact key _ x hfx' hfx (fun j h => (hupd j h).symm)
  · exact key x _ hfx hfx' hupd
  · rw [hfx, hfx'] at hx
    exact absurd rfl hx

end PEqualNP.Outside.L_meta_228

theorem PEqualNP.Outside.L_meta_228 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ), PEqualNP.MetaComplexity.HasTypedRank n f s →
    (Finset.univ.filter (fun i : Fin n => ∃ x : Fin n → Bool, f x ≠ f (Function.update x i (!x i)))).card ≤ s := by
  rintro n f s ⟨τ, hτ, hr⟩
  calc (Finset.univ.filter (fun i : Fin n => ∃ x : Fin n → Bool, f x ≠ f (Function.update x i (!x i)))).card
      = ∑ i ∈ Finset.univ.filter (fun i : Fin n => ∃ x : Fin n → Bool, f x ≠ f (Function.update x i (!x i))), 1 := by simp
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => ∃ x : Fin n → Bool, f x ≠ f (Function.update x i (!x i))),
          ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix n f τ i b).rank := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hi).2
      exact PEqualNP.Outside.L_meta_228.pos_of_dep n f τ hτ i x hx
    _ ≤ ∑ i : Fin n, ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix n f τ i b).rank :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ ≤ s := hr
