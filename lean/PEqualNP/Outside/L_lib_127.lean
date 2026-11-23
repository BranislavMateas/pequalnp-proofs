import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_127

theorem hall (n : ℕ) (π : Equiv.Perm (Fin n × Bool)) :
    ∃ f : Fin n → Fin n, Function.Injective f ∧
      ∀ ρ, f ρ ∈ ({(π (ρ, false)).1, (π (ρ, true)).1} : Finset (Fin n)) := by
  rw [← Finset.all_card_le_biUnion_card_iff_exists_injective]
  intro s
  have key : (s ×ˢ (Finset.univ : Finset Bool)).card ≤
      2 * (s.biUnion fun ρ => ({(π (ρ, false)).1, (π (ρ, true)).1} : Finset (Fin n))).card := by
    apply Finset.card_le_mul_card_image_of_maps_to (f := fun p => (π p).1)
    · rintro ⟨ρ, β⟩ hp
      simp only [Finset.mem_product, Finset.mem_univ, and_true] at hp
      simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
      refine ⟨ρ, hp, ?_⟩
      cases β <;> simp
    · intro y _
      calc ((s ×ˢ (Finset.univ : Finset Bool)).filter (fun p => (π p).1 = y)).card
          ≤ ((({(y, false), (y, true)} : Finset (Fin n × Bool))).image π.symm).card := by
            apply Finset.card_le_card
            intro p hp
            simp only [Finset.mem_filter] at hp
            simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
            refine ⟨π p, ?_, by simp⟩
            rcases h : (π p) with ⟨y', β'⟩
            rw [h] at hp
            simp only at hp
            obtain ⟨_, hp⟩ := hp
            subst hp
            cases β' <;> simp
        _ ≤ ({(y, false), (y, true)} : Finset (Fin n × Bool)).card := Finset.card_image_le
        _ ≤ 2 := Finset.card_le_two
  rw [Finset.card_product, Finset.card_univ, Fintype.card_bool] at key
  omega

end PEqualNP.Outside.L_lib_127

theorem PEqualNP.Outside.L_lib_127 : ∀ (n : ℕ) (π : Equiv.Perm (Fin n × Bool)), ∃ b : Fin n → Bool, ∃ π₀ π₁ : Equiv.Perm (Fin n), ∀ (ρ : Fin n) (β : Bool), (π (ρ, β)).1 = (if (β != b ρ) = true then π₁ else π₀) ρ := by
  intro n π
  obtain ⟨f, hf, hft⟩ := PEqualNP.Outside.L_lib_127.hall n π
  classical
  let b : Fin n → Bool := fun ρ => if f ρ = (π (ρ, false)).1 then false else true
  have hb : ∀ ρ, (π (ρ, b ρ)).1 = f ρ := by
    intro ρ
    have := hft ρ
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    by_cases h : f ρ = (π (ρ, false)).1
    · simp only [b, h, ite_true]
    · simp only [b, h, ite_false]
      rcases this with h' | h'
      · exact absurd h' h
      · exact h'.symm
  let g : Fin n → Fin n := fun ρ => (π (ρ, !b ρ)).1
  have hfs : Function.Surjective f := Finite.injective_iff_surjective.mp hf
  have hg : Function.Injective g := by
    intro ρ ρ' hgg
    by_contra hne
    obtain ⟨σ, hσ⟩ := hfs (g ρ)
    have e1 : (π (σ, b σ)).1 = (π (ρ, !b ρ)).1 := by rw [hb, hσ]
    have e2 : (π (ρ', !b ρ')).1 = (π (ρ, !b ρ)).1 := hgg.symm
    have d1 : (σ, b σ) ≠ (ρ, !b ρ) := by
      intro h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      cases hbs : b σ <;> simp [hbs] at h2
    have d2 : (ρ', !b ρ') ≠ (ρ, !b ρ) := by
      intro h
      exact hne (Prod.mk.injEq _ _ _ _ ▸ h).1.symm
    have d3 : (σ, b σ) ≠ (ρ', !b ρ') := by
      intro h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      cases hbs : b σ <;> simp [hbs] at h2
    have i1 : π (σ, b σ) ≠ π (ρ, !b ρ) := fun h => d1 (π.injective h)
    have i2 : π (ρ', !b ρ') ≠ π (ρ, !b ρ) := fun h => d2 (π.injective h)
    have i3 : π (σ, b σ) ≠ π (ρ', !b ρ') := fun h => d3 (π.injective h)
    revert i1 i2 i3 e1 e2
    rcases π (σ, b σ) with ⟨y1, c1⟩
    rcases π (ρ, !b ρ) with ⟨y2, c2⟩
    rcases π (ρ', !b ρ') with ⟨y3, c3⟩
    intro e1 e2 i1 i2 i3
    simp only at e1 e2
    subst e1 e2
    cases c1 <;> cases c2 <;> cases c3 <;> simp_all
  have hfb : Function.Bijective f := ⟨hf, hfs⟩
  have hgb : Function.Bijective g := ⟨hg, Finite.injective_iff_surjective.mp hg⟩
  refine ⟨b, Equiv.ofBijective f hfb, Equiv.ofBijective g hgb, ?_⟩
  intro ρ β
  cases β <;> cases hbr : b ρ
  · rw [if_neg (by decide), Equiv.ofBijective_apply, ← hb ρ, hbr]
  · rw [if_pos (by decide), Equiv.ofBijective_apply]
    simp only [g, hbr, Bool.not_true]
  · rw [if_pos (by decide), Equiv.ofBijective_apply]
    simp only [g, hbr, Bool.not_false]
  · rw [if_neg (by decide), Equiv.ofBijective_apply, ← hb ρ, hbr]
