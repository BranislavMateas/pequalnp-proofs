import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_164 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) (t t1 t2 : ℕ), (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → (∃ S : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ≠ v → b ≠ v → a ∈ S ∨ b ∈ S) ∧ S.card = t1) → (∀ S : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ≠ v → b ≠ v → a ∈ S ∨ b ∈ S) → t1 ≤ S.card) → (∃ S : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ≠ v → b ≠ v → ¬ G.Adj v a → ¬ G.Adj v b → a ∈ S ∨ b ∈ S) ∧ S.card = t2) → (∀ S : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ≠ v → b ≠ v → ¬ G.Adj v a → ¬ G.Adj v b → a ∈ S ∨ b ∈ S) → t2 ≤ S.card) → t = min (t1 + 1) (t2 + (Finset.univ.filter (fun u : Fin n => G.Adj v u)).card) := by
  intro n G _ v t t1 t2 ⟨S, hS, hSc⟩ hmin ⟨S1, hS1, hS1c⟩ hmin1 ⟨S2, hS2, hS2c⟩ hmin2
  set N := Finset.univ.filter (fun u : Fin n => G.Adj v u) with hN
  have up1 : t ≤ t1 + 1 := by
    have := hmin (insert v S1) (by
      intro a b hab
      by_cases ha : a = v
      · left; simp [ha]
      by_cases hb : b = v
      · right; simp [hb]
      rcases hS1 a b hab ha hb with h | h
      · left; exact Finset.mem_insert_of_mem h
      · right; exact Finset.mem_insert_of_mem h)
    have h2 := Finset.card_insert_le v S1
    omega
  have up2 : t ≤ t2 + N.card := by
    have := hmin (S2 ∪ N) (by
      intro a b hab
      by_cases ha : a = v
      · right; subst ha; simp [hN, hab]
      by_cases hb : b = v
      · left; subst hb; simp [hN, hab.symm]
      by_cases hva : G.Adj v a
      · left; simp [hN, hva]
      by_cases hvb : G.Adj v b
      · right; simp [hN, hvb]
      rcases hS2 a b hab ha hb hva hvb with h | h
      · left; exact Finset.mem_union_left _ h
      · right; exact Finset.mem_union_left _ h)
    have h2 := Finset.card_union_le S2 N
    omega
  have low : min (t1 + 1) (t2 + N.card) ≤ t := by
    by_cases hv : v ∈ S
    · have := hmin1 (S.erase v) (by
        intro a b hab ha hb
        rcases hS a b hab with h | h
        · left; exact Finset.mem_erase.mpr ⟨ha, h⟩
        · right; exact Finset.mem_erase.mpr ⟨hb, h⟩)
      rw [Finset.card_erase_of_mem hv] at this
      have : 1 ≤ S.card := Finset.card_pos.mpr ⟨v, hv⟩
      omega
    · have hNS : N ⊆ S := by
        intro u hu
        simp only [hN, Finset.mem_filter, Finset.mem_univ, true_and] at hu
        rcases hS v u hu with h | h
        · exact absurd h hv
        · exact h
      have := hmin2 (S \ N) (by
        intro a b hab ha hb hva hvb
        rcases hS a b hab with h | h
        · left; simp [hN, h, hva]
        · right; simp [hN, h, hvb])
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hNS] at this
      have := Finset.card_le_card hNS
      omega
  omega
