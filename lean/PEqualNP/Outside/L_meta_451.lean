import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_451

theorem divmod (K a a' c c' : ℕ) (hc : c < K) (hc' : c' < K) (h : K * a + c = K * a' + c') :
    a = a' ∧ c = c' := by
  have hK : 0 < K := by omega
  have h1 : (K * a + c) / K = a := by
    rw [Nat.mul_add_div hK, Nat.div_eq_of_lt hc, add_zero]
  have h2 : (K * a' + c') / K = a' := by
    rw [Nat.mul_add_div hK, Nat.div_eq_of_lt hc', add_zero]
  have : a = a' := by rw [← h1, ← h2, h]
  subst this
  omega

end PEqualNP.Outside.L_meta_451

theorem PEqualNP.Outside.L_meta_451 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), u < v → H.Adj u v → 1 ≤ p → p ≤ 2 * k → Q u v p x → (S.neighborSet x).ncard = 2 := by
  intro m k H Q S hk hQ hS u v p x huv hadj hp1 hp2 hQx
  have hu := u.isLt
  have hv := v.isLt
  have huv' : u.val < v.val := huv
  have hx : x.val + 1 = m + 2 * k * (u.val * m + v.val) + p := by
    rcases (hQ u v p x).mp hQx with h | h | h <;> omega
  have decode : ∀ (u' v' : Fin m) (p' : ℕ), Q u' v' p' x → u' = u ∧ v' = v ∧ p' = p := by
    intro u' v' p' h
    have hu' := u'.isLt
    have hv' := v'.isLt
    rcases (hQ u' v' p' x).mp h with h | h | h
    · omega
    · omega
    · have e : 2 * k * (u'.val * m + v'.val) + (p' - 1) = 2 * k * (u.val * m + v.val) + (p - 1) := by
        omega
      obtain ⟨e1, e2⟩ := PEqualNP.Outside.L_meta_451.divmod (2 * k) _ _ _ _ (by omega) (by omega) e
      have e3 : m * u'.val + v'.val = m * u.val + v.val := by rw [mul_comm m, mul_comm m]; exact e1
      obtain ⟨e4, e5⟩ := PEqualNP.Outside.L_meta_451.divmod m _ _ _ _ hv' hv e3
      exact ⟨Fin.ext e4, Fin.ext e5, by omega⟩
  have hbig : u.val * m + v.val + 1 ≤ m * m := by
    have : (u.val + 1) * m ≤ m * m := Nat.mul_le_mul_right m (by omega)
    nlinarith
  have hbig2 : 2 * k * (u.val * m + v.val) + 2 * k ≤ 2 * k * (m * m) := by
    have := Nat.mul_le_mul_left (2 * k) hbig
    nlinarith
  have exQ : ∀ q, q ≤ 2 * k + 1 → ∃ y, Q u v q y := by
    intro q hq
    by_cases h0 : q = 0
    · refine ⟨⟨u.val, by omega⟩, (hQ _ _ _ _).mpr (Or.inl ⟨h0, rfl⟩)⟩
    by_cases h1 : q = 2 * k + 1
    · refine ⟨⟨v.val, by omega⟩, (hQ _ _ _ _).mpr (Or.inr (Or.inl ⟨h1, rfl⟩))⟩
    refine ⟨⟨m + 2 * k * (u.val * m + v.val) + q - 1, by omega⟩,
      (hQ _ _ _ _).mpr (Or.inr (Or.inr ⟨by omega, by omega, ?_⟩))⟩
    simp only
    omega
  have uniq : ∀ q y y', Q u v q y → Q u v q y' → y = y' := by
    intro q y y' h h'
    apply Fin.ext
    rcases (hQ _ _ _ _).mp h with h | h | h <;> rcases (hQ _ _ _ _).mp h' with h' | h' | h' <;> omega
  obtain ⟨y1, hy1⟩ := exQ (p - 1) (by omega)
  obtain ⟨y2, hy2⟩ := exQ (p + 1) (by omega)
  have hne : y1 ≠ y2 := by
    intro e
    subst e
    rcases (hQ _ _ _ _).mp hy1 with h | h | h <;> rcases (hQ _ _ _ _).mp hy2 with h' | h' | h' <;> omega
  have hset : S.neighborSet x = {y1, y2} := by
    ext y
    simp only [SimpleGraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hxy
      obtain ⟨u', v', _, _, p', hp', hh⟩ := (hS x y).mp hxy
      rcases hh with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · obtain ⟨rfl, rfl, rfl⟩ := decode u' v' p' ha
        right; exact uniq _ _ _ hb hy2
      · obtain ⟨rfl, rfl, e⟩ := decode u' v' (p' + 1) hb
        left
        have : p' = p - 1 := by omega
        subst this
        exact uniq _ _ _ ha hy1
    · rintro (rfl | rfl)
      · refine (hS x _).mpr ⟨u, v, huv, hadj, p - 1, by omega, Or.inr ⟨hy1, ?_⟩⟩
        have : p - 1 + 1 = p := by omega
        rw [this]; exact hQx
      · exact (hS x _).mpr ⟨u, v, huv, hadj, p, hp2, Or.inl ⟨hQx, hy2⟩⟩
  rw [hset, Set.ncard_pair hne]
