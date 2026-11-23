import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L270

open Finset PEqualNP.CircuitLowerBounds

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def read (v : ℕ → Bool) (j i : ℕ) : Bool :=
  if i < j then v i else false

private def eval (g : Gate) (v : ℕ → Bool) : Bool :=
  g.op.eval (g.inputs.map v)

private def defaultGate : Gate := ⟨.or, []⟩

private lemma fold_spec (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length ∧
    (∀ i < w.length, (gs.foldl step w).getD i false = w.getD i false) ∧
    ∀ j < gs.length, (gs.foldl step w).getD (w.length + j) false =
      eval (gs.getD j defaultGate)
        (read (fun a => (gs.foldl step w).getD a false) (w.length + j)) := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    obtain ⟨h₁, h₂, h₃⟩ := ih (step w g)
    have hl : (step w g).length = w.length + 1 := by simp [step]
    simp only [List.foldl_cons]
    refine ⟨by rw [h₁, hl]; simp; omega, ?_, ?_⟩
    · intro i hi
      rw [h₂ i (by omega)]
      exact List.getD_append _ _ _ _ hi
    · intro j hj
      cases j with
      | zero =>
        rw [Nat.add_zero, h₂ _ (by omega)]
        have hv : (step w g).getD w.length false = eval g (fun a => w.getD a false) := by
          simp [step, eval]
        rw [hv, List.getD_cons_zero]
        unfold eval
        congr 1
        apply List.map_congr_left
        intro a _
        unfold read
        split_ifs with ha
        · change w.getD a false = (gs.foldl step (step w g)).getD a false
          rw [h₂ a (by omega)]
          exact (List.getD_append _ _ _ _ ha).symm
        · exact List.getD_eq_default _ _ (by omega)
      | succ j =>
        have h := h₃ j (by simp at hj; omega)
        rw [hl] at h
        rw [List.getD_cons_succ, show w.length + (j + 1) = w.length + 1 + j by omega]
        exact h

private def value (C : Circuit) {n : ℕ} (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private def gate (C : Circuit) (n w : ℕ) : Gate :=
  C.gates.getD (w - n) defaultGate

private def Valid (C : Circuit) (n w : ℕ) : Prop :=
  n ≤ w ∧ w < n + C.gates.length

private lemma value_input (C : Circuit) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    value C x w = x ⟨w, hw⟩ := by
  change (C.gates.foldl step (List.ofFn x)).getD w false = _
  rw [(fold_spec C.gates (List.ofFn x)).2.1 _ (by simpa)]
  simp [List.getD_eq_getElem?_getD, hw]

private lemma value_missing (C : Circuit) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.gates.length ≤ w) : value C x w = false := by
  change (C.gates.foldl step (List.ofFn x)).getD w false = _
  apply List.getD_eq_default
  simpa [(fold_spec C.gates (List.ofFn x)).1] using hw

private lemma value_gate (C : Circuit) {n : ℕ} (x : Fin n → Bool) {w : ℕ}
    (hw : Valid C n w) : value C x w = eval (gate C n w) (read (value C x) w) := by
  obtain ⟨h₁, h₂⟩ := hw
  have h := (fold_spec C.gates (List.ofFn x)).2.2 (w - n) (by omega)
  rw [List.length_ofFn, show n + (w - n) = w by omega] at h
  exact h

private def Legal (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

private lemma gate_legal (C : Circuit) (hC : Legal C) {n w : ℕ} (hw : Valid C n w) :
    ((gate C n w).op = GateOp.and ∨ (gate C n w).op = GateOp.or) ∧
      (gate C n w).inputs.length = 2 := by
  obtain ⟨h₁, h₂⟩ := hw
  apply hC
  unfold gate
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  exact List.getElem_mem _

private def deps (C : Circuit) (n w : ℕ) : Finset ℕ :=
  (gate C n w).inputs.toFinset.filter (· < w)

private lemma dep_lt (C : Circuit) (n w : ℕ) : ∀ i ∈ deps C n w, i < w := by
  intro i hi
  exact (mem_filter.mp hi).2

private lemma deps_card (C : Circuit) (hC : Legal C) {n w : ℕ} (hw : Valid C n w) :
    (deps C n w).card ≤ 2 := by
  unfold deps
  exact (card_filter_le _ _).trans ((List.toFinset_card_le _).trans_eq (gate_legal C hC hw).2)

private lemma boolGate_le (g : Gate) (hOp : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hLen : g.inputs.length = 2) (x y : ℕ → Bool) (h : ∀ a ∈ g.inputs, x a ≤ y a) :
    eval g x ≤ eval g y := by
  obtain ⟨op, l⟩ := g
  change l.length = 2 at hLen
  obtain ⟨a, b, rfl⟩ : ∃ a b, l = [a, b] := by
    cases l with
    | nil => simp at hLen
    | cons a l =>
      cases l with
      | nil => simp at hLen
      | cons b l =>
        have h₀ : l = [] := by simpa using hLen
        subst l
        exact ⟨a, b, rfl⟩
  have ha := h a (by simp)
  have hb := h b (by simp)
  rcases hOp with hOp | hOp
  all_goals
    change op = _ at hOp
    subst op
    simp only [eval, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
      List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false]
    clear h
    generalize x a = xa at ha ⊢
    generalize y a = ya at ha ⊢
    generalize x b = xb at hb ⊢
    generalize y b = yb at hb ⊢
    cases xa <;> cases ya <;> cases xb <;> cases yb <;>
      first | decide | exact False.elim ((by decide : ¬ (true ≤ false)) ha)
                    | exact False.elim ((by decide : ¬ (true ≤ false)) hb)

private lemma value_step_le (C : Circuit) (hC : Legal C) {n : ℕ} (x y : Fin n → Bool)
    {w : ℕ} (hw : Valid C n w) (h : ∀ a ∈ deps C n w, value C x a ≤ value C y a) :
    value C x w ≤ value C y w := by
  rw [value_gate C x hw, value_gate C y hw]
  obtain ⟨hOp, hLen⟩ := gate_legal C hC hw
  apply boolGate_le _ hOp hLen
  intro a ha
  unfold read
  split_ifs with ht
  · exact h a (mem_filter.mpr ⟨List.mem_toFinset.mpr ha, ht⟩)
  · rfl

private lemma value_mono (C : Circuit) (hC : Legal C) {n : ℕ} {x y : Fin n → Bool}
    (h : ∀ p, x p ≤ y p) (w : ℕ) : value C x w ≤ value C y w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hin : w < n
    · rw [value_input C x w hin, value_input C y w hin]
      exact h _
    by_cases hout : n + C.gates.length ≤ w
    · rw [value_missing C x w hout, value_missing C y w hout]
    apply value_step_le C hC x y ⟨by omega, by omega⟩
    exact fun a ha => ih a (dep_lt C n w a ha)

private lemma cut (P : ℕ → Prop) [DecidablePred P] (d : ℕ → Finset ℕ)
    (hd : ∀ w, P w → (d w).card ≤ 2)
    (hlt : ∀ w, ∀ a ∈ d w, a < w)
    (b : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, P w → w < b) :
    ∃ B : Finset ℕ, (∀ w ∈ B, ¬P w) ∧ B.card ≤ F.card + ((range b).filter P).card ∧
      ∀ R : ℕ → Prop, (∀ w, P w → (∀ a ∈ d w, R a) → R w) →
        (∀ w ∈ B, R w) → ∀ w ∈ F, R w := by
  induction b generalizing F with
  | zero =>
    exact ⟨F, fun w hw hp => (Nat.not_lt_zero _ (hF w hw hp)).elim, by simp, fun _ _ h => h⟩
  | succ b ih =>
    have hfilt : (range b).filter P ⊆ (range (b + 1)).filter P :=
      filter_subset_filter _ (range_mono (by omega))
    by_cases ht : b ∈ F ∧ P b
    · obtain ⟨hb, hp⟩ := ht
      let G := F.erase b ∪ d b
      have hG : ∀ w ∈ G, P w → w < b := by
        intro w hw hP
        rcases mem_union.mp hw with hw | hw
        · obtain ⟨hne, hwF⟩ := mem_erase.mp hw
          have := hF w hwF hP
          omega
        · exact hlt b w hw
      obtain ⟨B, hB, hCard, hLift⟩ := ih G hG
      refine ⟨B, hB, ?_, ?_⟩
      · have hGcard := (card_union_le (F.erase b) (d b))
        rw [card_erase_of_mem hb] at hGcard
        have hFpos := card_pos.mpr ⟨b, hb⟩
        have hdcard := hd b hp
        have hBudget : ((range (b + 1)).filter P).card = ((range b).filter P).card + 1 := by
          rw [range_add_one, filter_insert, ite_eq_left hp, card_insert_of_notMem]
          simp
        change B.card ≤ F.card + ((range (b + 1)).filter P).card
        rw [hBudget]
        change B.card ≤ (F.erase b ∪ d b).card + ((range b).filter P).card at hCard
        omega
      · intro R hR hBC w hw
        by_cases he : w = b
        · subst w
          exact hR b hp (fun a ha => hLift R hR hBC a (mem_union_right _ ha))
        · exact hLift R hR hBC w (mem_union_left _ (mem_erase.mpr ⟨he, hw⟩))
    · have hF' : ∀ w ∈ F, P w → w < b := by
        intro w hw hp
        have hne : w ≠ b := fun he => ht ⟨he ▸ hw, he ▸ hp⟩
        have := hF w hw hp
        omega
      obtain ⟨B, hB, hCard, hLift⟩ := ih F hF'
      exact ⟨B, hB, hCard.trans (Nat.add_le_add_left (card_le_card hfilt) _), hLift⟩

private def single {n : ℕ} (p q : Fin n) : Bool :=
  decide (q = p)

private def support (C : Circuit) (n w : ℕ) : Finset (Fin n) :=
  univ.filter (fun p => value C (single p) w = true)

private lemma mem_support (C : Circuit) (n w : ℕ) (p : Fin n) :
    p ∈ support C n w ↔ value C (single p) w = true := by simp [support]

private lemma valid_of_card (C : Circuit) (n w : ℕ) (hw : 2 ≤ (support C n w).card) :
    Valid C n w := by
  constructor
  · by_contra! hi
    have he : support C n w = {⟨w, hi⟩} := by
      ext p
      rw [mem_support, value_input C (single p) w hi, mem_singleton]
      simp [single, eq_comm]
    simp [he] at hw
  · by_contra! hi
    have he : support C n w = ∅ := by
      ext p
      rw [mem_support, value_missing C (single p) w hi]
      simp
    simp [he] at hw

private def Private (C : Circuit) {n : ℕ} (S : Finset (Fin n)) (w : ℕ) : Prop :=
  Valid C n w ∧ support C n w ⊆ S ∧ 2 ≤ (support C n w).card

private noncomputable def privateWires (C : Circuit) {n : ℕ} (S : Finset (Fin n)) :
    Finset ℕ := by
  classical
  exact (range (n + C.gates.length)).filter (Private C S)

private lemma mem_privateWires (C : Circuit) {n : ℕ} (S : Finset (Fin n)) (w : ℕ) :
    w ∈ privateWires C S ↔ Private C S w := by
  classical
  unfold privateWires
  constructor
  · exact fun h => (mem_filter.mp h).2
  · exact fun h => mem_filter.mpr ⟨mem_range.mpr h.1.2, h⟩

private noncomputable def outsidePoint (C : Circuit) {n : ℕ} (S : Finset (Fin n)) (w : ℕ) :
    Finset (Fin n) := by
  classical
  exact if h : ∃ p, p ∈ support C n w ∧ p ∉ S then {Classical.choose h} else ∅

private lemma outsidePoint_card (C : Circuit) {n : ℕ} (S : Finset (Fin n)) (w : ℕ) :
    (outsidePoint C S w).card ≤ 1 := by
  classical
  unfold outsidePoint
  split <;> simp

private lemma outsidePoint_disjoint (C : Circuit) {n : ℕ} (S : Finset (Fin n)) (w : ℕ)
    {p : Fin n} (hp : p ∈ outsidePoint C S w) : p ∉ S := by
  classical
  unfold outsidePoint at hp
  split at hp
  · rename_i h
    rw [mem_singleton] at hp
    rw [hp]
    exact (Classical.choose_spec h).2
  · simp at hp

private lemma outsidePoint_hit (C : Circuit) {n : ℕ} (S : Finset (Fin n)) (w : ℕ)
    (hw : ¬ support C n w ⊆ S) :
    ∃ p ∈ outsidePoint C S w, p ∈ support C n w := by
  classical
  have h : ∃ p, p ∈ support C n w ∧ p ∉ S := by
    by_contra! hh
    exact hw (fun p hp => hh p hp)
  refine ⟨Classical.choose h, ?_, (Classical.choose_spec h).1⟩
  simp [outsidePoint, h]

private lemma one_output (C : Circuit) (hC : Legal C) {n k c : ℕ} (S : Finset (Fin n))
    (o : ℕ) (hSingle : ∀ p : Fin n, value C (single p) o = true ↔ p ∈ S)
    (hSparse : ∀ x : Fin n → Bool, (univ.filter fun p => x p = true).card ≤ k →
      (∀ p ∈ S, x p = false) → value C x o = false)
    (hk : c ≤ k) (hc : c + 1 ≤ S.card) : c ≤ (privateWires C S).card := by
  classical
  by_contra! hFew
  obtain ⟨B, hB, hCard, hLift⟩ := cut (Private C S) (deps C n)
    (fun w hw => deps_card C hC hw.1) (dep_lt C n) (n + C.gates.length)
    {o} (fun w _ hw => hw.1.2)
  change B.card ≤ ({o} : Finset ℕ).card + (privateWires C S).card at hCard
  simp only [card_singleton] at hCard
  have hBk : B.card ≤ k := by omega
  have hBS : B.card < S.card := by omega
  let inside := B.filter (fun w => support C n w ⊆ S)
  let U := inside.biUnion (support C n)
  have hU : U.card ≤ B.card := by
    calc
      U.card ≤ inside.card * 1 := by
        apply card_biUnion_le_card_mul
        intro w hw
        obtain ⟨hwB, hwS⟩ := mem_filter.mp hw
        by_contra! hbig
        have hbig' : 2 ≤ (support C n w).card := by omega
        exact hB w hwB ⟨valid_of_card C n w hbig', hwS, hbig'⟩
      _ ≤ B.card := by simpa [inside] using card_filter_le B (fun w => support C n w ⊆ S)
  obtain ⟨p, hpS, hpU⟩ : ∃ p ∈ S, p ∉ U := by
    by_contra! h
    exact (not_le_of_gt (hU.trans_lt hBS)) (card_le_card h)
  let X := B.biUnion (outsidePoint C S)
  let x : Fin n → Bool := fun q => decide (q ∈ X)
  have hX : X.card ≤ B.card := by
    simpa using card_biUnion_le_card_mul B (outsidePoint C S) 1
      (fun w _ => outsidePoint_card C S w)
  have hxf : (univ.filter fun p => x p = true) = X := by ext q; simp [x]
  have hxS : ∀ q ∈ S, x q = false := by
    intro q hq
    have hn : q ∉ X := by
      intro hx
      obtain ⟨w, _, hw⟩ := mem_biUnion.mp hx
      exact outsidePoint_disjoint C S w hw hq
    simp [x, hn]
  have hAtX : value C x o = false := hSparse x (hxf ▸ hX.trans hBk) hxS
  have hAtP : value C (single p) o = true := (hSingle p).mpr hpS
  have hCompare : value C (single p) o ≤ value C x o := by
    apply hLift (fun w => value C (single p) w ≤ value C x w)
    · exact fun w hw => value_step_le C hC (single p) x hw.1
    · intro w hw
      by_cases hin : support C n w ⊆ S
      · have hnp : p ∉ support C n w := by
          intro hp
          exact hpU (mem_biUnion.mpr ⟨w, mem_filter.mpr ⟨hw, hin⟩, hp⟩)
        have he : value C (single p) w = false := by
          simpa [mem_support] using hnp
        simp [he]
      · obtain ⟨q, hqO, hqW⟩ := outsidePoint_hit C S w hin
        have hqX : q ∈ X := mem_biUnion.mpr ⟨w, hw, hqO⟩
        have hm : ∀ r, single q r ≤ x r := by
          intro r
          by_cases hr : r = q <;> simp [single, x, hr, hqX]
        have hv := value_mono C hC hm w
        rw [(mem_support C n w q).mp hqW] at hv
        have he : value C x w = true := by
          cases h : value C x w with
          | false => exact False.elim ((by decide : ¬ (true ≤ false)) (h ▸ hv))
          | true => rfl
        simp [he]
    · exact mem_singleton_self o
  rw [hAtX, hAtP] at hCompare
  exact (by decide : ¬ (true ≤ false)) hCompare

private lemma all_outputs {n m k : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o c : Fin m → ℕ) (hPair : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hC : Legal C) (hSingle : ∀ (i : Fin m) (p : Fin n), value C (single p) (o i) = true ↔ p ∈ S i)
    (hSparse : ∀ (i : Fin m) (x : Fin n → Bool), (univ.filter fun p => x p = true).card ≤ k →
      (∀ p ∈ S i, x p = false) → value C x (o i) = false)
    (hk : ∀ i, c i ≤ k) (hc : ∀ i, c i + 1 ≤ (S i).card) :
    ∑ i, c i ≤ C.size := by
  classical
  let F := fun i => privateWires C (S i)
  have hDisj : ((univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint F := by
    intro i _ j _ hij
    apply disjoint_left.mpr
    intro w hi hj
    obtain ⟨_, hiS, hCard⟩ := (mem_privateWires C (S i) w).mp hi
    obtain ⟨_, hjS, _⟩ := (mem_privateWires C (S j) w).mp hj
    have hle : (support C n w).card ≤ (S i ∩ S j).card :=
      card_le_card (fun p hp => mem_inter.mpr ⟨hiS hp, hjS hp⟩)
    have := hPair i j hij
    omega
  have hSub : univ.biUnion F ⊆ Ico n (n + C.gates.length) := by
    intro w hw
    obtain ⟨i, _, hwi⟩ := mem_biUnion.mp hw
    exact mem_Ico.mpr ((mem_privateWires C (S i) w).mp hwi).1
  calc
    (∑ i, c i) ≤ ∑ i, (F i).card :=
      sum_le_sum (fun i _ => one_output C hC (S i) (o i) (hSingle i) (hSparse i) (hk i) (hc i))
    _ = (univ.biUnion F).card := (card_biUnion hDisj).symm
    _ ≤ (Ico n (n + C.gates.length)).card := card_le_card hSub
    _ = C.size := by simp [Circuit.size]

end PEqualNP.Outside.L270

theorem PEqualNP.Outside.L_meta_270 : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size := by
  intro n m k S C o c hPair _ hC hSingle hSparse hk hc
  exact PEqualNP.Outside.L270.all_outputs S C o c hPair hC hSingle hSparse hk hc
