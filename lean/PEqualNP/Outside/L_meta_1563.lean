import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Fin

namespace PEqualNP.Outside.L_meta_1563_aux

def lines (t : Fin 13) : Finset (Fin 13) := {t, t + 1, t + 3, t + 9}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 15000000 in
theorem union_card :
    (Finset.univ.filter (fun x : Fin 13 → Bool =>
      x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ lines 0 → x v = true)).card = 6148 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 15000000 in
theorem pair_card :
    (Finset.univ.filter (fun x : Fin 13 → Bool => x 0 = true ∨ x 1 = true)).card = 6144 := by
  decide +kernel

end PEqualNP.Outside.L_meta_1563_aux

open PEqualNP.Outside.L_meta_1563_aux in
theorem PEqualNP.Outside.L_meta_1563 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    (∀ x y : Fin 13 → Bool, (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → (∀ v : Fin 13, x v = true → y v = true) → (y 0 = true ∨ y 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → y v = true)) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true))).card = 6148 ∧
    (∀ t : Fin 13, ((fun v : Fin 13 => decide (v ∉ L t)) 0 = true ∨ (fun v : Fin 13 => decide (v ∉ L t)) 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → (fun v : Fin 13 => decide (v ∉ L t)) v = true)) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => x 0 = true ∨ x 1 = true)).card = 6144 ∧
    (∀ x : Fin 13 → Bool, (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) ↔ (x 0 = true ∨ x 1 = true ∨ x = (fun v : Fin 13 => decide (v ∉ L 0)) ∨
      x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 3)) ∨ x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 9)) ∨
      x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 3 ∨ v = 9)))) := by
  intro L hL
  have h : L = lines := funext hL
  subst L
  refine ⟨?_, union_card, ?_, pair_card, ?_⟩
  · intro x y hx hxy
    rcases hx with h0 | h1 | hout
    · exact Or.inl (hxy 0 h0)
    · exact Or.inr (Or.inl (hxy 1 h1))
    · exact Or.inr (Or.inr (fun v hv => hxy v (hout v hv)))
  · decide +kernel
  · intro x
    constructor
    · rintro (h0 | h1 | hout)
      · exact Or.inl h0
      · exact Or.inr (Or.inl h1)
      · by_cases h0 : x 0 = true
        · exact Or.inl h0
        by_cases h1 : x 1 = true
        · exact Or.inr (Or.inl h1)
        right; right
        have hmem (v : Fin 13) : v ∈ lines 0 ↔ v = 0 ∨ v = 1 ∨ v = 3 ∨ v = 9 := by
          simp [lines]
        have hv (v : Fin 13) (h : v ∉ lines 0) := hout v h
        by_cases h3 : x 3 = true <;> by_cases h9 : x 9 = true
        · right; right; right
          funext v
          by_cases hn : v ∈ lines 0
          · rcases (hmem v).mp hn with rfl | rfl | rfl | rfl <;> simp_all
          · simp [hn, hv v hn]
        · right; left
          funext v
          by_cases hn : v ∈ lines 0
          · rcases (hmem v).mp hn with rfl | rfl | rfl | rfl <;> simp_all
          · simp [hn, hv v hn]
        · right; right; left
          funext v
          by_cases hn : v ∈ lines 0
          · rcases (hmem v).mp hn with rfl | rfl | rfl | rfl <;> simp_all
          · simp [hn, hv v hn]
        · left
          funext v
          by_cases hn : v ∈ lines 0
          · rcases (hmem v).mp hn with rfl | rfl | rfl | rfl <;> simp_all
          · simp [hn, hv v hn]
    · rintro (h0 | h1 | rfl | rfl | rfl | rfl)
      · exact Or.inl h0
      · exact Or.inr (Or.inl h1)
      all_goals
        right; right
        intro v hv
        simp [hv]
