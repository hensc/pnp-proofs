import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1462

-- An element of the row of p that lies in a set not containing p is the pointer f i, and p is off X.
theorem row_point {n : ℕ} (X T : Finset (Fin n)) (p z q : Fin n) (hp : p ∉ T)
    (hz : z ∈ (if p ∈ X then ({p} : Finset (Fin n)) else {p, q}) ∩ T) : p ∉ X ∧ q ∈ T := by
  by_cases hX : p ∈ X
  · rw [if_pos hX] at hz
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hz
    rw [Finset.mem_singleton] at h1
    subst h1
    exact absurd h2 hp
  · rw [if_neg hX] at hz
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hz
    rw [Finset.mem_insert, Finset.mem_singleton] at h1
    rcases h1 with rfl | rfl
    · exact absurd h2 hp
    · exact ⟨hX, h2⟩

end PEqualNP.Outside.L_meta_1462

open PEqualNP.Outside.L_meta_1462

theorem PEqualNP.Outside.L_meta_1462 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (X B : Finset (Fin n))
    (r : Fin n → Fin n → Prop) (f : Fin m → Fin n),
    (∀ a b : Fin n, r a b → ¬ r b a) →
    (∀ i : Fin m, ¬ S i ⊆ X → f i ∈ B ∧ f i ∉ S i ∧ ∀ y ∈ S i ∩ B, r (f i) y) →
    (∀ (i : Fin m) (p : Fin n), p ∈ S i →
      (if p ∈ X then ({p} : Finset (Fin n)) else {p, f i}) ∩ S i = {p}) ∧
    (∀ i j : Fin m, i ≠ j → ¬ ((∃ p ∈ S i \ S j,
        ((if p ∈ X then ({p} : Finset (Fin n)) else {p, f i}) ∩ S j).Nonempty) ∧
      (∃ s ∈ S j \ S i, ((if s ∈ X then ({s} : Finset (Fin n)) else {s, f j}) ∩ S i).Nonempty))) := by
  intro n m S X B r f hanti hf
  refine ⟨?_, ?_⟩
  · intro i p hp
    by_cases hX : p ∈ X
    · rw [if_pos hX]
      ext z
      simp only [Finset.mem_inter, Finset.mem_singleton]
      constructor
      · exact fun h => h.1
      · rintro rfl
        exact ⟨rfl, hp⟩
    · rw [if_neg hX]
      have hsub : ¬ S i ⊆ X := fun h => hX (h hp)
      have hfi : f i ∉ S i := (hf i hsub).2.1
      ext z
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hz⟩
        · rfl
        · exact absurd hz hfi
      · rintro rfl
        exact ⟨Or.inl rfl, hp⟩
  · intro i j _ h
    obtain ⟨⟨p, hp, ⟨z, hz⟩⟩, ⟨s, hs, ⟨z', hz'⟩⟩⟩ := h
    obtain ⟨hpi, hpj⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hsj, hsi⟩ := Finset.mem_sdiff.mp hs
    obtain ⟨hpX, hfiSj⟩ := row_point X (S j) p z (f i) hpj hz
    obtain ⟨hsX, hfjSi⟩ := row_point X (S i) s z' (f j) hsi hz'
    have hi : ¬ S i ⊆ X := fun h => hpX (h hpi)
    have hj : ¬ S j ⊆ X := fun h => hsX (h hsj)
    obtain ⟨hfiB, _, hri⟩ := hf i hi
    obtain ⟨hfjB, _, hrj⟩ := hf j hj
    have h1 : r (f i) (f j) := hri (f j) (Finset.mem_inter.mpr ⟨hfjSi, hfjB⟩)
    have h2 : r (f j) (f i) := hrj (f i) (Finset.mem_inter.mpr ⟨hfiSj, hfiB⟩)
    exact hanti _ _ h1 h2
