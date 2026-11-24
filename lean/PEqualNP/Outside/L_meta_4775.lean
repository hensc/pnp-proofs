import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_4775

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  rfl

theorem all_mono (l : List ℕ) (u v : ℕ → Bool) (h : ∀ i, u i = true → v i = true) :
    (l.map u).all id = true → (l.map v).all id = true := by
  simp only [List.all_map, List.all_eq_true, Function.comp, id]
  exact fun hu i hi => h i (hu i hi)

theorem any_mono (l : List ℕ) (u v : ℕ → Bool) (h : ∀ i, u i = true → v i = true) :
    (l.map u).any id = true → (l.map v).any id = true := by
  simp only [List.any_map, List.any_eq_true, Function.comp, id]
  exact fun ⟨i, hi, hu⟩ => ⟨i, hi, h i hu⟩

-- Every wire of an AND/OR gate list can only go up when the starting wires go up.
theorem mono_foldl (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ wx wy : List Bool, wx.length = wy.length →
      (∀ i, wx.getD i false = true → wy.getD i false = true) →
      ∀ i, (gs.foldl stepW wx).getD i false = true → (gs.foldl stepW wy).getD i false = true := by
  induction gs with
  | nil => intro wx wy _ h; exact h
  | cons g gs ih =>
    intro wx wy hl h
    rw [List.foldl_cons, List.foldl_cons]
    have hg := hgs g (by simp)
    apply ih (fun g' hg' => hgs g' (by simp [hg'])) _ _ (by simp [stepW, hl])
    intro i hi
    simp only [stepW] at hi ⊢
    rcases Nat.lt_trichotomy i wx.length with hlt | heq | hgt
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
        ← List.getD_eq_getElem?_getD] at hi
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
        ← List.getD_eq_getElem?_getD]
      exact h i hi
    · subst heq
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)] at hi
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      simp only [Nat.sub_self, hl, List.getElem?_cons_zero, Option.getD_some] at hi ⊢
      rcases hg with hop | hop
      · rw [hop] at hi ⊢
        exact all_mono _ _ _ h hi
      · rw [hop] at hi ⊢
        exact any_mono _ _ _ h hi
    · rw [getD_ge _ _ (by simp; omega)] at hi
      exact absurd hi (by simp)

end PEqualNP.Outside.L_meta_4775

open PEqualNP.Outside.L_meta_4775

theorem PEqualNP.Outside.L_meta_4775 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → ∀ (x3 x4 : Fin (14 : ℕ) → Bool), (∀ (x5 : Fin (14 : ℕ)), x3 x5 = Bool.true → x4 x5 = Bool.true) → x1.eval (List.ofFn x3) = Bool.true → x1.eval (List.ofFn x4) = Bool.true := by
  intro C hC x y hxy hx
  have hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have h := (hC g hg).1
    simpa using h
  exact mono_foldl C.gates hops (List.ofFn x) (List.ofFn y) (by simp) (by
    intro i hi
    by_cases hin : i < 14
    · rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hi ⊢
      simp only [hin, dif_pos] at hi ⊢
      exact hxy _ (by simpa using hi)
    · rw [getD_ge _ _ (by simp; omega)] at hi
      exact absurd hi (by simp)) C.output hx
