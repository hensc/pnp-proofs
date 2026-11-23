import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1451

-- One step of the wire fold of a circuit.
def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem eval_eq (gs : List Gate) (o : ℕ) (xs : List Bool) :
    Circuit.eval ⟨gs, o⟩ xs = (gs.foldl stepW xs).getD o false := rfl

theorem foldl_length (l : List Gate) (w : List Bool) :
    (l.foldl stepW w).length = w.length + l.length := by
  induction l generalizing w with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih]
    simp only [stepW, List.length_append, List.length_cons, List.length_nil]
    omega

theorem foldl_prefix (l : List Gate) (w : List Bool) : ∃ r, l.foldl stepW w = w ++ r := by
  induction l generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons a l ih =>
    obtain ⟨r, hr⟩ := ih (stepW w a)
    refine ⟨[a.op.eval (a.inputs.map fun i => w.getD i false)] ++ r, ?_⟩
    rw [List.foldl_cons, hr, stepW, List.append_assoc]

theorem getD_foldl_lt (l : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (l.foldl stepW w).getD i false = w.getD i false := by
  obtain ⟨r, hr⟩ := foldl_prefix l w
  rw [hr, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  rfl

theorem foldl_set (l : List Gate) (t : ℕ) (b : Gate) (w : List Bool) (ht : t < l.length)
    (hc : b.op.eval (b.inputs.map fun i => ((l.take t).foldl stepW w).getD i false) =
      (l[t]).op.eval ((l[t]).inputs.map fun i => ((l.take t).foldl stepW w).getD i false)) :
    (l.set t b).foldl stepW w = l.foldl stepW w := by
  induction l generalizing t w with
  | nil => simp at ht
  | cons a l ih =>
    cases t with
    | zero =>
      simp only [List.set_cons_zero, List.foldl_cons]
      simp only [List.take_zero, List.foldl_nil, List.getElem_cons_zero] at hc
      congr 1
      simp only [stepW, hc]
    | succ t =>
      simp only [List.set_cons_succ, List.foldl_cons]
      simp only [List.take_succ_cons, List.foldl_cons, List.getElem_cons_succ] at hc
      exact ih t (stepW w a) (by simpa using ht) hc

theorem mem_set_good (l : List Gate) (t : ℕ) (b : Gate) (P : Gate → Prop) (hb : P b)
    (hl : ∀ j (hj : j < l.length), j ≠ t → P l[j]) : ∀ g ∈ l.set t b, P g := by
  intro g hg
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  rw [List.getElem_set]
  split
  · exact hb
  · exact hl i (by simpa using hi) (Ne.symm ‹_›)

theorem headD_map (ins : List ℕ) (w : List Bool) (d : ℕ) (hd : w.length ≤ d) :
    (ins.map fun i => w.getD i false).headD false = w.getD (ins.headD d) false := by
  cases ins with
  | nil =>
    simp only [List.map_nil, List.headD_nil]
    exact (getD_ge w d hd).symm
  | cons a r => simp

end PEqualNP.Outside.L_meta_1451

open PEqualNP.Outside.L_meta_1451

theorem PEqualNP.Outside.L_meta_1451 : ∀ (m : ℕ) (f : (Fin m → Bool) → Bool) (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin m → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = f x) → ∃ (hg g0 g1 : List PEqualNP.CircuitLowerBounds.Gate) (ho o0 o1 : ℕ), hg.length ≤ gates.length ∧ g0.length ≤ gates.length ∧ g1.length ≤ gates.length ∧ (∀ g ∈ hg ++ g0 ++ g1, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ ∀ x : Fin m → Bool, (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨hg, ho⟩ (List.ofFn x) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨g0, o0⟩ (List.ofFn x) = f x) ∧ (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨hg, ho⟩ (List.ofFn x) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨g1, o1⟩ (List.ofFn x) = f x) := by
  intro m f gates o hops huniq hf
  by_cases hN : ∃ t : Fin gates.length, (gates.get t).op = GateOp.not
  · obtain ⟨⟨t, htl⟩, ht⟩ := hN
    simp only [List.get_eq_getElem] at ht
    have hother : ∀ j (hj : j < gates.length), j ≠ t →
        ((gates[j]).op = GateOp.and ∨ (gates[j]).op = GateOp.or) ∧ (gates[j]).inputs.length ≤ 2 := by
      intro j hj hjt
      obtain ⟨h1, h2⟩ := hops _ (List.getElem_mem hj)
      refine ⟨?_, h2⟩
      rcases h1 with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
      · exact absurd (Fin.mk.inj_iff.mp (huniq ⟨j, hj⟩ ⟨t, htl⟩ (by simpa using h1) (by simpa using ht))) hjt
    let a0 := (gates[t]).inputs.headD (m + t)
    let ho := if a0 < m + t then a0 else m + gates.length
    have orN : (⟨GateOp.or, []⟩ : Gate).op = GateOp.or ∧ ([] : List ℕ).length ≤ 2 := ⟨rfl, by simp⟩
    refine ⟨gates.set t ⟨GateOp.or, []⟩, gates.set t ⟨GateOp.or, []⟩, gates.set t ⟨GateOp.and, []⟩,
      ho, o, o, by simp, by simp, by simp, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append] at hg
      rcases hg with (hg | hg) | hg
      · exact mem_set_good gates t ⟨GateOp.or, []⟩ (fun g : Gate => (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ⟨Or.inr rfl, by simp⟩ hother g hg
      · exact mem_set_good gates t ⟨GateOp.or, []⟩ (fun g : Gate => (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ⟨Or.inr rfl, by simp⟩ hother g hg
      · exact mem_set_good gates t ⟨GateOp.and, []⟩ (fun g : Gate => (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ⟨Or.inl rfl, by simp⟩ hother g hg
    · intro x
      let wt := (gates.take t).foldl stepW (List.ofFn x)
      have hwt : wt.length = m + t := by
        simp only [wt, foldl_length, List.length_ofFn, List.length_take]
        omega
      have hnot : (gates[t]).op.eval ((gates[t]).inputs.map fun i => wt.getD i false) =
          !(wt.getD a0 false) := by
        rw [ht]
        simp only [GateOp.eval]
        rw [headD_map _ wt (m + t) (by omega)]
      have hsplit : ∀ l : List Gate, l.length = gates.length → l.take t = gates.take t →
          l.foldl stepW (List.ofFn x) = (l.drop t).foldl stepW wt := by
        intro l _ hlt
        conv_lhs => rw [← List.take_append_drop t l]
        rw [List.foldl_append, hlt]
      have hh : Circuit.eval ⟨gates.set t ⟨GateOp.or, []⟩, ho⟩ (List.ofFn x) = wt.getD a0 false := by
        rw [eval_eq, hsplit _ (by simp) (List.take_set_of_le (Nat.le_refl t))]
        by_cases ha : a0 < m + t
        · simp only [ho, ha, ite_true]
          exact getD_foldl_lt _ _ _ (by omega)
        · simp only [ho, ha, ite_false]
          rw [getD_ge _ _ (by rw [foldl_length]; simp; omega), getD_ge _ _ (by omega)]
      refine ⟨fun h1 => ?_, fun h0 => ?_⟩
      · rw [← hf x, eval_eq, eval_eq, foldl_set gates t _ _ htl]
        rw [hnot, ← hh, h1]
        rfl
      · rw [← hf x, eval_eq, eval_eq, foldl_set gates t _ _ htl]
        rw [hnot, ← hh, h0]
        rfl
  · refine ⟨gates, gates, gates, o, o, o, le_refl _, le_refl _, le_refl _, ?_, ?_⟩
    · intro g hg
      have hg' : g ∈ gates := by
        simp only [List.mem_append, or_self] at hg
        exact hg
      obtain ⟨h1, h2⟩ := hops g hg'
      refine ⟨?_, h2⟩
      rcases h1 with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg'
        exact absurd ⟨⟨i, hi⟩, by simpa using h1⟩ hN
    · intro x
      exact ⟨fun _ => hf x, fun _ => hf x⟩
