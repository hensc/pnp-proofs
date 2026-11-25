import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_2233

theorem orStep_eq (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    ∃ e, orStep n cs g = cs ++ [e] ∧ ∀ x, x ∈ e ↔ (x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, (n ≤ w ∧ w < n + cs.length) ∧ x ∈ cs.getD (w - n) [])) := by
  refine ⟨_, rfl, ?_⟩
  intro x
  by_cases hop : g.op = GateOp.or
  · simp [hop, List.mem_flatMap, List.mem_filter, and_assoc]
  · simp [hop]

theorem orFold_len (n : ℕ) (l : List Gate) (cs : List (List ℕ)) :
    (l.foldl (orStep n) cs).length = cs.length + l.length := by
  induction l generalizing cs with
  | nil => simp
  | cons g l ih =>
    rw [List.foldl_cons, ih]
    obtain ⟨e, he, _⟩ := orStep_eq n cs g
    rw [he]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem orFold_prefix (n : ℕ) (l : List Gate) (cs : List (List ℕ)) :
    ∃ r, l.foldl (orStep n) cs = cs ++ r := by
  induction l generalizing cs with
  | nil => exact ⟨[], by simp⟩
  | cons g l ih =>
    obtain ⟨e, he, _⟩ := orStep_eq n cs g
    obtain ⟨r, hr⟩ := ih (orStep n cs g)
    refine ⟨[e] ++ r, ?_⟩
    rw [List.foldl_cons, hr, he, List.append_assoc]

theorem orFold_getD (n : ℕ) (l : List Gate) (cs : List (List ℕ)) (i : ℕ) (hi : i < cs.length) :
    (l.foldl (orStep n) cs).getD i [] = cs.getD i [] := by
  obtain ⟨r, hr⟩ := orFold_prefix n l cs
  rw [hr, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem orSets_len (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  unfold orSets
  rw [orFold_len]
  simp

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

-- Membership in the OR closure of gate k, read off the fold.
theorem cl_mem (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) (x : ℕ) :
    x ∈ (orSets n C).getD k [] ↔ (x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, (n ≤ w ∧ w < n + k) ∧ x ∈ (orSets n C).getD (w - n) [])) := by
  let cs := (C.gates.take k).foldl (orStep n) []
  obtain ⟨e, he, hmem⟩ := orStep_eq n cs C.gates[k]
  have hcs : cs.length = k := by
    simp only [cs, orFold_len, List.length_nil, List.length_take]
    omega
  have hsplit : orSets n C =
      (C.gates.drop (k + 1)).foldl (orStep n) ((C.gates.take (k + 1)).foldl (orStep n) []) := by
    unfold orSets
    rw [← List.foldl_append, List.take_append_drop]
  have htake : (C.gates.take (k + 1)).foldl (orStep n) [] = cs ++ [e] := by
    rw [List.take_succ, List.getElem?_eq_getElem hk, Option.toList_some, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    exact he
  have hget : ∀ i, i ≤ k → (orSets n C).getD i [] = (cs ++ [e]).getD i [] := by
    intro i hi
    rw [hsplit, htake, orFold_getD _ _ _ _ (by simp [hcs]; omega)]
  have hcsget : ∀ i, i < k → cs.getD i [] = (orSets n C).getD i [] := by
    intro i hi
    rw [hget i (by omega), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega)]
  have hek : (orSets n C).getD k [] = e := by
    rw [hget k (le_refl _), List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    simp [hcs]
  rw [hek, hmem, hcs, gateAt_eq C k hk]
  constructor
  · rintro (h | ⟨hop, w, hw, ⟨h1, h2⟩, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, ⟨h1, h2⟩, by rw [← hcsget _ (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, ⟨h1, h2⟩, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, ⟨h1, h2⟩, by rw [hcsget _ (by omega)]; exact hx⟩

theorem cl_empty (n : ℕ) (C : Circuit) (k : ℕ) (hk : C.gates.length ≤ k) :
    (orSets n C).getD k [] = [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [orSets_len]; exact hk)]
  rfl

theorem cl_bound (n : ℕ) (C : Circuit) :
    ∀ k x, x ∈ (orSets n C).getD k [] → k < C.gates.length ∧ x ≤ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x hx
    by_cases hk : k < C.gates.length
    · refine ⟨hk, ?_⟩
      rcases (cl_mem n C k hk x).mp hx with h | ⟨_, w, _, ⟨h1, h2⟩, hx'⟩
      · omega
      · have := (ih (w - n) (by omega) x hx').2
        omega
    · rw [cl_empty n C k (by omega)] at hx
      simp at hx

-- Every gate of the closure but its top is read directly by an OR gate of the closure.
theorem parent (n : ℕ) (C : Circuit) :
    ∀ k x, x ∈ (orSets n C).getD k [] → x ≠ k → ∃ h, h ∈ (orSets n C).getD k [] ∧
      h < C.gates.length ∧ (gateAt C h).op = GateOp.or ∧ n + x ∈ (gateAt C h).inputs := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x hx hxk
    have hk := (cl_bound n C k x hx).1
    rcases (cl_mem n C k hk x).mp hx with h | ⟨hop, w, hw, ⟨h1, h2⟩, hx'⟩
    · exact absurd h hxk
    · by_cases hxw : x = w - n
      · refine ⟨k, (cl_mem n C k hk k).mpr (Or.inl rfl), hk, hop, ?_⟩
        have : n + x = w := by omega
        rw [this]
        exact hw
      · obtain ⟨h, hh, hlt, hop', hin⟩ := ih (w - n) (by omega) x hx' hxw
        exact ⟨h, (cl_mem n C k hk h).mpr (Or.inr ⟨hop, w, hw, ⟨h1, h2⟩, hh⟩), hlt, hop', hin⟩

end PEqualNP.Outside.L_meta_2233

open PEqualNP.Outside.L_meta_2233

theorem PEqualNP.Outside.L_meta_2233 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ j ∈ F, j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j) → F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} + 1 := by
  classical
  intro n C F hC hF
  obtain ⟨hops, _, h2⟩ := hC
  by_cases hno : n ≤ C.output
  · let o' := C.output - n
    let K := ((orSets n C).getD o' []).toFinset
    have hOR : ∀ j, OrReaches n C C.output j ↔ j ∈ K := by
      intro j
      simp [OrReaches, hno, K, o']
    let D := K.filter (fun i => i < C.gates.length ∧ (gateAt C i).op = GateOp.or)
    have hset : {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
        OrReaches n C C.output i} = ↑D := by
      ext i
      simp only [Set.mem_setOf_eq, Finset.coe_filter, D, hOR]
      tauto
    rw [hset, Set.ncard_coe_finset]
    let A := K.filter (fun i => (gateAt C i).op = GateOp.and)
    have hFA : F ⊆ A := by
      intro j hj
      obtain ⟨_, hand, hr⟩ := hF j hj
      exact Finset.mem_filter.mpr ⟨(hOR j).mp hr, hand⟩
    have hdisj : Disjoint A D := by
      rw [Finset.disjoint_left]
      intro a ha hd
      have h1 := (Finset.mem_filter.mp ha).2
      have h2' := (Finset.mem_filter.mp hd).2.2
      rw [h1] at h2'
      cases h2'
    have hAD : A ∪ D ⊆ K := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hcard1 : F.card + D.card ≤ K.card := by
      have := Finset.card_union_of_disjoint hdisj
      have := Finset.card_le_card hAD
      have := Finset.card_le_card hFA
      omega
    have hcover : K.erase o' ⊆
        D.biUnion (fun h => ((gateAt C h).inputs.map (fun w => w - n)).toFinset) := by
      intro x hx
      obtain ⟨hxo, hxK⟩ := Finset.mem_erase.mp hx
      have hxK' : x ∈ (orSets n C).getD o' [] := List.mem_toFinset.mp hxK
      obtain ⟨h, hh, hlt, hop, hin⟩ := parent n C o' x hxK' hxo
      refine Finset.mem_biUnion.mpr ⟨h, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hh, hlt, hop⟩, ?_⟩
      rw [List.mem_toFinset, List.mem_map]
      exact ⟨n + x, hin, by omega⟩
    have hbu : (D.biUnion (fun h => ((gateAt C h).inputs.map (fun w => w - n)).toFinset)).card ≤
        2 * D.card := by
      calc _ ≤ ∑ h ∈ D, (((gateAt C h).inputs.map (fun w => w - n)).toFinset).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ h ∈ D, 2 := by
            apply Finset.sum_le_sum
            intro h hh
            have hlt := (Finset.mem_filter.mp hh).2.1
            have hl2 : (gateAt C h).inputs.length = 2 := by
              rw [gateAt_eq C h hlt]
              exact h2 _ (List.getElem_mem hlt)
            calc _ ≤ ((gateAt C h).inputs.map (fun w => w - n)).length := List.toFinset_card_le _
              _ = 2 := by rw [List.length_map, hl2]
        _ = 2 * D.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hK : K.card ≤ (K.erase o').card + 1 := by
      by_cases ho : o' ∈ K
      · rw [Finset.card_erase_of_mem ho]
        have := Finset.card_pos.mpr ⟨o', ho⟩
        omega
      · rw [Finset.erase_eq_of_notMem ho]
        omega
    have := Finset.card_le_card hcover
    omega
  · have hF0 : F = ∅ := by
      ext j
      simp only [Finset.notMem_empty, iff_false]
      intro hj
      exact hno (hF j hj).2.2.1
    simp [hF0]
