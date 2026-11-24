import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

-- A dirty AND gate accepts some input that contains no edge.
-- Reduce their number until at most one remains, keeping the size bound.
theorem PEqualNP.Outside.R_meta_612_3 :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∃ u v, G.Adj u v) → NoFourCycle G → Monotone2 C →
      circuitFun n C = graphFun G ∅ → 2 ≤ (junk G C).card →
      ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
        D.size ≤ C.size ∧ (junk G D).card < (junk G C).card) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∃ u v, G.Adj u v) → NoFourCycle G → Monotone2 C →
      circuitFun n C = graphFun G ∅ → (junk G C).card ≤ 1 →
      ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧
        G.edgeSet.ncard + S.card ≤ C.size + 1) →
    ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∃ u v : Fin n, G.Adj u v) → (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → G.edgeSet.ncard + t ≤ C.size + 1 := by
  classical
  intro descend count n t G C hedge hfour _ hmin hmono heval
  have hc4 : NoFourCycle G := by
    intro a b hab
    apply Finset.card_le_one.mpr
    intro u hu v hv
    have hu' := (Finset.mem_filter.mp hu).2
    have hv' := (Finset.mem_filter.mp hv).2
    by_contra huv
    exact hfour a u b v hu'.1.ne hab hv'.1.ne hu'.2.ne.symm huv hv'.2.ne
      hu'.1 hu'.2.symm hv'.2 hv'.1.symm
  have computes : circuitFun n C = graphFun G ∅ := by
    funext x
    by_cases h : ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true
    · simp [circuitFun, graphFun, h, (heval x).mpr h]
    · have hf : C.eval (List.ofFn x) = false := by
        cases e : C.eval (List.ofFn x) with
        | false => rfl
        | true => exact (h ((heval x).mp e)).elim
      simp [circuitFun, graphFun, h, hf]
  have bound : ∀ k : ℕ, ∀ D : Circuit, (junk G D).card = k → Monotone2 D →
      circuitFun n D = graphFun G ∅ → G.edgeSet.ncard + t ≤ D.size + 1 := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k smaller =>
      intro D hk hm hf
      by_cases few : (junk G D).card ≤ 1
      · obtain ⟨S, cover, cost⟩ := count n G D hedge hc4 hm hf few
        exact (Nat.add_le_add_left (hmin S cover) _).trans cost
      · obtain ⟨D', hm', hf', size, less⟩ :=
          descend n G D hedge hc4 hm hf (by omega)
        exact (smaller _ (hk ▸ less) D' rfl hm' hf').trans (Nat.add_le_add_right size 1)
  exact bound _ C rfl hmono computes
