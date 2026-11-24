module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlocksUnique
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalInvariantsMatchSemisimple
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SignAtBasePlaceEqEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingSpecNormalisedCharacterEq
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwInputs.Move GlobalTheory.HeightCounting.SideCopy
attribute [local instance] Formalism.BasicNotions.Host.cmStar


private theorem multiset_eq_of_esymm (M M' : Multiset ℂ) (r : ℕ) (h1 : M.card = r) (h2 : M'.card = r)
    (h : ∀ k, 1 ≤ k → k ≤ r → M.esymm k = M'.esymm k) : M = M' := by
  have hp : (M.map fun a => Polynomial.X - Polynomial.C a).prod = (M'.map fun a => Polynomial.X - Polynomial.C a).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm, h1, h2]
    refine Finset.sum_congr rfl fun k hk => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [Multiset.esymm]
    · rw [h k hk0 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
  rw [← Polynomial.roots_multiset_prod_X_sub_C M, hp, Polynomial.roots_multiset_prod_X_sub_C]

private theorem isRepOf_of_split (D : D7) {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (π : D.naut.CG n) (s : ℝ)
    (hC : GlobalTheory.RowTie.ChebSplit D.nd) (ρ₁ ρ₂ : G D.host.E D.nd.Om →* GL (Fin n) (Qbar l))
    (h₂ : IsRepOf D l ι π s ρ₂)
    (c₁ : Continuous (fun g => ((ρ₁ g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)))) (s₁ : IsSSRep ρ₁)
    (f₁ : ∀ᶠ w in Filter.cofinite, IsSplitPl D.host w → ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om),
      IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
      ((ρ₁ σ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom =
        galPol D.naut (D.naut.lpTw (D.naut.locG π w) s)) : IsRepOf D l ι π s ρ₁ := by
  obtain ⟨c₂, s₂, f₂⟩ := h₂
  have hfin := (Filter.eventually_cofinite.mp f₁).union (Filter.eventually_cofinite.mp f₂)
  have hcp := GlobalTheory.TwistLG.charpoly_eq_of_dense ρ₁ ρ₂ c₁ c₂ _ (hC hfin.toFinset).closure_eq (by
    rintro g ⟨w, hw, hs, B, hB, hg⟩
    rw [Set.Finite.mem_toFinset] at hw
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hw
    apply Polynomial.map_injective ι.toRingHom ι.injective
    rw [hw.1 hs B g hB hg, hw.2 B g hB hg])
  refine ⟨c₁, s₁, f₂.mono fun w hw B σ hB hσ => ?_⟩
  rw [hcp σ]
  exact hw B σ hB hσ
