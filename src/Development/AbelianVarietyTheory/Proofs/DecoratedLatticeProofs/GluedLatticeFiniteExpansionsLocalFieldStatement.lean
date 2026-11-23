module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedLatticeFiniteExpansionsLocalField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.FinPl GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData ValuativeRel IsLocalRing Matrix

theorem _root_.GlobalTheory.T.gluedLattice_finite_expansions_localField : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (χ : AddChar 𝓀[k] ℂ), χ ≠ 1 → ∀ (Λ : Submodule 𝒪[k] (n → k)) [Λ.IsFullLattice k], (∀ P : Pair k n', latInd (gluedS q 1 P.ker P.vec) Λ = ((resCard k : ℂ) ^ Fintype.card n)⁻¹ • (tensCol (latInd P.ker Λ) (vecInd Λ) + ∑ Q ∈ withLat Λ, tensCol (latInd P.ker Q.ker + mainDatum q χ 1 P Q) (charInd χ Q)) ∧ latInd P.ker Λ + ∑ Q ∈ withLat Λ, (latInd P.ker Q.ker + mainDatum q χ 1 P Q) = ((resCard k : ℂ) ^ Fintype.card n) • latInd P.lat Λ) ∧ (∀ R : Pair k n', latInd Λ (gluedS q 1 R.ker R.vec) = tensRow (latInd Λ R.ker) (dualInd Λ) + ∑ Q ∈ withLat Λ, tensRow (phiOne Q R) (cosetInd q Q.lat Q.red)) ∧ ∀ (L : Submodule 𝒪[k] (n' → k)) [L.IsFullLattice k], latInd Λ (lastKer L) = tensRow (latInd Λ L) (dualInd Λ) ∧ latInd Λ (lastPair q L).lat = tensRow (latInd Λ L) (dualInd Λ + ∑ Q ∈ withLat Λ, cosetInd q Q.lat Q.red) := by
  intro k _ _ _ _ n n' _ _ _ _ q χ hχ Λ _
  refine ⟨fun P => ⟨GlobalTheory.GluedExp.glued_col q χ hχ Λ P,
    GlobalTheory.GluedExp.glued_sum q χ hχ Λ P⟩, GlobalTheory.GluedExp.glued_row q Λ, ?_⟩
  intro L _
  have hlast : latInd Λ (lastPair q L).lat =
      tensRow (latInd Λ L) (dualInd Λ + ∑ Q ∈ withLat Λ, cosetInd q Q.lat Q.red) := by
    classical
    funext x
    rw [tensRow, GlobalTheory.GluedExp.coset_total, latInd, latInd, ite_zero_mul_ite_zero, mul_one]
    have hm (v : n' ⊕ Fin 1 → k) :
        v ∈ (lastPair q L).lat ↔ v ∘ Sum.inl ∈ L ∧ q.1 • v (Sum.inr 0) ∈ 𝒪[k] := by
      rw [Pair.mem_lat_iff]
      simp only [GlobalTheory.LastSteps.lastPair_hasVal]
      constructor
      · rintro ⟨a, h, s, hs, -⟩
        exact ⟨h, hs ▸ s.2⟩
      · rintro ⟨h, hs⟩
        exact ⟨_, h, ⟨_, hs⟩, rfl, rfl⟩
    refine if_congr ⟨fun h => ⟨fun y hy => ((hm _).1 (h y hy)).1, fun y hy => ?_⟩,
      fun h y hy => (hm _).2 ⟨h.1 y hy, ?_⟩⟩ rfl rfl
    · rw [smul_dotProduct]
      exact ((hm _).1 (h y hy)).2
    · have hη := h.2 y hy
      rw [smul_dotProduct] at hη
      exact hη
  exact ⟨GlobalTheory.GluedExp.last_ker Λ L, hlast⟩
