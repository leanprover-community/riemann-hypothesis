module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalTangentHarrisTaylorRepresentingFaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFormallySmoothSquareZeroLiftStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackCompStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfArtinianSquareZeroLiftingNoetherianBaseStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfUniversalFirstOrderTaStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

theorem RepFam.smoothOfRelativeDimension : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ F : RepFam b N, IsQProjOver F.s → SmoothOfRelativeDimension (D.a * (D.n - 1)) F.s := by
  intro p _ D R _ _ b N hN hNp F hq
  have hlft : LocallyOfFiniteType F.s := by
    obtain ⟨M, i, hi, hqc, hi'⟩ := hq
    have := isProper_str R M
    rw [← hi']
    infer_instance
  have hsm : Smooth F.s := by
    refine GlobalTheory.T.smooth_of_artinian_squareZero_lifting_noetherian_base R F.X F.s hlft ?_
    intro C C₀ _ _ _ _ π hπ hker t x₀ hx
    obtain ⟨β, rfl⟩ : ∃ β : R →+* C, t = spMap β :=
      ⟨(Spec.preimage t).hom, by simp [spMap]⟩
    have hcomp : spMap π ≫ spMap β = spMap (π.comp β) := by
      simp [spMap, ← Spec.map_comp]
    have hs₀ : x₀ ≫ F.s = spMap (π.comp β) := by rw [hx, hcomp]
    obtain ⟨o₀, ⟨m₀⟩⟩ := GlobalTheory.T.exists_harrisTaylorObjectPullback p D R b N _ _ F.s _ F.univ x₀ hs₀
    obtain ⟨o', ⟨m'⟩⟩ := GlobalTheory.T.harrisTaylor_formally_smooth_squareZero_lift p D R b N hN hNp C C₀ π β hπ (by rw [← hker, pow_two]) o₀
    obtain ⟨x, ⟨hxs, ⟨mx⟩⟩, -⟩ := F.rep (Sp C) (spMap β) o'
    obtain ⟨mc⟩ := GlobalTheory.T.harrisTaylorObjectPullback_comp p D R b N _ _ _ _ _ _ o₀ o' F.univ (spMap π) x m' mx
    refine ⟨x, ?_, hxs⟩
    exact (F.rep (Sp C₀) (spMap (π.comp β)) o₀).unique
      ⟨by rw [Category.assoc, hxs, hcomp], ⟨mc⟩⟩ ⟨hs₀, ⟨m₀⟩⟩
  exact GlobalTheory.T.smoothOfRelativeDimension_of_universal_firstOrder_tangent R F.X F.s _ hsm (GlobalTheory.T.exists_universal_tangent_harrisTaylor_representingFamily p D R b N hN hNp F hq hsm)

end GlobalTheory.UPel.HT
