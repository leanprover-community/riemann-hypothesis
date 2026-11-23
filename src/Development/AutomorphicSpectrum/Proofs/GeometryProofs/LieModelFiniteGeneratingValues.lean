module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Basic.Complex.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbBound

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif


set_option backward.isDefEq.respectTransparency false in
theorem lie_frame_values_basis : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (z₀ : Sp ℂ ⟶ X), IsCptGen ξ → genPt ξ ⤳ centre z₀ → ∃ (N : ℕ) (s : Fin N → Li), (∀ i, ∃ v : epsAt z₀ ⟶ G, M.ValAt z₀ (s i) v) ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel G z₀ V) (b : Fin N → V), (∀ i, M.ValAt z₀ (s i) (Mz.pt (b i))) → LinearIndependent ℂ b ∧ Submodule.span ℂ (Set.range b) = ⊤ := by
  intro X Ω _ ξ G _ _ _ Li _ _ M z₀ hξ h
  obtain ⟨R, _, x, hx, F, _, _, MR, n, b₀, hp⟩ := LieVB.exists_chart G (centre z₀)
  have hq' : (X.fromSpecStalk (centre z₀)) (IsLocalRing.closedPoint (X.presheaf.stalk (centre z₀))) ∈
      x.opensRange := by
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hp
  obtain ⟨ψ, hψ⟩ := LieVB.exists_lift (A := X.presheaf.stalk (centre z₀)) x (X.fromSpecStalk (centre z₀)) hq'
  obtain ⟨EA, _, _, ⟨MA⟩⟩ := lieModel_exists X G (X.presheaf.stalk (centre z₀)) (X.fromSpecStalk (centre z₀))
  obtain ⟨-, BA, -, -⟩ := LieVB.basis_tr (A := X.presheaf.stalk (centre z₀)) ψ x (X.fromSpecStalk (centre z₀))
    hψ MR MA b₀
  obtain ⟨i, hi⟩ := LieVB.exists_tr (A := X.presheaf.stalk (centre z₀)) (X.fromSpecStalk (centre z₀)) ξ
    (genMap ξ ⟨centre z₀, h⟩) (LieTangent.spec_genMap ξ ⟨centre z₀, h⟩) MA M
  have hext : ∀ a, M.Extends ⟨centre z₀, h⟩ (i a) (MA.pt a) := fun a => ⟨MA.tan a, hi a⟩
  refine ⟨n, fun k => i (BA k), fun k => ?_, fun V _ _ Mz b hb => ?_⟩
  · obtain ⟨E₀, _, _, ⟨M₀⟩⟩ := lieModel_exists X G ℂ z₀
    obtain ⟨j, hj⟩ := LieVB.exists_tr (A := X.presheaf.stalk (centre z₀)) (X.fromSpecStalk (centre z₀)) z₀
      (Scheme.stalkClosedPointTo z₀).hom (LieTangent.spec_centre z₀) MA M₀
    exact ⟨M₀.pt (j (BA k)), h, _, hext _, hj _⟩
  · obtain ⟨β, B, hB, hβ⟩ := LieVB.basis_tr (R := X.presheaf.stalk (centre z₀))
      (Scheme.stalkClosedPointTo z₀).hom (X.fromSpecStalk (centre z₀)) z₀ (LieTangent.spec_centre z₀) MA Mz BA
    have hbB : b = B := by
      funext k
      obtain ⟨_, v, hv, hw⟩ := hb k
      have hva : MA.pt (BA k) = v := (hext (BA k)).unique (hξ.inj _) hv
      subst hva
      rw [hB]
      exact LieVB.pt_left_inj Mz (hw.trans (hβ _).symm)
    rw [hbB]
    exact ⟨B.linearIndependent, B.span_eq⟩

end GlobalTheory.CompanionTheory.Ar.QuotUnif
