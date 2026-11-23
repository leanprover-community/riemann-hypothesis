module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Order.CompletePartialOrder
public import Development.WeilBound.CoreStatements.HodgeTatePoints.CiEigVal
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.EigVal

theorem values_eigen_sheaves : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (k K : Type) [Field k] [Field K] [Algebra k K] (z : Spec (CommRingCat.of K) ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (Vz : Type) [AddCommGroup Vz] [Module K Vz] (Mz : LieModel G z Vz) (h₀ : genPt ξ ⤳ centre z) (O S : Type) [CommRing O] [Fintype S] (act : O → (G ⟶ G)) (r : O →+* Module.End Ω V) (rz : O →+* Module.End K Vz) (σ : S → (O →+* Ω)) (χ : S → (O →+* k)), IsCptGen ξ → Smooth G.hom → (∀ a, IsMonHom (act a)) → M.IsActOf act r → Mz.IsActOf act rz → IsSplit χ → (∀ s a, ValAt ξ z (σ s a) (algebraMap k K (χ s a))) → M.lat ⟨centre z, h₀⟩ = ⨆ s, M.eigLat r (σ s) ⟨centre z, h₀⟩ → ∀ s, Submodule.span K {v | ∃ e ∈ M.eigLat r (σ s) ⟨centre z, h₀⟩, M.ValAt z e (Mz.pt v)} = eigSp rz ((algebraMap k K).comp (χ s)) :=
  @PositivityTheory.HtPt.Ci.eig_val

end GlobalTheory.CompanionTheory.Ar.EigVal
