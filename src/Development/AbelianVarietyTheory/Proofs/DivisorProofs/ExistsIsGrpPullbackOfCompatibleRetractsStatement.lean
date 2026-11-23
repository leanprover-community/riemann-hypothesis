module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsGrpPullbackOfCompatibleRetracts
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_isGrpPullback_of_compatible_retracts : ∀ {S S' B : Scheme.{0}} (j : S' ⟶ S) (f : S' ⟶ B) (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G'] (P : Over B) [GrpObj P] (φ : G'.left ⟶ G.left) (ψ : G'.left ⟶ P.left) (hφ : IsGrpPullback G' G j φ) (hψ : IsGrpPullback G' P f ψ) (e : G ⟶ G) (e₀ : P ⟶ P) (e' : G' ⟶ G') (he' : IsMonHom e') (h₁ : e'.left ≫ φ = φ ≫ e.left) (h₂ : e'.left ≫ ψ = ψ ≫ e₀.left) (H : Over S) [GrpObj H] (i : H ⟶ G) (r : G ⟶ H) (hi : IsMonHom i) (hr : IsMonHom r) (hir : i ≫ r = 𝟙 H) (hri : r ≫ i = e) (C : Over B) [GrpObj C] (k : C ⟶ P) (p : P ⟶ C) (hk : IsMonHom k) (hp : IsMonHom p) (hkp : k ≫ p = 𝟙 C) (hpk : p ≫ k = e₀), ∃ (C' : Over S') (_ : GrpObj C') (a : C'.left ⟶ H.left) (b : C'.left ⟶ C.left), IsGrpPullback C' H j a ∧ IsGrpPullback C' C f b := by
  first | exact @GlobalTheory.RetractPullback.exists_isGrpPullback_of_retracts | exact GlobalTheory.RetractPullback.exists_isGrpPullback_of_retracts | (intros; apply GlobalTheory.RetractPullback.exists_isGrpPullback_of_retracts <;> assumption)
