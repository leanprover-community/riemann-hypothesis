module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixUnitsExtendNormalNoetherian
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_matrixUnits_extend_normal_noetherian : ∀ {S B : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S] (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (U₀ : S.Opens) (hU : Dense (U₀ : Set S)) (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (G' : Over U₀.toScheme) [GrpObj G'] (P : Over B) [GrpObj P] [IsCommMonObj P] (f : U₀.toScheme ⟶ B) (φ : G'.left ⟶ G.left) (ψ : G'.left ⟶ P.left) (hφ : IsGrpPullback G' G U₀.ι φ) (hψ : IsGrpPullback G' P f ψ) (E' : Fin 8 → Fin 8 → (P ⟶ P)) (hE' : ∀ a b, IsMonHom (E' a b)) (hrel : ∀ a b c d, E' a b ≫ E' c d = if b = c then E' a d else 1) (hsum : ∏ a, E' a a = 𝟙 P), ∃ E : Fin 8 → Fin 8 → (G ⟶ G), (∀ a b, IsMonHom (E a b)) ∧ (∀ a b c d, E a b ≫ E c d = if b = c then E a d else 1) ∧ ∏ a, E a a = 𝟙 G ∧ ∀ a b, ∃ e : G' ⟶ G', IsMonHom e ∧ e.left ≫ φ = φ ≫ (E a b).left ∧ e.left ≫ ψ = ψ ≫ (E' a b).left := by
  first | exact @GlobalTheory.EighthPowerUnits.exists_matrixUnits_extend | exact GlobalTheory.EighthPowerUnits.exists_matrixUnits_extend | (intros; apply GlobalTheory.EighthPowerUnits.exists_matrixUnits_extend <;> assumption)
