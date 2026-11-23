module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizationBaseChangeCompleteDvr
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.uniformization_base_change_complete_dvr : ∀ (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsLocalRing R₀], AdmBase R₀ (maximalIdeal R₀) → ∀ (D₀ : DegData R₀ (maximalIdeal R₀)) (A₀ : PolAV (Sp (FractionRing R₀))) (G₀ : Over (Sp R₀)) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ (U₀ : Unif (maximalIdeal R₀) D₀ A₀ G₀) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R₀ →+* W), Function.Injective φ → IsLocalHom φ → ∀ (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (β : GW.left ⟶ G₀.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), IsGrpPullback GW G₀ (spMap φ) β → LBIso UW.LG.L (U₀.LG.L.pull β) → Nonempty (IsPullDeg φ D₀.toPre DW.toPre) := by
  first | exact @GlobalTheory.Mum.isPullDeg_of_trait_unif | exact GlobalTheory.Mum.isPullDeg_of_trait_unif | (intros; apply GlobalTheory.Mum.isPullDeg_of_trait_unif <;> assumption)
