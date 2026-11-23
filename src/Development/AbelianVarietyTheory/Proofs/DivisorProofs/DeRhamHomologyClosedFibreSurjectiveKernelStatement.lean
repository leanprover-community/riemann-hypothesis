module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcObjIsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamHomologyClosedFibreSurjectiveKernel
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
attribute [local instance] Functor.grpObjObj

theorem _root_.GlobalTheory.T.deRhamHomology_closedFibre_surjective_kernel : ∀ (C₀ : Type) [CommRing C₀] [IsLocalRing C₀] (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ (O : Type) [CommRing O] (a : OAct O A₀), ∃ f : HdR A₀ →ₛₗ[algebraMap C₀ (IsLocalRing.ResidueField C₀)] HdR ((Over.pullback (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀)))).obj A₀), Function.Surjective f ∧ (∀ h, f h = 0 → h ∈ IsLocalRing.maximalIdeal C₀ • (⊤ : Submodule C₀ (HdR A₀))) ∧ ∀ (x : O) (h : HdR A₀), f (act (dp0 C₀) (𝟙 _) a x h) = act (dp0 (IsLocalRing.ResidueField C₀)) (𝟙 _) (OAct.pullback (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀))) A₀ a) x (f h) := by
  first | (exact @GlobalTheory.HdRFibre.fibre_baseChange) | (exact GlobalTheory.HdRFibre.fibre_baseChange) | (intros; apply GlobalTheory.HdRFibre.fibre_baseChange  <;> assumption)
