module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SplitExtDVR

theorem exists_complete_dvr_split_ext : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (G : Over (Sp V)) [GrpObj G], IsSemiAbelian G →
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : CharZero W) (g : V →+* W),
      IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ g.IsIntegral ∧ Function.Injective g ∧ IsLocalHom g ∧
      ∃ E : SplitExt (Sp (IsLocalRing.ResidueField W)),
        E.IsGt ((Over.pullback (spMap (IsLocalRing.residue W))).obj ((Over.pullback (spMap g)).obj G)) := by
  intro V _ _ _ _ hcV G _ hG
  haveI := hcV
  let F := AlgebraicClosure (FractionRing V)
  have : Algebra.IsAlgebraic V F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := V) (K := FractionRing V) (C := F)).2 inferInstance
  have hi : Function.Injective (algebraMap V F) := by
    rw [IsScalarTower.algebraMap_eq V (FractionRing V) F]
    exact (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective _ _)
  have : FaithfulSMul V F := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  obtain ⟨W, hd, hc, hfin, hs⟩ := GlobalTheory.Ex.UnifModel.exists_split V F G hG
  have hW : Function.Injective (algebraMap V W) := fun _ _ h => hi (congrArg (fun z : W => (z : F)) h)
  have : CharZero W := charZero_of_injective_algebraMap hW
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective _ _).2 hW
  have hl : IsLocalHom (algebraMap V W) := inferInstance
  have hint : (algebraMap V W).IsIntegral := by
    have : Algebra.IsIntegral V W := Algebra.IsIntegral.of_finite V W
    exact Algebra.IsIntegral.isIntegral
  exact ⟨W, inferInstance, inferInstance, hd, inferInstance, algebraMap V W, hc, hint, hW, hl, hs⟩

end GlobalTheory.SplitExtDVR
