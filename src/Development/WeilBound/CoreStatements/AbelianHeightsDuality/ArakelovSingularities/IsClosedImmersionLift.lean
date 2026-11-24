module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.PolyDef
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ChowProduct
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverOfIsPullback
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.TopologicalKrullDimOfPolyCovered
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ChowSegre
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

namespace GlobalTheory.Amb

variable (k : Type) [CommRing k]

theorem polyCovered_mp [IsDomain k] : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ), PolyCovered (mpStr k m n) (∑ i, n i)
  | 0, n => by
    rw [Fin.sum_univ_one]
    exact _root_.GlobalTheory.Amb.polyCovered_pSpace' (n 0)
  | m + 1, n => by
    have h := polyCovered_pullback (toSpecBase k (n 0)) (mpStr k m (Fin.tail n)) (n 0) (∑ i, Fin.tail n i)
      (_root_.GlobalTheory.Amb.polyCovered_pSpace' (n 0)) (polyCovered_mp m (Fin.tail n))
    rw [Fin.sum_univ_succ]
    exact h

theorem isIntegral_mp [IsDomain k] (m : ℕ) (n : Fin (m + 1) → ℕ) : IsIntegral (MP k m n) :=
  _root_.GlobalTheory.Amb.isIntegral_of_polyCovered' _ _ (polyCovered_mp k m n)

theorem smooth_mp : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ), SmoothOfRelativeDimension (∑ i, n i) (mpStr k m n)
  | 0, n => by
    rw [Fin.sum_univ_one]
    exact (inferInstance : SmoothOfRelativeDimension (n 0) (PSpace.str k (n 0)))
  | m + 1, n => by
    have ih := smooth_mp m (Fin.tail n)
    have h1 : SmoothOfRelativeDimension (∑ i, Fin.tail n i)
        (pullback.fst (toSpecBase k (n 0)) (mpStr k m (Fin.tail n))) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange (n := ∑ i, Fin.tail n i)).of_isPullback
        (IsPullback.of_hasPullback _ _).flip ih
    have h2 : SmoothOfRelativeDimension (n 0) (toSpecBase k (n 0)) :=
      (inferInstance : SmoothOfRelativeDimension (n 0) (PSpace.str k (n 0)))
    have e : ∑ i, n i = (∑ i, Fin.tail n i) + n 0 := by
      rw [Fin.sum_univ_succ, add_comm]; rfl
    rw [e]
    exact smoothOfRelativeDimension_comp (n := ∑ i, Fin.tail n i) (m := n 0) (hf := h1) (hg := h2) _ _

theorem genSmooth_mp (m : ℕ) (n : Fin (m + 1) → ℕ) : GenSmooth (mpStr k m n) (∑ i, n i) := by
  haveI := smooth_mp k m n
  exact genSmooth_of_smooth _ _

theorem isArithVar_mp [IsDomain k] [CharZero k] (hf : Module.Finite ℤ k) (m : ℕ) (n : Fin (m + 1) → ℕ) :
    IsArithVar (mpStr k m n) (∑ i, n i) := by
  haveI : Module.Finite ℤ k := hf
  haveI : IsNoetherian ℤ k := isNoetherian_of_isNoetherianRing_of_finite ℤ k
  haveI : IsNoetherianRing k := isNoetherian_of_tower ℤ inferInstance
  have hdim : ringKrullDim k = 1 := _root_.GlobalTheory.Amb.ringKrullDim_eq_one' hf
  have hbase := (GlobalTheory.ArithBase.isArithVar_id (k := k) hdim).flat
  rw [Category.id_comp] at hbase
  haveI := hbase
  haveI : SmoothOfRelativeDimension (∑ i, n i) (mpStr k m n) := smooth_mp k m n
  haveI : Smooth (mpStr k m n) := SmoothOfRelativeDimension.smooth (∑ i, n i) (mpStr k m n)
  refine ⟨inferInstance, hf, isIntegral_mp k m n, ?_, ?_, ?_⟩
  · rw [← multiProjEmb_toSpecBase]
    exact GlobalTheory.ProjSpace.isProjOver_comp_of_isClosedImmersion _ (GlobalTheory.ProjSpace.isProjOver_pspace_str k _)
  · exact Flat.comp _ _
  · exact _root_.GlobalTheory.Amb.topologicalKrullDim_of_polyCovered' hdim (mpStr k m n) _ (polyCovered_mp k m n)

theorem isClosedImmersion_lift {T : Scheme.{0}} (m : ℕ) (n' : ℕ) (n : Fin (m + 1) → ℕ) (a : T ⟶ PSpace k n')
    [IsClosedImmersion a] (b : T ⟶ MP k m n) (h : a ≫ toSpecBase k n' = b ≫ mpStr k m n) :
    IsClosedImmersion (pullback.lift a b h : T ⟶ pullback (toSpecBase k n') (mpStr k m n)) := by
  haveI : IsProper (mpStr k m n) := isProper_mpStr k m n
  haveI : IsSeparated (mpStr k m n) := inferInstance
  haveI : IsSeparated (pullback.fst (toSpecBase k n') (mpStr k m n)) := inferInstance
  haveI : IsClosedImmersion (pullback.lift a b h ≫ pullback.fst (toSpecBase k n') (mpStr k m n)) := by
    rw [pullback.lift_fst]
    infer_instance
  exact IsClosedImmersion.of_comp (pullback.lift a b h) (pullback.fst (toSpecBase k n') (mpStr k m n))

end GlobalTheory.Amb
