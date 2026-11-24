module

public import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.GammaEqDpow
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRham
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRhamMap
public import GroundTheory.PAdicHodge.ThetaBDeRhamPlusFieldCycloUnitBdRZpow
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GroundTheory.PAdicHodge

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

def cPd : Reformulated.AutPerF.BdRPlus l (OC l) ≃+* Formalism.Per6.BdRp l := Reformulated.AutPerF.BdRPlus.mapEquiv l (e l)

def cD : Reformulated.AutPerF.BdR l (OC l) ≃+* Formalism.Per6.BdR l :=
  IsFractionRing.ringEquivOfRingEquiv (cPd l)

theorem cD_algebraMap (y : Reformulated.AutPerF.BdRPlus l (OC l)) :
    cD l (algebraMap _ _ y) = algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (cPd l y) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ y

theorem ker_theta_eq_span_symm_tBdR :
    RingHom.ker (Reformulated.AutPerF.BdRPlus.theta l (OC l)) = Ideal.span {(cPd l).symm (tBdR l)} :=
  (Reformulated.AutPerF.BdRPlus.irreducible_iff _).1
    ((MulEquiv.irreducible_iff (f := (cPd l).symm)).2 irreducible_tBdR)

theorem fil_transport {A B K L : Type} [CommRing A] [CommRing B] [Field K] [Field L] [Algebra A K]
    [Algebra B L] (f : A ≃+* B) (F : K ≃+* L) (h : ∀ y, F (algebraMap A K y) = algebraMap B L (f y))
    (t : B) (a : ℤ) (x : K) :
    x ∈ Submodule.span A {algebraMap A K (f.symm t) ^ a} ↔
      F x ∈ Submodule.span B {algebraMap B L t ^ a} := by
  have ht : F (algebraMap A K (f.symm t) ^ a) = algebraMap B L t ^ a := by
    rw [map_zpow₀, h, RingEquiv.apply_symm_apply]
  rw [Submodule.mem_span_singleton, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨f c, by rw [Algebra.smul_def, Algebra.smul_def, map_mul, h, ht]⟩
  · rintro ⟨c, hc⟩
    refine ⟨f.symm c, F.injective ?_⟩
    rw [← hc, Algebra.smul_def, Algebra.smul_def, map_mul, h, ht, RingEquiv.apply_symm_apply]

theorem cD_fil (a : ℤ) (x : Reformulated.AutPerF.BdR l (OC l)) :
    x ∈ Reformulated.AutPerF.BdR.fil l (OC l) a ↔ cD l x ∈ Formalism.Per6.FilD l a := by
  have h1 : Formalism.Per6.FilD l a = Submodule.span (Formalism.Per6.BdRp l)
      {(algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (tBdR l)) ^ a} := fil_eq_span_tBdR a
  rw [h1, Reformulated.AutPerF.BdR.fil_eq_span (ker_theta_eq_span_symm_tBdR l)]
  exact fil_transport (cPd l) (cD l) (cD_algebraMap l) (tBdR l) a x

end Cmp6
