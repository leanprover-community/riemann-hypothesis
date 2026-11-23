module

public import Development.WeilBound.CoreStatements.PeriodRingComparison.PrimitiveEpsilon.UntiltEpsilonEqOne
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.EqZeroOfPMulEqZero
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Period
public import Development.WeilBound.CoreStatements.PeriodRingComparison.TeichmullerLogarithm.LogEps
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.MapEqPadicPowCyclotomicCharacter

@[expose] public section

noncomputable section

open GroundTheory.PAdicHodge

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

theorem cA_symm_tA : (cA l).symm (Formalism.Per6.tA l) = Reformulated.AutPerF.Acris.logTeich (eps0 l) := by
  rw [← acris_log_teichmuller_epsilon, RingEquiv.symm_apply_apply]

theorem isUnit_bcris_l : IsUnit ((l : ℕ) : Formalism.Per6.Bcris l) := by
  simpa using PositivityTheory.LocInh.isUnit_cB_l l

def bcrisPlusHom : Reformulated.AutPerF.BcrisPlus l (OC l) →+* Formalism.Per6.Bcris l :=
  Reformulated.AutPerF.BcrisPlus.lift ((Formalism.Per6.cB l).comp (cA l).toRingHom) (isUnit_bcris_l l)

theorem bcrisPlusHom_algebraMap (x : Reformulated.AutPerF.Acris l (OC l)) :
    bcrisPlusHom l (algebraMap _ _ x) = Formalism.Per6.cB l (cA l x) :=
  Reformulated.AutPerF.BcrisPlus.lift_algebraMap _ _ x

theorem isUnit_cB_cA_logTeich {ε : Reformulated.AutPerF.tateModule l (OC l)} (hε : Reformulated.AutPerF.IsPrimitive ε) :
    IsUnit (Formalism.Per6.cB l (cA l (Reformulated.AutPerF.Acris.logTeich ε))) := by
  obtain ⟨a, rfl⟩ := (epsilon_isPrimitive l).exists_unit hε
  rw [Reformulated.AutPerF.Acris.logTeich_padicPow, ← cA_symm_tA, map_mul, RingEquiv.apply_symm_apply,
    map_mul]
  exact (((a.isUnit.map (algebraMap ℤ_[l] (Reformulated.AutPerF.Acris l (OC l)))).map (cA l)).map
    (Formalism.Per6.cB l)).mul (Formalism.Per6.Loc2.isUnit_right _ _)

def bcrisHom : Reformulated.AutPerF.Bcris l (OC l) →+* Formalism.Per6.Bcris l :=
  Reformulated.AutPerF.Bcris.lift (bcrisPlusHom l) (fun ε hε => by
    rw [bcrisPlusHom_algebraMap]
    exact isUnit_cB_cA_logTeich l hε)

theorem bcrisHom_algebraMap (x : Reformulated.AutPerF.Acris l (OC l)) :
    bcrisHom l (algebraMap _ _ x) = Formalism.Per6.cB l (cA l x) :=
  (Reformulated.AutPerF.Bcris.lift_algebraMap _ _ _).trans (bcrisPlusHom_algebraMap l x)

def bcrisInv : Formalism.Per6.Bcris l →+* Reformulated.AutPerF.Bcris l (OC l) :=
  Formalism.Per6.Loc2.lift
    ((algebraMap (Reformulated.AutPerF.Acris l (OC l)) (Reformulated.AutPerF.Bcris l (OC l))).comp (cA l).symm.toRingHom)
    (by
      rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, map_natCast,
        map_natCast]
      exact Reformulated.AutPerF.Bcris.isUnit_p (p := l) (R := OC l))
    (by
      rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, cA_symm_tA]
      exact Reformulated.AutPerF.Bcris.isUnit_logTeich (epsilon_isPrimitive l))

private theorem loc2_lift_comp_mk₀ {A E : Type} [CommRing A] [CommRing E] {a t : A}
    (f : A →+* E) (ha : IsUnit (f a)) (ht : IsUnit (f t)) :
    (Formalism.Per6.Loc2.lift f ha ht).comp (Formalism.Per6.Loc2.mk₀ a t) = f :=
  RingHom.ext (Formalism.Per6.Loc2.lift_mk₀ f ha ht)

theorem bcrisInv_cB (x : ACris.ACris ℂ_[l] l) :
    bcrisInv l (Formalism.Per6.cB l x) = algebraMap _ (Reformulated.AutPerF.Bcris l (OC l)) ((cA l).symm x) := by
  -- Comparing the ring homomorphisms avoids unfolding the localization's function coercions.
  have h : (bcrisInv l).comp (Formalism.Per6.cB l) =
      (algebraMap (Reformulated.AutPerF.Acris l (OC l)) (Reformulated.AutPerF.Bcris l (OC l))).comp
        (cA l).symm.toRingHom :=
    loc2_lift_comp_mk₀ _ _ _
  simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] using
    RingHom.congr_fun h x

theorem bcrisInv_bcrisHom (x : Reformulated.AutPerF.Bcris l (OC l)) : bcrisInv l (bcrisHom l x) = x := by
  have h : (bcrisInv l).comp (bcrisHom l) = RingHom.id _ := by
    refine Reformulated.AutPerF.Bcris.hom_ext fun y => ?_
    have h2 : ((bcrisInv l).comp (bcrisHom l)).comp
        (algebraMap (Reformulated.AutPerF.BcrisPlus l (OC l)) (Reformulated.AutPerF.Bcris l (OC l))) =
        (RingHom.id _).comp (algebraMap _ _) := by
      refine Reformulated.AutPerF.BcrisPlus.hom_ext fun z => ?_
      simp only [RingHom.comp_apply, RingHom.id_apply]
      change bcrisInv l (bcrisHom l (algebraMap (Reformulated.AutPerF.Acris l (OC l)) _ z)) =
        algebraMap (Reformulated.AutPerF.Acris l (OC l)) _ z
      rw [bcrisHom_algebraMap, bcrisInv_cB, RingEquiv.symm_apply_apply]
    exact RingHom.congr_fun h2 y
  exact RingHom.congr_fun h x

theorem bcrisHom_bcrisInv (x : Formalism.Per6.Bcris l) : bcrisHom l (bcrisInv l x) = x := by
  have h : (bcrisHom l).comp (bcrisInv l) = RingHom.id _ := by
    refine Formalism.Per6.Loc2.hom_ext fun y => ?_
    change bcrisHom l (bcrisInv l (Formalism.Per6.cB l y)) = Formalism.Per6.cB l y
    rw [bcrisInv_cB, bcrisHom_algebraMap, RingEquiv.apply_symm_apply]
  exact RingHom.congr_fun h x

def cBc : Reformulated.AutPerF.Bcris l (OC l) ≃+* Formalism.Per6.Bcris l :=
  RingEquiv.ofRingHom (bcrisHom l) (bcrisInv l) (RingHom.ext (bcrisHom_bcrisInv l))
    (RingHom.ext (bcrisInv_bcrisHom l))

theorem cBc_algebraMap (x : Reformulated.AutPerF.Acris l (OC l)) :
    cBc l (algebraMap _ _ x) = Formalism.Per6.cB l (cA l x) :=
  bcrisHom_algebraMap l x

theorem cBc_symm_cB (x : ACris.ACris ℂ_[l] l) :
    (cBc l).symm (Formalism.Per6.cB l x) = algebraMap _ (Reformulated.AutPerF.Bcris l (OC l)) ((cA l).symm x) :=
  bcrisInv_cB l x

end Cmp6
