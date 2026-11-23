module

public import Formalism.GaussJetBounds.StatementP
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.GaussJetBounds.GaussJetProofs.OrbMul
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.LogarithmEquivalence
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementE
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.TrDual
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
open MvPowerSeries
open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog ZV)

namespace GlobalTheory.ExpFacOrbits

theorem expFactor_allOrbits : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (R : Finset (OrbitPlaces.Pl D)) {M N N' : ℕ} (eA : Fin M ≃ R × Fin N)
    (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]) (hbe : constantCoeff be = 0), subst (fun y : ZV (nP D p) M N' =>
        (X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]))
      (mvExp ((-1 : ℂ_[p]) • Formalism.DworkPowerSeriesWeights.bSum (Formalism.DworkPowerSeriesWeights.idM : ZV (nP D p) M N' → ZV (nP D p) M N' → ℂ_[p]) be)) =
      product_zeroth_first_parts.expS ℂ_[p] (OrbitPlaces.beAll D p (N0 := N) (N1 := N') R (fun _ => -1) (fun _ => be)) := by
  intro D p _ R M N N' eA be hbe
  classical
  set a : ZV (nP D p) M N' → MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p] := fun y =>
    X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) with ha_def
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero (fun y => constantCoeff_X _)
  have hlin : ∀ ab : Fin M × Fin N', (fun s : ZMod (nP D p) =>
      Formalism.DworkPowerSeriesWeights.linSub (Formalism.DworkPowerSeriesWeights.idM : ZV (nP D p) M N' → ZV (nP D p) M N' → ℂ_[p]) (s, ab.1, ab.2)) =
      fun s => (X (s, ab.1, ab.2) : MvPowerSeries (ZV (nP D p) M N') ℂ_[p]) := fun ab =>
    funext fun s => Formalism.DworkPowerSeriesWeights.OrbMul.linSub_idM (s, ab.1, ab.2)
  have hX : ∀ ab : Fin M × Fin N', HasSubst (fun s : ZMod (nP D p) =>
      (X (s, ab.1, ab.2) : MvPowerSeries (ZV (nP D p) M N') ℂ_[p])) := fun ab =>
    hasSubst_of_constantCoeff_zero (fun s => constantCoeff_X _)
  have hB : Formalism.DworkPowerSeriesWeights.bSum (Formalism.DworkPowerSeriesWeights.idM : ZV (nP D p) M N' → ZV (nP D p) M N' → ℂ_[p]) be =
      ∑ ab : Fin M × Fin N', subst (fun s : ZMod (nP D p) =>
        (X (s, ab.1, ab.2) : MvPowerSeries (ZV (nP D p) M N') ℂ_[p])) be := by
    unfold Formalism.DworkPowerSeriesWeights.bSum
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [hlin ab]
  have hcc : constantCoeff ((-1 : ℂ_[p]) •
      Formalism.DworkPowerSeriesWeights.bSum (Formalism.DworkPowerSeriesWeights.idM : ZV (nP D p) M N' → ZV (nP D p) M N' → ℂ_[p]) be) = 0 := by

    rw [hB, Finset.smul_sum, map_sum]
    refine Finset.sum_eq_zero fun ab _ => ?_
    rw [MvPowerSeries.constantCoeff_smul, constantCoeff_subst_eq_zero (hX ab) (fun s => constantCoeff_X _) hbe,
      smul_zero]
  rw [Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' ha hcc]
  show mvExp _ = mvExp _
  congr 1

  rw [hB, ← coe_substAlgHom ha, map_smul, map_sum, coe_substAlgHom ha]
  have hterm : ∀ ab : Fin M × Fin N', subst a (subst (fun s : ZMod (nP D p) =>
        (X (s, ab.1, ab.2) : MvPowerSeries (ZV (nP D p) M N') ℂ_[p])) be) =
      subst (fun s : ZMod (nP D p) =>
        (X (OrbitPlaces.orbMap D p (eA ab.1).1 s, (eA ab.1).2, ab.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) be := by
    intro ab
    rw [subst_comp_subst_apply (hX ab) ha]
    congr 1
    funext s
    rw [subst_X ha]
  simp_rw [hterm]
  unfold OrbitPlaces.beAll
  simp only [← Finset.smul_sum]
  congr 1
  rw [Fintype.sum_prod_type]
  rw [Equiv.sum_comp eA (fun x : R × Fin N => ∑ b : Fin N', subst (fun s : ZMod (nP D p) =>
        (X (OrbitPlaces.orbMap D p x.1 s, x.2, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) be)]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_coe_sort R (fun r => ∑ a : Fin N, ∑ b : Fin N', subst (fun s : ZMod (nP D p) =>
        (X (OrbitPlaces.orbMap D p r s, a, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) be)

end GlobalTheory.ExpFacOrbits
