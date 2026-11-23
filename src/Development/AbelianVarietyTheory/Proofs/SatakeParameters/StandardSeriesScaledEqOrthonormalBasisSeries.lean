module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsConstantCoeffOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
public import Formalism.LocalToGlobal.InertKernelTheory.DefsRepFrame
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingHomRhoK

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

noncomputable section

namespace GlobalTheory.KerStd.HypCoord

theorem mvPowerSeries_subst_linearForm {σ τ : Type} [Fintype σ] {K : Type} [Field K] {a : σ → MvPowerSeries τ K}
    (ha : MvPowerSeries.HasSubst a) (α : σ → K) :
    MvPowerSeries.subst a (∑ j, MvPowerSeries.C (α j) * MvPowerSeries.X j : MvPowerSeries σ K) =
      ∑ j, MvPowerSeries.C (α j) * a j := by

  rw [← MvPowerSeries.coe_substAlgHom ha, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MvPowerSeries.coe_substAlgHom ha, MvPowerSeries.subst_mul ha, MvPowerSeries.subst_X ha, MvPowerSeries.subst_C]

theorem stdSer_scaled_eq_thOrth : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' r : ℕ) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hz : Fin r → MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]), (∀ i, MvPowerSeries.constantCoeff (hz i) = 0) → (∀ k, ∑ i, MvPowerSeries.C (Formalism.L2.KerInert.RepFrame.lamB D lam b k i) * hz i = ∑ j : OrbitPlaces.Pl D × Fin N × Fin N', MvPowerSeries.C (chgB D lam P P' k ((0 : ZMod 1), (tauPl D j.1, j.2))) * MvPowerSeries.X j) → ∀ (c : ℂ_[p]) (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C c * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) (stdSer D lam (fun _ => 1) P P' G) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) = MvPowerSeries.subst hz (thOrth D lam c b G) := by
  intro D p _ lam N N' r P P' b hz hz0 hlin c G
  have hs1 : MvPowerSeries.HasSubst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' =>
      (MvPowerSeries.C c * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun v => by simp
  have hs2 : MvPowerSeries.HasSubst hz := MvPowerSeries.hasSubst_of_constantCoeff_zero hz0
  have e : ∀ x : ℂ_[p], algebraMap ℂ_[p] (MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) x = MvPowerSeries.C x := fun x => rfl
  rw [stdSer, atLin, thOrth, MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp) hs1,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp) hs2]
  congr 1
  funext k
  simp only [e, one_mul]
  rw [mvPowerSeries_subst_linearForm hs1, mvPowerSeries_subst_linearForm hs2]
  have h1 : (∑ i, MvPowerSeries.C (c * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) * hz i :
      MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) =
      MvPowerSeries.C c * ∑ i, MvPowerSeries.C (Formalism.L2.KerInert.RepFrame.lamB D lam b k i) * hz i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, mul_assoc]
    rfl
  rw [h1, hlin k, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end GlobalTheory.KerStd.HypCoord
