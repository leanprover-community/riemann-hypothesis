module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsLatInd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunSplitPlaceSchroedingerModel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunOPlaceModelApply
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.PlaceSumTheta



theorem isThetaFunO_sum_placeModel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : Lat S) (M' : Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (L : Fin n → LocPl ψ S T M M'), (Function.Injective fun i => (L i).q.v) → ∀ (f₀ : WO S T → ℂ) (T' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), Vac ψ S T M M' (fun _ => True) f₀ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) (∑ i, (L i).q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 f₀ T' → ∀ Φ, IsSBHalf (∑ i, (L i).q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) Φ → IsThetaFunO ψ S T (T' Φ) := by
  intro D ψ hψ S T M M' hM hM' n L inj f₀ T' hvac hT' Φ hΦ
  have hidem : (∑ i, (L i).q.e) * (∑ i, (L i).q.e) = ∑ i, (L i).q.e := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_eq_single i
      (fun j _ h => GlobalTheory.SeeSaw.LocPlModel.e_mul_e _ _ (fun h' => h (inj h').symm)) (fun h => (h (Finset.mem_univ _)).elim)]
    exact (L i).q.split.1
  have hinf : infPart D (∑ i, (L i).q.e) = 0 := by

    rw [map_sum]
    exact Finset.sum_eq_zero fun i _ => GlobalTheory.LocMod.LinTheta.infPart_of_isSplitIdem (L i).q.split
  exact GlobalTheory.PlaceThetaVal.isThetaFunO_placeModel_apply hψ S T M M' hM hM' _ f₀ Φ T' hidem hinf hT' hvac.1 hΦ

end GlobalTheory.PlaceSumTheta
