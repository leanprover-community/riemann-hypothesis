module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatMulVec

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
namespace GlobalTheory.AdeleCocompactExt

theorem exists_compact_adeleE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    ∃ K : Set (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), IsCompact K ∧ ∀ a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), ∃ e : E, a - inclR (F := F) (AF F) e ∈ K := by
  intro F E _ _ _ _ _
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨K₀, hK₀, hK⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  haveI : IsModuleTopology (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := ⟨rfl⟩
  haveI : IsTopologicalRing (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := IsModuleTopology.isTopologicalRing (AF F) _
  let b := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (AF F) b
  have hφ : Continuous B.equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap B.equivFun.symm.toLinearMap
  refine ⟨B.equivFun.symm '' Set.pi Set.univ (fun _ => K₀),
    (isCompact_univ_pi fun _ => hK₀).image hφ, ?_⟩
  intro a
  choose x hx using fun k => hK (B.equivFun a k)
  refine ⟨∑ k, x k • b k, fun k => B.equivFun a k - algebraMap F (AF F) (x k), fun k _ => hx k, ?_⟩
  rw [LinearEquiv.symm_apply_eq]
  funext k
  have h1 : B.equivFun (inclR (F := F) (AF F) (∑ k, x k • b k)) k = algebraMap F (AF F) (x k) := by
    rw [Module.Basis.equivFun_apply]
    show (B.repr ((1 : AF F) ⊗ₜ[F] (∑ k, x k • b k))) k = _
    rw [Algebra.TensorProduct.basis_repr_tmul]
    simp [b, Module.Basis.repr_sum_self]
    rw [Finset.sum_eq_single k (fun j _ hj => by simp [Finsupp.single_apply, hj]) (by simp)]
    simp
  simp only [map_sub, Pi.sub_apply, h1]

end GlobalTheory.AdeleCocompactExt
