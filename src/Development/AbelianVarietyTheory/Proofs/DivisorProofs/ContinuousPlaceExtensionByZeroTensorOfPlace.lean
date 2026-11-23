module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.SaGen.ExtZero

open GlobalTheory.CompanionTheory.SaGen

variable {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [Field K] [Algebra F K]
  [TopologicalSpace K]

theorem iB_tmul (P : PlaceMap F K) (x : K) (e : E) :
    iB (E := E) P (x ⊗ₜ[F] e) = P.inj x ⊗ₜ[F] e := rfl

theorem iB_eq_sum [FiniteDimensional F E] (P : PlaceMap F K) (y : K ⊗[F] E) :
    iB (E := E) P y = ∑ k, P.inj ((Algebra.TensorProduct.basis K (Module.finBasis F E)).repr y k) •
      ((1 : AF F) ⊗ₜ[F] (Module.finBasis F E) k) := by
  set B := Algebra.TensorProduct.basis K (Module.finBasis F E)
  conv_lhs => rw [← B.sum_repr y]

  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [B, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, iB_tmul]

theorem continuous_iB [FiniteDimensional F E] [IsTopologicalRing K] (P : PlaceMap F K) :
    Continuous (iB (E := E) P) := by
  haveI : IsModuleTopology K (K ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) (AF F ⊗[F] E)
  haveI : ContinuousSMul (AF F) (AF F ⊗[F] E) := IsModuleTopology.toContinuousSMul (AF F) (AF F ⊗[F] E)
  have hc : ∀ k, Continuous fun y : K ⊗[F] E =>
      (Algebra.TensorProduct.basis K (Module.finBasis F E)).repr y k := fun k =>
    IsModuleTopology.continuous_of_linearMap ((Algebra.TensorProduct.basis K (Module.finBasis F E)).coord k)
  have h : (iB (E := E) P : K ⊗[F] E → AF F ⊗[F] E) = fun y => ∑ k,
      P.inj ((Algebra.TensorProduct.basis K (Module.finBasis F E)).repr y k) •
        ((1 : AF F) ⊗ₜ[F] (Module.finBasis F E) k) := funext (iB_eq_sum P)
  rw [h]
  exact continuous_finsetSum _ fun k _ =>
    Continuous.smul (f := fun y => P.inj ((Algebra.TensorProduct.basis K (Module.finBasis F E)).repr y k))
      (g := fun _ => (1 : AF F) ⊗ₜ[F] (Module.finBasis F E) k) (P.cont_inj.comp (hc k)) continuous_const

end GlobalTheory.CompanionTheory.SaGen.ExtZero

theorem GlobalTheory.CompanionTheory.SaGen.ExtZero.continuous_iB_place : ∀ {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E] [Field K] [Algebra F K] [TopologicalSpace K] [IsTopologicalRing K] (P : GlobalTheory.CompanionTheory.SaGen.PlaceMap F K), Continuous (GlobalTheory.CompanionTheory.SaGen.iB (E := E) P) :=
  fun P => GlobalTheory.CompanionTheory.SaGen.ExtZero.continuous_iB P
