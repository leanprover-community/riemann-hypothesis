module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualMeasuresFinitePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct ENNReal

namespace GlobalTheory.TraceSelfDual

section Form

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [Field R] [Algebra F R]
  (ι : Type) [Fintype ι]

noncomputable def traceBilin : LinearMap.BilinForm R (ι → R ⊗[F] E) :=
  LinearMap.mk₂ R (fun x y => ∑ i, Algebra.trace R (R ⊗[F] E) (x i * y i))
    (fun x x' y => by simp [add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum])
    (fun x y y' => by simp [mul_add, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum])

theorem traceBilin_apply (x y : ι → R ⊗[F] E) :
    traceBilin R ι x y = ∑ i, Algebra.trace R (R ⊗[F] E) (x i * y i) := rfl

theorem traceBilin_symm (x y : ι → R ⊗[F] E) : traceBilin R ι x y = traceBilin R ι y x := by
  simp only [traceBilin_apply, mul_comm]

variable [NumberField F] [NumberField E]

theorem eq_zero_of_traceBilin {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : ι → R ⊗[F] E)
    (hx : ∀ y, traceBilin R ι x y = 0) : x = 0 := by
  classical
  funext j
  refine GlobalTheory.SelfDualFinite.eq_zero_of_trace R h _ fun c => ?_
  have := hx (Pi.single j c)
  rw [traceBilin_apply, Finset.sum_eq_single j] at this
  · rwa [Pi.single_eq_same, mul_comm] at this
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, mul_zero, map_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

end Form

theorem exists_selfDual_trace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)), (∃ r, psiV F ψ v r ≠ 1) → ∀ (ι : Type) [Fintype ι], ∃ μ : Measure (ι → Fv F v ⊗[F] E), SelfDual μ (fun x y => psiV F ψ v (∑ i, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x i * y i))) := by
  intro F E _ _ _ _ _ σ h ψ hψ v hne ι _
  let χ : AddChar (Fv F v) ℂ := ψ.compAddMonoidHom
    ((AddMonoidHom.inr (Ainf F) (Af F)).comp (GlobalTheory.AdelicU.singleFin v).toAddMonoidHom)
  have hc : Continuous χ :=
    hψ.1.comp (Continuous.prodMk continuous_const (GlobalTheory.AdelicU.continuous_singleFin v))
  have hu : ∀ t, ‖χ t‖ = 1 := fun t => hψ.2.1 _
  exact (GlobalTheory.SelfDualFinite.existsUnique_of_bilin v χ hc hu hne _ (traceBilin (Fv F v) ι)
    (traceBilin_symm _ ι) (eq_zero_of_traceBilin _ ι h)).exists

end GlobalTheory.TraceSelfDual
