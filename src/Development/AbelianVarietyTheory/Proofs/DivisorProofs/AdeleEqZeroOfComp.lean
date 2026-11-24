module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit

namespace GlobalTheory.SWOpFin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adele_eq_zero_of_comp {c : AF F} (hf : ∀ v, evFin F v c = 0) (hi : ∀ w, evInf F w c = 0) : c = 0 := by
  refine Prod.ext (funext fun w => hi w) ?_
  exact Subtype.ext (funext fun v => hf v)

theorem tens_eq_zero_of_comp {z : AF F ⊗[F] E} (hf : ∀ v, compFin F E v z = 0) (hi : ∀ w, compInf F E w z = 0) :
    z = 0 := by
  let b := Module.Free.chooseBasis F E
  let B := Algebra.TensorProduct.basis (AF F) b
  have key : ∀ {A : Type} [CommRing A] [Algebra F A] (f : AF F →ₐ[F] A),
      (Algebra.TensorProduct.map f (AlgHom.id F E)) z = 0 → ∀ i, f (B.repr z i) = 0 := by
    intro A _ _ f hz i
    have hs : z = ∑ j, B.repr z j • B j := (B.sum_repr z).symm
    have hz' : ∑ j, f (B.repr z j) • (Algebra.TensorProduct.basis A b) j = 0 := by
      rw [hs] at hz

      simpa [B, Algebra.TensorProduct.basis_apply, Finset.sum_apply, map_sum, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      Algebra.TensorProduct.map_tmul] using hz
    exact Fintype.linearIndependent_iff.1 (Algebra.TensorProduct.basis A b).linearIndependent _ hz' i
  have hc : ∀ i, B.repr z i = 0 := fun i =>
    adele_eq_zero_of_comp (fun v => key (evFin F v) (hf v) i) (fun w => key (evInf F w) (hi w) i)
  rw [← B.sum_repr z]
  simp [hc]

variable {σ : E →ₐ[F] E} {n : ℕ} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E}

end GlobalTheory.SWOpFin
