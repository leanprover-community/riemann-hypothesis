module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InstBorelUK
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousCoeffRowAct
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped ComplexConjugate Kronecker InnerProductSpace

namespace GlobalTheory.CompanionTheory.CxAvg

section Abstract

variable {K E : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
  (μ : Measure K) [μ.IsHaarMeasure] (F : K →* (E →L[ℂ] E))

variable {F}

end Abstract

section Concrete

open PositivityTheory.RgTw (Mat hb)
open PositivityTheory.RgBcC

variable {n : ℕ}

theorem Rm_unitary (lam : Fin n → ℤ) (k : Matrix.unitaryGroup (Fin n) ℂ) :
    Rm lam k.1 = LinearMap.toMatrix (wb lam) (wb lam)
      (GlobalTheory.Branching.sqRep ℂ n (dw lam) (GlobalTheory.Branching.unitaryIncl n k)) := by
  have h : IsUnit k.1.det := (Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.Branching.unitaryIncl n k).isUnit
  have e : Matrix.nonsingInvUnit k.1 h = GlobalTheory.Branching.unitaryIncl n k := Units.ext rfl
  rw [Rm, dite_eq_left h, e]

theorem Rm_mul (lam : Fin n → ℤ) (k k' : Matrix.unitaryGroup (Fin n) ℂ) :
    Rm lam (k * k').1 = Rm lam k.1 * Rm lam k'.1 := by
  rw [Rm_unitary, Rm_unitary, Rm_unitary, map_mul, map_mul, Module.End.mul_eq_comp]
  exact LinearMap.toMatrix_comp _ _ _ _ _

theorem Rm_one (lam : Fin n → ℤ) : Rm lam (1 : Matrix.unitaryGroup (Fin n) ℂ).1 = 1 := by
  rw [Rm_unitary, map_one, map_one]
  exact LinearMap.toMatrix_id _

theorem continuous_unitaryIncl : Continuous (GlobalTheory.Branching.unitaryIncl n) := by
  rw [Units.continuous_iff]
  exact ⟨continuous_subtype_val, continuous_subtype_val.matrix_conjTranspose⟩

theorem continuous_Rm (lam : Fin n → ℤ) :
    Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => Rm lam k.1 := by
  simp only [Rm_unitary]
  refine continuous_matrix fun i j => ?_
  simp only [LinearMap.toMatrix_apply]
  exact (GlobalTheory.CompanionTheory.WInfCont.continuous_sqRep_coeff (dw lam) (wb lam j) ((wb lam).coord i)).comp
    continuous_unitaryIncl

end Concrete

end GlobalTheory.CompanionTheory.CxAvg
