module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem mir_inUJ_iff (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) : Formalism.REAL.inUJ ε g ↔ inUJ ε g := by
  first
  | rfl

theorem mir_UJset_eq (ε : Fin n → Bool) : Formalism.MainNotions.S.UJset ε = UJset ε := by
  first
  | rfl

theorem mir_Kset_eq (ε : Fin n → Bool) : Formalism.REAL.Kset ε = Kset ε := by
  first
  | rfl

theorem mir_lowK_eq (ε : Fin n → Bool) (lam : Fin n → ℝ) : Formalism.QuantumDeterminants.lowK ε lam = lowK ε lam := by
  first
  | rfl

theorem mir_isHCParam_iff (lam : Fin n → ℝ) : Formalism.QuantumDeterminants.IsHCParam lam ↔ S7.IsHCParam lam := by
  first
  | rfl

theorem mir_gapAtLeast_iff (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) :
    Formalism.QuantumDeterminants.GapAtLeast ε lam h ↔ GapAtLeast ε lam h := by
  first
  | rfl

theorem mir_isURepOn_iff {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (G : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    Formalism.MainNotions.S.IsURepOn G σ ↔ IsURepOn G σ := by
  first
  | rfl

theorem memLp_muG_of_haar (ε : Fin n → Bool) {X : Type*} [NormedAddCommGroup X]
    (F : Matrix (Fin n) (Fin n) ℂ → X) (p : ENNReal)
    (hF : ∀ μ : Measure (S7.UJ ε), μ.IsHaarMeasure → MemLp (fun g : S7.UJ ε => F (S7.toM g)) p μ) :
    MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) p (Formalism.REAL.muG ε) := by
  exact hF _ (Formalism.REAL.instIsHaarMuG n ε)

theorem integrable_muG_of_haar (ε : Fin n → Bool) {X : Type*} [NormedAddCommGroup X]
    (F : Matrix (Fin n) (Fin n) ℂ → X)
    (hF : ∀ μ : Measure (S7.UJ ε), μ.IsHaarMeasure → Integrable (fun g : S7.UJ ε => F (S7.toM g)) μ) :
    Integrable (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) (Formalism.REAL.muG ε) := by
  exact hF _ (Formalism.REAL.instIsHaarMuG n ε)

theorem measurePreserving_mul_right (ε : Fin n → Bool) (y : Formalism.REAL.UJ ε) :
    MeasurePreserving (fun x : Formalism.REAL.UJ ε => x * y) (Formalism.REAL.muG ε) (Formalism.REAL.muG ε) := by
  exact ⟨(continuous_mul_const y).measurable, Formalism.REAL.indefinite_unitary_unimodular n ε y⟩

end ReciprocityTheory.ChartRestriction.DS
