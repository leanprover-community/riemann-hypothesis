module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ResLine.Swap

section Swap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] [NumberField E] in
theorem cT_add' (σ : E →ₐ[F] E) {a b : Type} (M N : Matrix a b E) :
    Formalism.UG.cT (σ : E →+* E) (M + N) = Formalism.UG.cT (σ : E →+* E) M + Formalism.UG.cT (σ : E →+* E) N := by
  ext i j; simp [Formalism.UG.cT]

omit [NumberField F] [NumberField E] in
theorem cT_sub' (σ : E →ₐ[F] E) {a b : Type} (M N : Matrix a b E) :
    Formalism.UG.cT (σ : E →+* E) (M - N) = Formalism.UG.cT (σ : E →+* E) M - Formalism.UG.cT (σ : E →+* E) N := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_cT_of_isCMExt {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {a b : Type} (M : Matrix a b E) :
    Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) M) = M := by
  ext i j; simp [Formalism.UG.cT, GlobalTheory.SiegelSet.sigma_sigma hσ]

omit [NumberField F] [NumberField E] in
theorem cT_eq_of_isHermND {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) :
    Formalism.UG.cT (σ : E →+* E) J = J := by
  ext i j; simpa [Formalism.UG.cT] using hJ.1 i j

end Swap

end GlobalTheory.ResLine.Swap

end
