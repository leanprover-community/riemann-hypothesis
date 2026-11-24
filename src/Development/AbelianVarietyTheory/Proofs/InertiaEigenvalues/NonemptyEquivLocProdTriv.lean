module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions

namespace GlobalTheory.UnitaryBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem infGL_mem_UA {n : ℕ} (y : GL (Fin n) (Cinf E)) (hy : y.valᴴ * y.val = 1) : infGL E n y ∈ UA E n := by
  change cT (conjAd E) (infGL E n y).val * 1 * (infGL E n y).val = 1
  have h1 : (infGL E n y).val.map (pInf E) = y.val := congrArg Units.val (pInf_infGL y)
  have h2 : (infGL E n y).val.map (pFin E) = 1 := congrArg Units.val (pFin_infGL y)
  have h3 : (cT (conjAd E) (infGL E n y).val).map (pInf E) = y.valᴴ := by
    ext1 i j
    rw [Matrix.conjTranspose_apply, ← h1]
    exact (infEq E).symm_apply_apply _
  have h4 : (cT (conjAd E) (infGL E n y).val).map (pFin E) = 1 := by
    ext1 i j
    change conjFin (IsCMField.complexConj E).toRingEquiv (((infGL E n y).val.map (pFin E)) j i) = _
    rw [h2]
    simp only [Matrix.one_apply, eq_comm (a := j)]
    split_ifs <;> simp
  have h5 := congrArg₂ (· * ·) h3 h1
  have h6 := congrArg₂ (· * ·) h4 h2
  simp only [← Matrix.map_mul, hy, mul_one] at h5 h6
  rw [mul_one]
  ext1 i j
  refine ad_ext ((congrFun₂ h5 i j).trans ?_) ((congrFun₂ h6 i j).trans ?_) <;>
  · simp only [Matrix.one_apply]
    split_ifs <;> simp


end GlobalTheory.UnitaryBC

end
