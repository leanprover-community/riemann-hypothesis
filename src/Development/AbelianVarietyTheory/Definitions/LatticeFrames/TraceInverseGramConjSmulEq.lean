module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
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

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.Model

variable {D : D7}

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule

variable {ρ : ℕ} {B : BesLev D ρ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E} (l : Link B L' ζ')

include l in
theorem tau_gram (h : IsLineVec L' ζ') :
    l.τᴴ * (B.L.gram * l.τ) = (D.host.xi0 * star D.host.xi0) • L'.gram := by
  have : Unique (Fin L'.rank) := by rw [h.1]; infer_instance
  have hn := l.norm
  have hm : B.ζ = -(l.τ *ᵥ ζ') := by rw [l.map, neg_neg]
  have h0 := h.2
  rw [hm, star_neg, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg, Matrix.star_mulVec, ← dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc] at hn
  refine Matrix.ext fun i j => ?_
  obtain rfl := Subsingleton.elim i default
  obtain rfl := Subsingleton.elim j default
  generalize l.τᴴ * (B.L.gram * l.τ) = M at hn ⊢
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_unique, Pi.star_apply] at hn h0
  have hz : ζ' default ≠ 0 := fun e => h0 (by rw [e]; simp)
  have hz' : star (ζ' default) ≠ 0 := star_ne_zero.2 hz
  rw [Matrix.smul_apply, smul_eq_mul]
  apply mul_right_cancel₀ hz
  apply mul_left_cancel₀ hz'
  rw [hn]; ring


end GlobalTheory.Unf.Model

end
