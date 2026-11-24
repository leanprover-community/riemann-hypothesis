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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.StCheck

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}


theorem link_simil {σ : ℕ} {B : BesLev D σ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E} (h : IsLineVec L' ζ')
    (l : Link B L' ζ') : l.τᴴ * (B.L.gram * l.τ) = (D.host.xi0 * star D.host.xi0) • L'.gram := by
  have e : star ζ' ⬝ᵥ (l.τᴴ * (B.L.gram * l.τ)) *ᵥ ζ' =
      star ζ' ⬝ᵥ ((D.host.xi0 * star D.host.xi0) • L'.gram) *ᵥ ζ' := by
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.star_mulVec, ← Matrix.mulVec_mulVec, l.map, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, ← l.norm, star_neg, Matrix.mulVec_neg, neg_dotProduct_neg]
  have hu : Unique (Fin L'.rank) := by rw [h.1]; infer_instance
  have h2 := h.2
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_unique] at e h2
  funext i j
  rw [Subsingleton.elim i default, Subsingleton.elim j default]
  have a : star ζ' default ≠ 0 := left_ne_zero_of_mul h2
  have b : ζ' default ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul h2)
  have c := mul_left_cancel₀ a e
  have c' := mul_right_cancel₀ b c
  exact c'

end GlobalTheory.Unf.StCheck

end
