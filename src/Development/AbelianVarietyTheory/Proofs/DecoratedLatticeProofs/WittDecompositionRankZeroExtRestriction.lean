module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepRankZeroWittEmbeddingValueAtZero

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing MeasureTheory GlobalTheory.FinPl.VLast

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.VLast.KernPf

variable {D : D7}

theorem wittDecomposition_rankZero_coreEmbed_proj {S S₀ : HSp D} (e : HypDec S S₀ 0) : e.j0 ⬝ e.p0 = 1 := by
  have h := e.sum_eq_one
  have h1 : e.jX ⬝ e.pX = 0 := by ext i k; simp [Matrix.mul_apply]
  have h2 : e.jY ⬝ e.pY = 0 := by ext i k; simp [Matrix.mul_apply]
  rwa [h1, h2, zero_add, add_zero] at h

def wittCoreRestrictionHom {S S₀ : HSp D} {ρ : ℕ} (e : HypDec S S₀ ρ) (T : HSp D) : WO S T →+ WO S₀ T where
  toFun w := w ⬝ e.j0
  map_zero' := Matrix.zero_mul _
  map_add' _ _ := Matrix.add_mul _ _ _

theorem wittCoreRestrictionHom_apply {S S₀ : HSp D} {ρ : ℕ} (e : HypDec S S₀ ρ) (T : HSp D) (w : WO S T) : wittCoreRestrictionHom e T w = w ⬝ e.j0 := rfl

theorem wittDecomposition_rankZero_ext_restriction {S S₀ : HSp D} (e : HypDec S S₀ 0) (T : HSp D) (w : WO S T) : e.ext0 T (wittCoreRestrictionHom e T w) = w := by
  rw [HypDec.matrixExtendByZero_apply, wittCoreRestrictionHom_apply, Matrix.mul_assoc, wittDecomposition_rankZero_coreEmbed_proj, Matrix.mul_one]

end GlobalTheory.FinPl.VLast.KernPf

namespace GlobalTheory.FinPl.VLast.KernPf


end GlobalTheory.FinPl.VLast.KernPf
