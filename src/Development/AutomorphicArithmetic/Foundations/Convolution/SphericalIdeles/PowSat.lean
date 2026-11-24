module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.SphConj
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C GlobalTheory.CuspRep Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V.Published UpperTheory.CBC

namespace UpperTheory.ConvolutionTheory.Sph.PW

variable {K : Type} [Field K] [NumberField K]

private theorem ideleModule_localIdele (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ((GroundTheory.Global.IdeleGroup.ideleModule K (Neutral.B1.localIdele K v x)).1 : ℝ) =
      ‖(x : v.adicCompletion K)‖ := by
  have e : Neutral.B1.localIdele K v x = GroundTheory.Global.IdeleGroup.finiteEmbedding v x :=
    Units.ext rfl
  rw [e]
  exact GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding v x

private theorem norm_eq_zpow (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) (n : ℤ)
    (h : Valued.v x = WithZero.exp n) : ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ n := by
  rw [FinitePlace.norm_def, h, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  change (Ideal.absNorm v.asIdeal : ℝ) ^ (WithZero.exp n).log = _
  rw [WithZero.log_exp]

private theorem loc_eq {χ : HChar K} {s : ℂ} (h : UpperTheory.ConvolutionTheory.T.IsPow χ s)
    (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ((χ.loc v x : ℂˣ) : ℂ) = ((‖(x : v.adicCompletion K)‖ : ℝ) : ℂ) ^ s := by
  rw [← ideleModule_localIdele]
  exact h _

end UpperTheory.ConvolutionTheory.Sph.PW

open UpperTheory.ConvolutionTheory.Sph.PW in
theorem UpperTheory.ConvolutionTheory.Sph.powSat :
    UpperTheory.ConvolutionTheory.Sph.PowSat := by
  intro K _ _ χ s h v
  refine ⟨fun x hx => Units.ext ?_, ?_⟩
  · rw [loc_eq h, norm_eq_zpow v _ 0 (by simpa [Formalism.L2.Host.IsUnitAt] using hx)]
    simp
  · have e : χ.val v = χ.loc v (Formalism.L2.Host.atFin v (Formalism.L2.Host.unif v)) := rfl
    rw [e, loc_eq h, norm_eq_zpow v _ (-1) (Formalism.L2.Host.unif_spec v), zpow_neg_one,
      Complex.ofReal_inv, Complex.inv_cpow _ _ (by
        rw [Complex.arg_ofReal_of_nonneg (by positivity)]
        exact Real.pi_pos.ne), Complex.cpow_neg]
    simp
