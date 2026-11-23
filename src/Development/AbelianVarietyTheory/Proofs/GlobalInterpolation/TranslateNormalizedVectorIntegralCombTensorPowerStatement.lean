module

public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateNormalizedVectorIntegralCombTensorPower
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero

@[expose] public section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

theorem _root_.GlobalTheory.T.translate_normalized_vector_integral_comb_tensor_power : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ χ : IdE D → ℂ, IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → EqAt D p (StandardLatticesGL3.stdL D N) L → EqAt D p (StandardLatticesGL3.stdL D N') L' → ∀ t : VC D N N', TorsPrime D p (La D B.tor L L') t → ∃ (m : ℕ) (c : Fin m → ℂ) (s : Fin m → VC D N N'), (∀ k, c k ∈ Qbar ∧ IsIntP (lamC lam (c k))) ∧ (∀ k, TorsPrime D p (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (s k)) ∧ U D B.tor t (B.eNat χ N N' L L') = fun z => ∑ k, c k * U D B.tor (s k) (B.thZero N N') z := by
  first | exact @GlobalTheory.MomN.transl_normVec_int | exact GlobalTheory.MomN.transl_normVec_int | (intros; apply GlobalTheory.MomN.transl_normVec_int <;> assumption)
