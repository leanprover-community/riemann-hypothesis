module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JetsTorsionTranslatesCmThetaProduct
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.jets_torsion_translates_cm_theta_product : ∀ (D : D7), Inp D → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → Nat.Coprime (Ideal.absNorm cc) p → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (a d r : ℕ) (b : Fin r → Matrix (Fin d) (Fin a) D.host.E), OnB D b → LocBasis D p (YYl D (stdL D a) (stdL D d)) b → ∀ (s : VC D a d) (Nn : ℕ), 0 < Nn → Nn • s ∈ LaB D (tor0 D cc δ) b → (p ∣ Nn → SplitIn D p) → ∀ (n : ℕ) (y : Fin n → Matrix (Fin d) (Fin a) D.host.E), (∀ i, y i ∈ YYl D (stdL D a) (stdL D d)) → iteratedFDeriv ℂ n (U D (tor0 D cc δ) s (pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0))) 0 (fun i => embV D (tor0 D cc δ) (y i)) ∈ Qbar ∧ ‖lamC lam (iteratedFDeriv ℂ n (U D (tor0 D cc δ) s (pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0))) 0 (fun i => embV D (tor0 D cc δ) (y i)))‖ ≤ (‖(Nn : ℂ_[p])‖⁻¹) ^ n * (if p = D.host.d then (p : ℝ) ^ ((n : ℝ) / 4) else 1) := by
  first | exact @GlobalTheory.ProductJets.jets_translate_product | exact GlobalTheory.ProductJets.jets_translate_product | (intros; apply GlobalTheory.ProductJets.jets_translate_product <;> assumption)
