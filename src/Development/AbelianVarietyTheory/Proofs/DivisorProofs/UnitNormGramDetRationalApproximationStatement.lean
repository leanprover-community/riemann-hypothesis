module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNormOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitNormGramDetRationalApproximation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

theorem _root_.GlobalTheory.T.unitNorm_gramDet_rational_approximation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [NontriviallyNormedField K] [CompleteSpace K] [Algebra F K], DenseRange (algebraMap F K) → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x y : Fin M → E, hE σ J x x ≠ 0 → ∀ w : Fin M → K ⊗[F] E, IsUnitNorm K σ (-(gram2R K σ J (fun i => inclR K (x i)) w)) → IsUnitNorm K σ (-(gram2R K σ J w (fun i => inclR K (y i)))) → ∃ z : Fin M → E, hE σ J z z ≠ 0 ∧ IsUnitNorm K σ (-(inclR K (gram2E σ J x z))) ∧ IsUnitNorm K σ (-(inclR K (gram2E σ J z y))) := by
  first | exact @GlobalTheory.PlaneNormApprox.approx | exact GlobalTheory.PlaneNormApprox.approx | (intros; apply GlobalTheory.PlaneNormApprox.approx <;> assumption)
