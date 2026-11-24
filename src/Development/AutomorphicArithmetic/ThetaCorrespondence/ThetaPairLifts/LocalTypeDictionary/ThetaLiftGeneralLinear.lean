module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GlThetaLiftIsClosed
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

@[expose] public section

section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.Published
open scoped TensorProduct

theorem _root_.GlobalTheory.T.theta_lift_general_linear : BernsteinZelevinskyFiniteness → BernsteinUnitaryProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (μ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin (r + t)) k) W), r < t → IsSmoothChar μ → IsUnitaryChar μ → IsSmooth σ → σ.IsIrreducible → IsUnitarisable σ → IsSmooth π → π.IsIrreducible → ThetaPair μ σ π → Nonempty (π.Equiv (prod₂ σ (detRep (Fin t) μ))) := by
  first | exact @_root_.UpperTheory.Lit.Mix.gl_thetaLift_isClosed | exact _root_.UpperTheory.Lit.Mix.gl_thetaLift_isClosed | (intros; apply _root_.UpperTheory.Lit.Mix.gl_thetaLift_isClosed <;> assumption)
end
