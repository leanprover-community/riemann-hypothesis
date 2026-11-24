module

public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalRingPointDualNumberSndLinearDerivation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TangentOrigin

theorem _root_.GlobalTheory.T.evalRingPoint_dualNumber_snd_linear_derivation : ∀ {X : Scheme.{0}} {S K : Type} [CommRing S] [Field K] (G : Sp S ⟶ X) (ψ : S →+* K) {ι : Type} [Fintype ι] (θc : ι → (S →+* DualNumber K)) (θ : S →+* DualNumber K) (m : ι → K), (∀ a s, (θc a s).fst = ψ s) → (∀ s, (θ s).fst = ψ s) → (∀ s, (θ s).snd = ∑ a, m a * (θc a s).snd) → ∀ (O : X.Opens) (f : Γ(X, O)) (h : ⊤ ≤ (spMap θ ≫ G) ⁻¹ᵁ O) (h' : ∀ a, ⊤ ≤ (spMap (θc a) ≫ G) ⁻¹ᵁ O), (evalPt (spMap θ ≫ G) O h f).snd = ∑ a, m a * (evalPt (spMap (θc a) ≫ G) O (h' a) f).snd := by
  first | exact @GlobalTheory.DualEval.evalPt_snd_sum | exact GlobalTheory.DualEval.evalPt_snd_sum | (intros; apply GlobalTheory.DualEval.evalPt_snd_sum <;> assumption)
