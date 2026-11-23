module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModel
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Order.Filter.Germ.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Analytic.Constructions

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

noncomputable section

def holGerms {σ : Type} [Fintype σ] (w : σ → ℂ) : Subring (Germ (𝓝 w) ℂ) where
  carrier := {φ | ∃ f : (σ → ℂ) → ℂ, AnalyticAt ℂ f w ∧ (f : Germ (𝓝 w) ℂ) = φ}
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, rfl⟩
  one_mem' := ⟨fun _ => 1, analyticAt_const, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, rfl⟩
  zero_mem' := ⟨fun _ => 0, analyticAt_const, rfl⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, rfl⟩

theorem analyticAt_eval_polynomial {σ : Type} [Fintype σ] (w : σ → ℂ) (q : MvPolynomial σ ℂ) :
    AnalyticAt ℂ (fun z : σ → ℂ => eval z q) w := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : σ → ℂ => a) w)
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p i hp =>
    have hi : AnalyticAt ℂ (fun z : σ → ℂ => z i) w :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt w
    simp only [map_mul, eval_X]
    exact hp.mul hi

def polyGerm {σ : Type} [Fintype σ] (w : σ → ℂ) : MvPolynomial σ ℂ →+* holGerms w :=
  ((Germ.coeRingHom (𝓝 w)).comp (RingHom.pi fun z : σ → ℂ => (MvPolynomial.eval z))).codRestrict
    (holGerms w) fun q => ⟨fun z => eval z q, analyticAt_eval_polynomial w q, rfl⟩

def ZariskiAnalyticNormality.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → w ∈ zeroSetIn I →
      (I.map (polyGerm w)).IsPrime ∧ IsIntegrallyClosed (holGerms w ⧸ I.map (polyGerm w))

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
