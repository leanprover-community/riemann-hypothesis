module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCPullbackBijectiveFiniteStrictlyHenselianStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCechNerveLevelSpecTensorPowerStatement
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
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep.LevelZero

variable {R : Type} [CommRing R]

theorem pull_iso_bijective {E E' : Spc} (e : E ≅ E') (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R e.hom F n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

theorem cechC_pull_bijective : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) →
    ∀ (A' : Type) [CommRing A'] [Algebra A A'], Module.Finite A A' → ∀ (k : ℕ) (i : ℤ),
    Function.Bijective (pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q i) 0) := by
  intro q _ A _ hA hq A' _ _ hfin k i
  obtain ⟨e0, e, h1, -⟩ := GlobalTheory.T.laurentCechNerve_level_spec_tensorPower A A' k
  haveI := hfin
  have hT : Module.Finite A (PiTensorProduct A (fun _ : Fin (k + 1) => A')) := inferInstance
  have hr0 := GlobalTheory.T.laurentC_pullback_bijective_finite_strictlyHenselian q A hA hq (PiTensorProduct A (fun _ : Fin (k + 1) => A')) hT i
  have hmap := congrArg (fun f => disc.map f) h1
  simp only [Functor.map_comp] at hmap
  have heq : ∀ x, pull _ (disc.map e.hom) (tw q i) 0 (pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q i) 0 x) =
      pull _ (spMap (LaurentPolynomial.C : PiTensorProduct A (fun _ : Fin (k + 1) => A') →+*
        LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A')))) (tw q i) 0
        (pull _ (disc.map e0.hom) (tw q i) 0 x) := by
    intro x
    rw [← pull_comp, hmap, pull_comp]
    rfl
  have hcomp : (pull _ (disc.map e.hom) (tw q i) 0) ∘ (pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q i) 0) =
      (pull _ (spMap (LaurentPolynomial.C : PiTensorProduct A (fun _ : Fin (k + 1) => A') →+*
        LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A')))) (tw q i) 0) ∘
        (pull _ (disc.map e0.hom) (tw q i) 0) := funext heq
  have he : Function.Bijective (pull _ (disc.map e.hom) (tw q i) 0) :=
    pull_iso_bijective (disc.mapIso e) (tw q i) 0
  have he0 : Function.Bijective (pull _ (disc.map e0.hom) (tw q i) 0) :=
    pull_iso_bijective (disc.mapIso e0) (tw q i) 0
  rw [← Function.Bijective.of_comp_iff' he, hcomp]
  exact hr0.comp he0

end GlobalTheory.EtC.GmStep.LevelZero
