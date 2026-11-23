module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNeZeroForallPointExtendSubalgebra
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
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
import GroundTheory.FunctionField.PlaceDefs

@[expose] public section

open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

theorem UpperTheory.exists_specialization_of_eval_ne_zero :
    ∀ (k L : Type) [Field k] [IsAlgClosed k] [Field L] [Algebra k L] (n : ℕ) (x : Fin n → L) (s : Finset L), ∃ g : MvPolynomial (Fin n) k, MvPolynomial.aeval x g ≠ 0 ∧ ∀ c : Fin n → k, (∀ p : MvPolynomial (Fin n) k, MvPolynomial.aeval x p = 0 → MvPolynomial.eval c p = 0) → MvPolynomial.eval c g ≠ 0 → ∃ (R : Subalgebra k L) (hx : ∀ i, x i ∈ R) (φ : R →ₐ[k] k), (s : Set L) ⊆ R ∧ ∀ i, φ ⟨x i, hx i⟩ = c i := by
  intro k L _ _ _ _ n x s
  let f : MvPolynomial (Fin n) k →ₐ[k] L := MvPolynomial.aeval x
  let J : Ideal (MvPolynomial (Fin n) k) := RingHom.ker f
  haveI : J.IsPrime := RingHom.ker_isPrime _
  let ξ : (MvPolynomial (Fin n) k ⧸ J) →ₐ[k] L := Ideal.kerLiftAlg f
  have hξinj : Function.Injective ξ := Ideal.kerLiftAlg_injective f
  have hξmk : ∀ p, ξ (Ideal.Quotient.mk J p) = MvPolynomial.aeval x p := fun p => rfl
  haveI : Algebra.FiniteType k (MvPolynomial (Fin n) k ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k J) (Ideal.Quotient.mkₐ_surjective k J)
  obtain ⟨a, S, hξ, ha, hs, H⟩ := GlobalTheory.exists_ne_zero_forall_point_extend_subalgebra k
    (MvPolynomial (Fin n) k ⧸ J) L ξ hξinj s
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨g, fun h0 => ha (Ideal.Quotient.eq_zero_iff_mem.2 h0), fun c hc hg => ?_⟩
  let e : MvPolynomial (Fin n) k →ₐ[k] k := MvPolynomial.aeval c
  have he : ∀ p, e p = MvPolynomial.eval c p := fun p => by
    simp [e, MvPolynomial.coe_aeval_eq_eval]
  let φ : (MvPolynomial (Fin n) k ⧸ J) →ₐ[k] k :=
    Ideal.Quotient.liftₐ J e (fun p hp => by
      rw [he]
      exact hc p hp)
  have hφmk : ∀ p, φ (Ideal.Quotient.mk J p) = e p := fun p => rfl
  obtain ⟨ψ, hψ⟩ := H φ (by rw [hφmk, he]; exact hg)
  have hxS : ∀ i, x i ∈ S := fun i => by
    have := hξ (Ideal.Quotient.mk J (MvPolynomial.X i))
    rwa [hξmk, MvPolynomial.aeval_X] at this
  refine ⟨S, hxS, ψ, fun t ht => hs t ht, fun i => ?_⟩
  have h1 : (⟨x i, hxS i⟩ : S) = ⟨ξ (Ideal.Quotient.mk J (MvPolynomial.X i)), hξ _⟩ :=
    Subtype.ext (((hξmk _).trans (MvPolynomial.aeval_X x i)).symm)
  rw [h1, hψ, hφmk, he, MvPolynomial.eval_X]
