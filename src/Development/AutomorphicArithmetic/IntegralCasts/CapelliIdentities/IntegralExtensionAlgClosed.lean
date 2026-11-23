module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.GoingUp

@[expose] public section

theorem UpperTheory.Reformulated.B.IntegralExtensionAlgClosed.exists_ringHom_extension_of_integral :
    ∀ (R S K : Type) [inst : CommRing R] [inst_1 : CommRing S]
    [inst_2 : Algebra R S] [Algebra.IsIntegral R S] [inst_4 : Field K] [IsAlgClosed K],
    Function.Injective (⇑(Algebra.algebraMap R S) : R → S) →
      ∀ (b : R →+* K), ∃ (Φ : S →+* K), Φ.comp (Algebra.algebraMap R S) = b := by
  intro R S K _ _ _ _ _ _ hinj b
  haveI hp : (RingHom.ker b).IsPrime := RingHom.ker_isPrime b
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := S)
    (RingHom.ker b) ⊥ (by
      intro x hx
      have hx0 : algebraMap R S x = 0 := by simpa using hx
      have : x = 0 := hinj (by simpa using hx0)
      simp [this])
  haveI : Q.LiesOver (RingHom.ker b) := ⟨hQp.symm⟩
  letI : Algebra (R ⧸ RingHom.ker b) K := (RingHom.kerLift b).toAlgebra
  haveI : FaithfulSMul (R ⧸ RingHom.ker b) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective b)
  haveI : Algebra.IsIntegral (R ⧸ RingHom.ker b) (S ⧸ Q) := inferInstance
  haveI : FaithfulSMul (R ⧸ RingHom.ker b) (S ⧸ Q) := inferInstance
  haveI : Module.IsTorsionFree (R ⧸ RingHom.ker b) (S ⧸ Q) :=
    Module.isTorsionFree_iff_faithfulSMul.2 inferInstance
  haveI : Module.IsTorsionFree (R ⧸ RingHom.ker b) K :=
    Module.isTorsionFree_iff_faithfulSMul.2 inferInstance
  haveI : Algebra.IsAlgebraic (R ⧸ RingHom.ker b) (S ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let ψ : (S ⧸ Q) →ₐ[R ⧸ RingHom.ker b] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨ψ.toRingHom.comp (Ideal.Quotient.mk Q), ?_⟩
  ext x
  exact ψ.commutes (Ideal.Quotient.mk (RingHom.ker b) x)
