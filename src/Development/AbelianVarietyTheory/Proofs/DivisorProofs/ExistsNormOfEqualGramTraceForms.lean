module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAevalEqOfSeparable
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitLemma.IsometryUnit

theorem isometry_unit : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K), B.P.Separable → ∀ (ε : B.A), (ε = 1 ∨ ε = -1) → ∀ (a : ℕ) (β β' : B.Aˣ), B.σ (β : B.A) = β * (ε * B.g) → B.σ (β' : B.A) = β' * (ε * B.g) → ∀ b b' : Module.Basis (Fin a) K.E B.A, (∀ i j, B.herm β (b i) (b j) = B.herm β' (b' i) (b' j)) → ∃ t : B.Aˣ, (β' : B.A) = β * (t * B.σ t) := by
  intro K B hs ε hε a β β' hβ hβ' b b' hgram
  have hs' : (LinearMap.mulLeft K.E B.g).charpoly.Separable := hs
  have σsm : ∀ (r : K.E) (y : B.A), B.σ (r • y) = K.c r • B.σ y := by
    intro r y; rw [Algebra.smul_def, map_mul, B.σ_alg, Algebra.smul_def]
  have trσ := GlobalTheory.UnitLemma.PairClass.trace_σ K B
  have addL : ∀ (x u u' v : B.A), B.herm x (u + u') v = B.herm x u v + B.herm x u' v := by
    intro x u u' v; unfold InvAlg.herm; rw [mul_add, add_mul, map_add (f := _)]
  have subL : ∀ (x u u' v : B.A), B.herm x (u - u') v = B.herm x u v - B.herm x u' v := by
    intro x u u' v; unfold InvAlg.herm; rw [mul_sub, sub_mul, map_sub]
  have smulL : ∀ (x : B.A) (r : K.E) (u v : B.A), B.herm x (r • u) v = r * B.herm x u v := by
    intro x r u v; unfold InvAlg.herm; rw [mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]
  have addR : ∀ (x u v v' : B.A), B.herm x u (v + v') = B.herm x u v + B.herm x u v' := by
    intro x u v v'; unfold InvAlg.herm; rw [map_add (f := _), mul_add, map_add (f := _)]
  have smulR : ∀ (x : B.A) (r : K.E) (u v : B.A), B.herm x u (r • v) = K.c r * B.herm x u v := by
    intro x r u v; unfold InvAlg.herm; rw [σsm, mul_smul_comm, map_smul, smul_eq_mul]

  have asym : ∀ (x : B.A), B.σ x = x * (ε * B.g) → ∀ z y, K.c (B.herm x z y) = B.herm x (ε * B.g * y) z := by
    intro x hx z y; unfold InvAlg.herm
    rw [← trσ]; congr 1; simp only [map_mul, B.σ_σ, hx]; ring

  have nd : ∀ x : B.A, (∀ y, Algebra.trace K.E B.A (x * y) = 0) → x = 0 :=
    fun x hx => GlobalTheory.UnitLemma.PairClass.trace_nondeg K.E B.A B.g hs' x hx
  have ndh : ∀ w : B.A, (∀ z, B.herm β w z = 0) → w = 0 := by
    intro w hw
    have h0 : (β : B.A) * w = 0 := nd _ (fun y => by
      have := hw (B.σ y); unfold InvAlg.herm at this; rwa [B.σ_σ] at this)
    have := congrArg (fun z => ((β⁻¹ : B.Aˣ) : B.A) * z) h0
    simpa [← mul_assoc] using this

  let φ : B.A ≃ₗ[K.E] B.A := b'.equiv b (Equiv.refl _)
  have hφb : ∀ i, φ (b' i) = b i := fun i => by simp [φ, Module.Basis.equiv_apply]
  have hφ : ∀ u v, B.herm β (φ u) (φ v) = B.herm β' u v := by
    let F₁ : B.A →ₗ[K.E] B.A →ₛₗ[(K.c : K.E →+* K.E)] K.E :=
      LinearMap.mk₂'ₛₗ (RingHom.id K.E) (K.c : K.E →+* K.E) (fun u v => B.herm β (φ u) (φ v))
        (fun u u' v => by rw [map_add (f := _), addL]) (fun r u v => by rw [map_smul, smulL]; rfl)
        (fun u v v' => by rw [map_add (f := _), addR]) (fun r u v => by rw [map_smul, smulR]; rfl)
    let F₂ : B.A →ₗ[K.E] B.A →ₛₗ[(K.c : K.E →+* K.E)] K.E :=
      LinearMap.mk₂'ₛₗ (RingHom.id K.E) (K.c : K.E →+* K.E) (fun u v => B.herm β' u v)
        (fun u u' v => addL _ _ _ _) (fun r u v => smulL _ _ _ _)
        (fun u v v' => addR _ _ _ _) (fun r u v => smulR _ _ _ _)
    have hF : F₁ = F₂ := LinearMap.ext_basis b' b' (fun i j => by
      simp only [F₁, F₂, LinearMap.mk₂'ₛₗ_apply, hφb]; exact hgram i j)
    intro u v
    have := LinearMap.congr_fun₂ hF u v
    simp only [F₁, F₂, LinearMap.mk₂'ₛₗ_apply] at this
    exact this
  have hcomm : ∀ u, φ (ε * B.g * u) = ε * B.g * φ u := by
    intro u
    rw [← sub_eq_zero]
    apply ndh
    intro z
    obtain ⟨v, rfl⟩ : ∃ v, φ v = z := ⟨φ.symm z, by simp⟩
    rw [subL, hφ, ← asym _ hβ', ← hφ, asym _ hβ, sub_self]
  have hg : ∀ u, φ (B.g * u) = B.g * φ u := by
    intro u
    rcases hε with rfl | rfl
    · simpa using hcomm u
    · have := hcomm u
      simp only [neg_mul, one_mul, map_neg, neg_inj] at this
      exact this
  have hpoly : ∀ q : K.E[X], ∀ u, φ (aeval B.g q * u) = aeval B.g q * φ u := by
    intro q
    induction q using Polynomial.induction_on with
    | C r => intro u; rw [aeval_C, ← Algebra.smul_def, ← Algebra.smul_def, map_smul]
    | add p q hp hq => intro u; rw [map_add (f := _), add_mul, add_mul, map_add (f := _), hp, hq]
    | monomial n r h =>
      intro u
      have e : aeval B.g (C r * X ^ (n + 1)) = aeval B.g (C r * X ^ n) * B.g := by
        simp [pow_succ, mul_assoc]
      rw [e, mul_assoc, h, hg, mul_assoc]
  have hmul : ∀ y, φ y = y * φ 1 := by
    intro y
    obtain ⟨q, rfl⟩ := GlobalTheory.UnitLemma.PairClass.exists_aeval_eq_of_separable B.g hs' y
    simpa using hpoly q 1
  have ht : IsUnit (φ 1) := by
    have := hmul (φ.symm 1)
    rw [LinearEquiv.apply_symm_apply] at this
    exact ⟨⟨φ 1, φ.symm 1, by rw [mul_comm]; exact this.symm, this.symm⟩, rfl⟩
  refine ⟨ht.unit, ?_⟩
  rw [IsUnit.unit_spec]
  rw [← sub_eq_zero]
  apply nd
  intro y
  have h1 := hφ y 1
  rw [hmul y] at h1
  unfold InvAlg.herm at h1
  rw [map_one B.σ, mul_one] at h1
  have h2 : ((β' : B.A) - β * (φ 1 * B.σ (φ 1))) * y = (β' : B.A) * y - β * (y * φ 1) * B.σ (φ 1) := by ring
  rw [h2, map_sub, h1, sub_self]

end GlobalTheory.UnitLemma.IsometryUnit
