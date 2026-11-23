module

public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongOfCongOnFixed
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Invariant.Profinite
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne Pointwise

namespace GlobalTheory.InertiaLift

theorem exists_mem_Ine_eq_on : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver A w →
    ∀ (L : IntermediateField E Ω) (ψ : G E Ω), ψ ∈ Dec (F := E) A →
    (∀ x ∈ L, IsIntegral ℤ x → A.valuation (ψ x - x) < 1) →
    ∃ ι ∈ Ine (F := E) A, ∀ x ∈ L, ι x = ψ x := by
  intro E Ω _ _ _ _ _ A w _ L ψ hψ hL
  letI : TopologicalSpace (IntCl E Ω) := ⊥
  haveI : DiscreteTopology (IntCl E Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl E Ω
  let H := L.fixingSubgroup
  have hH : IsClosed (H : Set (Ω ≃ₐ[E] Ω)) := by
    have e : (H : Set (Ω ≃ₐ[E] Ω)) = ⋂ x : L, ((MulAction.stabilizer (Ω ≃ₐ[E] Ω) (x : Ω) :
        Subgroup (Ω ≃ₐ[E] Ω)) : Set (Ω ≃ₐ[E] Ω)) := by
      ext σ
      simp only [Set.mem_iInter, SetLike.mem_coe, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
      rw [IntermediateField.mem_fixingSubgroup_iff]
      exact ⟨fun h x => h x x.2, fun h x hx => h ⟨x, hx⟩⟩
    rw [e]
    exact isClosed_iInter fun x =>
      (MulAction.stabilizer (Ω ≃ₐ[E] Ω) (x : Ω)).isClosed_of_isOpen
        (stabilizer_isOpen_of_isIntegral (K := E) (x : Ω))
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  let Q := primeBelow (F := E) A
  let R' := FixedPoints.subalgebra (𝓞 E) (IntCl E Ω) H
  have hR' : ∀ b : R', ∀ k ∈ H, k • (b : IntCl E Ω) = b := fun b k hk => b.2 ⟨k, hk⟩
  have : SMulCommClass H R' (IntCl E Ω) := ⟨fun k r b => by
    change (k : Ω ≃ₐ[E] Ω) • ((r : IntCl E Ω) * b) = (r : IntCl E Ω) * (k : Ω ≃ₐ[E] Ω) • b
    rw [smul_mul', hR' r k k.2]⟩
  have : Algebra.IsInvariant R' (IntCl E Ω) H := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩
  have : Q.LiesOver (Q.under R') := ⟨rfl⟩
  have hψQ : ψ • Q = Q := by
    have h1 : ψ • A = A := hψ
    rw [← primeBelow_smul, h1]
  have hfix : ∀ r : R', ψ • (r : IntCl E Ω) - r ∈ Q := by
    intro r
    have hrL : ((r : IntCl E Ω) : Ω) ∈ L := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup L, IntermediateField.mem_fixedField_iff]
      intro f hf
      exact congrArg Subtype.val (hR' r f hf)
    exact hL _ hrL (isIntegral_int_of_isIntegral (r : IntCl E Ω).2)
  let φ : (IntCl E Ω ⧸ Q) ≃ₐ[R' ⧸ Q.under R'] (IntCl E Ω ⧸ Q) := AlgEquiv.ofRingEquiv
    (f := Ideal.quotientEquiv Q Q (MulSemiringAction.toRingEquiv (Ω ≃ₐ[E] Ω) (IntCl E Ω) ψ)
      hψQ.symm)
    (fun r => by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      change Ideal.Quotient.mk Q (ψ • (r : IntCl E Ω)) = Ideal.Quotient.mk Q (r : IntCl E Ω)
      rw [Ideal.Quotient.eq]
      exact hfix r)
  obtain ⟨⟨v, hvQ⟩, hv⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := H)
    (Q.under R') Q φ
  refine ⟨ψ * (v : Ω ≃ₐ[E] Ω)⁻¹, GlobalTheory.InertiaMovesRoot.mem_Ine_of_cong fun b => ?_, fun x hx => ?_⟩
  · have h1 : Ideal.Quotient.mk Q ((v : Ω ≃ₐ[E] Ω) • ((v : Ω ≃ₐ[E] Ω)⁻¹ • b)) =
        Ideal.Quotient.mk Q (ψ • ((v : Ω ≃ₐ[E] Ω)⁻¹ • b)) :=
      DFunLike.congr_fun hv (Ideal.Quotient.mk Q ((v : Ω ≃ₐ[E] Ω)⁻¹ • b))
    rw [smul_inv_smul, eq_comm, Ideal.Quotient.eq] at h1
    rwa [mul_smul]
  · have hv' : ((v : Ω ≃ₐ[E] Ω)⁻¹) x = x :=
      (IntermediateField.mem_fixingSubgroup_iff L _).mp (H.inv_mem v.2) x hx
    rw [AlgEquiv.mul_apply, hv']

end GlobalTheory.InertiaLift
