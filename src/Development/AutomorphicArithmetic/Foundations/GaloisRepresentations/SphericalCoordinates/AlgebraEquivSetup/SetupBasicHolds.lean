import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ExistsClose
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCodiffGen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PFormOKSt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PFormPerfSt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PIdemEx
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugateSqrtNeg
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPerfCof
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PQuadEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRepAdj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRepEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRepLaws
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTraceType
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HenselRoot
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCodiffUnit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.POrient
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRealIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardSubtypeEqOfMultiset
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PDomSt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRealGen

section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pBarEx :
    BarEx := by
  intro E _ _ _
  refine ⟨(IsCMField.ringOfIntegersComplexConj E).toRingEquiv, fun a => ?_⟩
  exact IsCMField.coe_ringOfIntegersComplexConj E a
end

section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pDeltaEx :
    DeltaEx := by
  intro E _ _ _ bar hbar ω tr nm htr hnm hD M hcop t ht hgen hpos τ₀
  obtain ⟨hti, e, he, hez⟩ := hgen
  have hbω : bar ω = (tr : 𝓞 E) - ω := eq_sub_of_add_eq' htr
  have hnm' : ω * ((tr : 𝓞 E) - ω) = (nm : 𝓞 E) := by rw [← hbω]; exact hnm
  set u : 𝓞 E := 2 * ω - (tr : 𝓞 E) with hu
  set D : ℤ := tr ^ 2 - 4 * nm with hDdef
  have huu : u * u = (D : 𝓞 E) := by
    rw [hu, hDdef]; push_cast; linear_combination (-4 : 𝓞 E) * hnm'
  have huuE : (u : E) * (u : E) = (D : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) huu
    simpa using this
  have huE : (u : E) = 2 * (ω : E) - (tr : E) := by
    rw [hu]; norm_cast
  have h1 : (IsCMField.complexConj E) (ω : E) = (tr : E) - ω := by
    rw [← hbar ω, hbω]; norm_cast
  have hconj : (IsCMField.complexConj E) (u : E) = -(u : E) := by
    rw [huE, map_sub, map_mul, h1, map_intCast, map_ofNat]; ring
  have hτu : ∀ τ : E →+* ℂ, (τ u).re = 0 := by
    intro τ
    have h := IsCMField.complexEmbedding_complexConj E τ (u : E)
    rw [hconj, map_neg] at h
    have h2 := congrArg Complex.re h
    simp at h2
    linarith
  have hτt : ∀ τ : E →+* ℂ, (τ t).im = 0 := by
    intro τ
    have h := IsCMField.complexEmbedding_complexConj E τ t
    rw [ht] at h
    have h2 := congrArg Complex.im h
    simp at h2
    linarith
  have hu0 : (τ₀ u).im ≠ 0 := by
    intro h
    have h0 : τ₀ u = 0 := Complex.ext (hτu τ₀) h
    have h3 := congrArg τ₀ huuE
    rw [map_mul, h0, zero_mul, map_intCast] at h3
    have : D = 0 := by exact_mod_cast h3.symm
    linarith
  obtain ⟨c, hc, hcs⟩ : ∃ c : ℤ, c * c = 1 ∧ (c : ℝ) * (τ₀ u).im < 0 := by
    rcases lt_or_gt_of_ne hu0 with h | h
    · exact ⟨1, by norm_num, by simpa using h⟩
    · exact ⟨-1, by norm_num, by simpa using h⟩
  have hcE : (c : E) * (c : E) = 1 := by exact_mod_cast hc
  have hDabs : ((D.natAbs : ℕ) : E) = -((u : E) * (u : E)) := by
    rw [huuE]
    have : ((D.natAbs : ℕ) : ℤ) = -D := Int.ofNat_natAbs_of_nonpos hD.le
    have h2 := congrArg (fun k : ℤ => (k : E)) this
    simpa using h2
  refine ⟨(c : E) * t * u, ?_, ⟨?_, e * D.natAbs, ?_, ?_⟩, ?_⟩
  · rw [map_mul, map_mul, map_intCast, ht, hconj]; ring
  · intro x
    obtain ⟨m, hm⟩ := hti ((c : 𝓞 E) * u * x)
    refine ⟨m, ?_⟩
    have hcast : (((c : 𝓞 E) * u * x : 𝓞 E) : E) = (c : E) * u * x := by norm_cast
    rw [hcast] at hm
    rw [← hm]; congr 1; ring
  · have h2 : Int.gcd D (M : ℤ) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcop
    have h3 : Nat.Coprime D.natAbs M := by
      simpa [Int.gcd, Nat.Coprime] using h2
    exact Nat.Coprime.mul he h3
  · intro z hz
    obtain ⟨x, hx⟩ := hez z hz
    refine ⟨-(c : 𝓞 E) * u * x, ?_⟩
    have hcast : ((-(c : 𝓞 E) * u * x : 𝓞 E) : E) = -(c : E) * u * x := by norm_cast
    rw [hcast]
    push_cast
    linear_combination ((D.natAbs : ℕ) : E) * hx + (t * (x : E)) * hDabs + (t * (u : E) * (u : E) * (x : E)) * hcE
  · intro τ hτ
    have hτu' : τ u = τ₀ u := by
      rw [huE, map_sub, map_mul, map_sub, map_mul, hτ, map_intCast, map_intCast, map_ofNat, map_ofNat]
    rw [map_mul, map_mul, map_intCast, hτu']
    simp only [Complex.mul_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, hτt τ, hτu τ₀]
    nlinarith [mul_neg_of_pos_of_neg (hpos τ) hcs]
end

section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pDiagTrace :
    DiagTrace := by
  intro I _ a M hM
  classical
  have hdec : M = ∑ k, (LinearMap.single ℝ (fun _ : I => ℂ) k) ∘ₗ
      ((Algebra.lmul ℝ ℂ (a k)) ∘ₗ LinearMap.proj k) := by
    refine LinearMap.ext fun z => funext fun j => ?_
    simp [hM, LinearMap.sum_apply, Finset.sum_apply, Pi.single_apply]
  have hk : ∀ k : I, LinearMap.trace ℝ (I → ℂ) ((LinearMap.single ℝ (fun _ : I => ℂ) k) ∘ₗ
      ((Algebra.lmul ℝ ℂ (a k)) ∘ₗ LinearMap.proj k)) = 2 * (a k).re := by
    intro k
    rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc, LinearMap.proj_comp_single_same,
      LinearMap.comp_id, ← Algebra.trace_complex_apply, Algebra.trace_apply]
  rw [hdec, map_sum, Finset.sum_congr rfl (fun k _ => hk k), Complex.re_sum, Finset.mul_sum]
end

section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pHdSign :
    HdSign := by
  intro E _ _ _ A n τ i
  have hcim : ∀ σ : E →+* ℂ, (σ (A.c : E)).im = 0 := by
    intro σ
    have h1 : σ ((A.bar A.c : 𝓞 E) : E) = (starRingEnd ℂ) (σ (A.c : E)) := by
      rw [A.bar_eq, IsCMField.complexEmbedding_complexConj]
    rw [A.c_real] at h1
    exact Complex.conj_eq_iff_im.mp h1.symm
  have hre : InfinitePlace.mk τ = InfinitePlace.mk A.τ₀ → (τ (A.c : E)).re < 0 := by
    intro h
    rcases InfinitePlace.mk_eq_iff.mp h with h' | h'
    · rw [h']
      exact A.c_neg
    · have h2 := A.c_neg
      rw [← h', NumberField.ComplexEmbedding.conjugate_coe_eq] at h2
      simpa using h2
  have hδ : (τ A.δ).re = 0 := by
    have h1 : τ ((IsCMField.complexConj E) A.δ) = (starRingEnd ℂ) (τ A.δ) :=
      IsCMField.complexEmbedding_complexConj E τ A.δ
    rw [A.δ_im, map_neg] at h1
    have h2 := congrArg Complex.re h1
    simp at h2
    linarith
  have hc := hcim τ
  refine ⟨?_, hδ, ?_, ?_⟩
  · simp only [Arith.hd, Arith.dg]
    split_ifs <;> simp [Complex.mul_im, hc]
  · rintro ⟨h, hi0⟩
    have hr := hre h
    simp only [Arith.hd, Arith.dg, if_pos hi0]
    simp
    linarith
  · intro hn
    by_cases hp : InfinitePlace.mk τ = InfinitePlace.mk A.τ₀
    · have hi : (i : ℕ) ≠ 0 := fun hi0 => hn ⟨hp, hi0⟩
      have hr := hre hp
      simp only [Arith.hd, Arith.dg, if_neg hi]
      simp [Complex.mul_re, hc]
      nlinarith
    · have hr : 0 < (τ (A.c : E)).re := A.c_pos τ hp
      simp only [Arith.hd, Arith.dg]
      split_ifs
      · simp
        linarith
      · simp [Complex.mul_re, hc]
        nlinarith
end

section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pLiftEx :
    LiftEx := by
  unfold UpperTheory.Gal.W2.Seed.LiftEx
  intro E _ _ τ₀
  let sA : E →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  letI : Algebra E (AlgebraicClosure ℚ) := sA.toRingHom.toAlgebra
  letI : Algebra E ℂ := τ₀.toAlgebra
  haveI : IsScalarTower ℚ E (AlgebraicClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq (fun x => (sA.commutes x).symm)
  haveI hQ : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : Algebra.IsAlgebraic E (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) E
  let iA : AlgebraicClosure ℚ →ₐ[E] ℂ := IsAlgClosed.lift
  refine ⟨sA.toRingHom, iA.toRingHom, fun x => ?_⟩
  exact iA.commutes x
end

section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pOrbEx :
    OrbEx := by
  intro E _ _ p _ Kq u τ₁ h₁
  classical
  let S := {τ : E →+* PadicAlgCl p // LiesOver Kq u τ}
  let R : Setoid S :=
    { r := fun a b => ∃ σ : Gal(PadicAlgCl p/ℚ_[p]),
        b.1 = ((σ.toRingEquiv : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p).comp a.1
      iseqv := ⟨fun a => ⟨1, by ext x; simp⟩,
        fun {a b} ⟨σ, hσ⟩ => ⟨σ⁻¹, by rw [hσ]; ext x; simp⟩,
        fun {a b c} ⟨σ, hσ⟩ ⟨ρ, hρ⟩ => ⟨ρ * σ, by rw [hρ, hσ]; ext x; simp⟩⟩ }
  haveI : Finite (E →+* PadicAlgCl p) := inferInstance
  haveI : Finite S := Subtype.finite
  haveI : Finite (Quotient R) := Quotient.finite _
  let s₁ : S := ⟨τ₁, h₁⟩
  let rep : Quotient R → S := fun q => if q = Quotient.mk R s₁ then s₁ else q.out
  have hrep : ∀ q, Quotient.mk R (rep q) = q := by
    intro q
    by_cases hq : q = Quotient.mk R s₁
    · simp only [rep, if_pos hq]
      exact hq.symm
    · simp only [rep, if_neg hq]
      exact Quotient.out_eq q
  let eq := Finite.equivFin (Quotient R)
  refine ⟨Nat.card (Quotient R), fun i => (rep (eq.symm i)).1, eq (Quotient.mk R s₁), ?_, ?_, ?_, ?_⟩
  · simp [rep, s₁]
  · intro i
    exact (rep _).2
  · intro i j σ hij
    apply eq.symm.injective
    rw [← hrep (eq.symm i), ← hrep (eq.symm j)]
    exact Quotient.sound ⟨σ, hij.symm⟩
  · intro τ hτ
    obtain ⟨σ, hσ⟩ := Quotient.exact (hrep (Quotient.mk R ⟨τ, hτ⟩))
    exact ⟨eq (Quotient.mk R ⟨τ, hτ⟩), σ, by simpa using hσ⟩
end

section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private theorem exists_trace_rep (E : Type) [Field E] [NumberField E] (f : 𝓞 E →ₗ[ℤ] ℤ) :
    ∃ z : E, ∀ y : 𝓞 E, Algebra.trace ℚ E (z * (y : E)) = ((f y : ℤ) : ℚ) := by
  let g : E →ₗ[ℚ] ℚ := (integralBasis E).constr ℚ (fun i => ((f (RingOfIntegers.basis E i) : ℤ) : ℚ))
  have hg : ∀ y : 𝓞 E, g (y : E) = ((f y : ℤ) : ℚ) := by
    have hext : ((g.restrictScalars ℤ).comp ((Algebra.linearMap (𝓞 E) E).restrictScalars ℤ)) =
        (Algebra.linearMap ℤ ℚ).comp f := by
      refine (RingOfIntegers.basis E).ext fun i => ?_
      simp [g, ← integralBasis_apply]
    intro y
    simpa using LinearMap.congr_fun hext y
  have hnd : (Algebra.traceForm ℚ E).Nondegenerate := traceForm_nondegenerate ℚ E
  refine ⟨(LinearMap.BilinForm.toDual (Algebra.traceForm ℚ E) hnd).symm g, fun y => ?_⟩
  rw [← Algebra.traceForm_apply, ← LinearMap.BilinForm.toDual_def hnd, LinearEquiv.apply_symm_apply]
  exact hg y

theorem UpperTheory.Gal.W2.Seed.pPerfOf :
    PerfOf := by
  intro E _ _ _ A M hgen hc q hq
  obtain ⟨_, e1, he1, hz⟩ := hgen
  obtain ⟨e2, he2, c', hc'⟩ := hc
  refine ⟨e1 * e2, Nat.Coprime.mul (he1.coprime_dvd_right hq) (he2.coprime_dvd_right hq), ?_, ⟨c' * e1, ?_⟩⟩
  · intro f
    obtain ⟨z, hzf⟩ := exists_trace_rep E f
    have hzc : InCodiff z := fun y => ⟨f y, hzf y⟩
    obtain ⟨x, hx⟩ := hz z hzc
    refine ⟨(e2 : 𝓞 E) * x, fun y => ?_⟩
    have h := A.trd_spec ((e2 : 𝓞 E) * x * y)
    have hmul : A.δ * ((((e2 : 𝓞 E) * x * y : 𝓞 E)) : E) = ((e1 * e2 : ℕ) : ℚ) • (z * (y : E)) := by
      rw [Algebra.smul_def, map_natCast]
      push_cast
      linear_combination (-((e2 : E) * (y : E))) * hx
    have hq' : ((A.trd ((e2 : 𝓞 E) * x * y) : ℤ) : ℚ) = (((e1 * e2 : ℕ) : ℤ) : ℚ) * ((f y : ℤ) : ℚ) := by
      rw [h, hmul, map_smul, hzf, smul_eq_mul]
      push_cast; ring
    exact_mod_cast hq'
  · rw [← mul_assoc, hc']
    push_cast
    ring
end

section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pSetupBasic :
    SetupBasic := by
  intro E _ _ _ A n p _ S
  have key : ∀ v : InfinitePlace E, sigPosH (S.G.gram_herm v) = 1 ↔ v = InfinitePlace.mk A.τ₀ := by
    intro v
    show sigPos (A.herm n) v.embedding = 1 ↔ _
    have h := S.sig v.embedding
    rw [InfinitePlace.mk_embedding] at h
    constructor
    · intro h1
      by_contra hne
      have h0 := (h.2 hne).1
      omega
    · intro hv
      exact (h.1 hv).1
  refine ⟨?_, (key _).2 rfl, fun h => ?_⟩
  · exact Fintype.card_eq_one_iff.2 ⟨⟨InfinitePlace.mk A.τ₀, (key _).2 rfl⟩,
      fun w => Subtype.ext ((key w.1).1 w.2)⟩
  · have h2 : 2 * 1 < Module.finrank ℚ E := by simpa using h
    exact ⟨Or.inl h2, Or.inl h2⟩
end

section
noncomputable section

open NumberField

namespace UpperTheory.Gal.W2.Seed

private theorem norm_cast_eq_one {E : Type} [Field E] [NumberField E] (M : ℕ) (b : 𝓞 E) :
    ((Algebra.norm ℤ (1 + (M : 𝓞 E) * b) : ℤ) : ZMod M) = 1 := by
  classical
  let bs := Module.Free.chooseBasis ℤ (𝓞 E)
  rw [Algebra.norm_eq_matrix_det bs, ← eq_intCast (Int.castRingHom (ZMod M)), RingHom.map_det]
  simp only [map_add, map_one, map_mul, map_natCast, ZMod.natCast_self, zero_mul, add_zero,
    Matrix.det_one, CharP.cast_eq_zero]

theorem pUnitMod : UnitMod := by
  intro E _ _ M c b _ h
  refine ⟨(Algebra.norm ℤ c).natAbs, ?_, ?_⟩
  · rw [← ZMod.isUnit_iff_coprime]
    have key := norm_cast_eq_one (E := E) M b
    rw [← h] at key
    rcases Int.natAbs_eq (Algebra.norm ℤ c) with hn | hn
    · rw [hn, Int.cast_natCast] at key
      rw [key]
      exact isUnit_one
    · rw [hn, Int.cast_neg, Int.cast_natCast, neg_eq_iff_eq_neg] at key
      rw [key]
      exact isUnit_one.neg
  · have hm := Ideal.absNorm_mem (Ideal.span ({c} : Set (𝓞 E)))
    rw [Ideal.absNorm_span_singleton, Ideal.mem_span_singleton] at hm
    obtain ⟨c', hc'⟩ := hm
    exact ⟨c', hc'.symm⟩

end UpperTheory.Gal.W2.Seed
end
end

section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pFormCoord :
    TraceType → FormCoord := by
  intro hT E _ _ _ A n Θ hΘ x y
  classical
  have hconj : ∀ (τ : E →+* ℂ) (b : 𝓞 E),
      τ ((A.bar b : 𝓞 E) : E) = (starRingEnd ℂ) (τ (b : E)) := fun τ b => by
    rw [A.bar_eq, IsCMField.complexEmbedding_complexConj]
  have hkey : ∀ a b : Fin n → 𝓞 E, ((A.EF n a b : ℤ) : ℝ) =
      ∑ k : Phi A × Fin n, 2 * (k.1.1 A.δ * k.1.1 (A.hd n k.2 : E) * k.1.1 (a k.2 : E) *
        (starRingEnd ℂ) (k.1.1 (b k.2 : E))).re := by
    intro a b
    have h1 : ((A.EF n a b : ℤ) : ℝ) =
        ((Algebra.trace ℚ E (A.δ * ((∑ i, A.hd n i * a i * A.bar (b i) : 𝓞 E) : E)) : ℚ) : ℝ) := by
      rw [← A.trd_spec, A.EF_apply]; norm_cast
    rw [h1, (hT E A).1, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have h2 : ((∑ i, A.hd n i * a i * A.bar (b i) : 𝓞 E) : E) =
        ∑ i, ((A.hd n i : 𝓞 E) : E) * (a i : E) * ((A.bar (b i) : 𝓞 E) : E) := by
      simpa using map_sum (algebraMap (𝓞 E) E) (fun i => A.hd n i * a i * A.bar (b i)) Finset.univ
    rw [h2, map_mul, map_sum, Finset.mul_sum, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_mul, hconj, mul_assoc]
  have hx : ∀ (r : ℝ) (a : Fin n → 𝓞 E) (k : Phi A × Fin n),
      Θ (r ⊗ₜ[ℤ] a) k = (r : ℂ) * k.1.1 (a k.2 : E) := by
    rintro r a ⟨τ, i⟩
    have h : r ⊗ₜ[ℤ] a = r • ((1 : ℝ) ⊗ₜ[ℤ] a) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h, map_smul, Pi.smul_apply, hΘ, Complex.real_smul]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ =>
    simp only [map_add, LinearMap.add_apply, h₁, h₂, Pi.add_apply, mul_add, add_mul, Complex.add_re,
      Finset.sum_add_distrib]
  | tmul r a =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add, h₁, h₂, Pi.add_apply, mul_add, Complex.add_re, Finset.sum_add_distrib]
    | tmul s b =>
      rw [LinearMap.BilinForm.baseChange_tmul, zsmul_eq_mul, hkey, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hx, hx, map_mul, Complex.conj_ofReal]
      have h : k.1.1 A.δ * k.1.1 (A.hd n k.2 : E) * ((r : ℂ) * k.1.1 (a k.2 : E)) *
          ((s : ℂ) * (starRingEnd ℂ) (k.1.1 (b k.2 : E))) =
          ((r * s : ℝ) : ℂ) * (k.1.1 A.δ * k.1.1 (A.hd n k.2 : E) * k.1.1 (a k.2 : E) *
            (starRingEnd ℂ) (k.1.1 (b k.2 : E))) := by
        push_cast; ring
      rw [h, Complex.re_ofReal_mul]; ring
end

section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pKqEx :
    TraceType → KqEx := by
  intro _ E _ _ _ A
  obtain ⟨w, hw⟩ : ∃ w : E, w = (A.ω : E) := ⟨_, rfl⟩
  have h1 : w + IsCMField.complexConj E w = (A.tr : E) := by
    have h := congrArg (fun z : 𝓞 E => (z : E)) A.tr_eq
    simpa [A.bar_eq, hw] using h
  have h2 : w * IsCMField.complexConj E w = (A.nm : E) := by
    have h := congrArg (fun z : 𝓞 E => (z : E)) A.nm_eq
    simpa [A.bar_eq, hw] using h
  have hq : w ^ 2 - (A.tr : E) * w + (A.nm : E) = 0 := by
    linear_combination w * h1 - h2
  have him : ∀ τ : E →+* ℂ, (τ w).im ≠ 0 := by
    intro τ h0
    have hz : (τ w) ^ 2 - (A.tr : ℂ) * τ w + (A.nm : ℂ) = 0 := by
      have h := congrArg τ hq
      simpa using h
    have hr : τ w = (((τ w).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h0])
    obtain ⟨r, hr'⟩ : ∃ r : ℝ, τ w = (r : ℂ) := ⟨_, hr⟩
    rw [hr'] at hz
    have hz' : r ^ 2 - (A.tr : ℝ) * r + (A.nm : ℝ) = 0 := by exact_mod_cast hz
    have hd : ((A.tr : ℝ)) ^ 2 - 4 * (A.nm : ℝ) < 0 := by exact_mod_cast A.disc_neg
    nlinarith [sq_nonneg (2 * r - (A.tr : ℝ))]
  have hint : IsIntegral ℚ w := Algebra.IsIntegral.isIntegral w
  have hdeg : (minpoly ℚ w).natDegree = 2 := by
    have hpd : (Polynomial.X ^ 2 - Polynomial.C (A.tr : ℚ) * Polynomial.X + Polynomial.C (A.nm : ℚ) : Polynomial ℚ).natDegree = 2 := by
      compute_degree!
    have hp0 : (Polynomial.X ^ 2 - Polynomial.C (A.tr : ℚ) * Polynomial.X + Polynomial.C (A.nm : ℚ) : Polynomial ℚ) ≠ 0 := by
      intro h
      rw [h] at hpd
      simp at hpd
    have hroot : Polynomial.aeval w (Polynomial.X ^ 2 - Polynomial.C (A.tr : ℚ) * Polynomial.X + Polynomial.C (A.nm : ℚ) : Polynomial ℚ) = 0 := by
      simpa using hq
    have hle := Polynomial.natDegree_le_of_dvd (minpoly.dvd ℚ w hroot) hp0
    have hpos := minpoly.natDegree_pos hint
    have hne : (minpoly ℚ w).natDegree ≠ 1 := by
      intro h
      obtain ⟨q, hq'⟩ := minpoly.natDegree_eq_one_iff.1 h
      apply him A.τ₀
      rw [← hq']
      simp
    omega
  have hfr : Module.finrank ℚ (IntermediateField.adjoin ℚ {w}) = 2 := by
    rw [IntermediateField.adjoin.finrank hint, hdeg]
  have hmem : w ∈ IntermediateField.adjoin ℚ {w} := IntermediateField.mem_adjoin_simple_self ℚ w
  refine ⟨(IntermediateField.adjoin ℚ {w}).toSubfield, hw ▸ hmem, ⟨?_, fun τ => ⟨w, hmem, him τ⟩⟩, ?_⟩
  · exact hfr
  · intro x hx
    rw [← hw]
    let pb := IntermediateField.adjoin.powerBasis hint
    obtain ⟨f, hf, hfx⟩ := pb.exists_eq_aeval ⟨x, hx⟩
    have hdim : pb.dim = 2 := by
      rw [IntermediateField.adjoin.powerBasis_dim, hdeg]
    have hf1 : f.natDegree ≤ 1 := by omega
    rw [Polynomial.eq_X_add_C_of_natDegree_le_one hf1] at hfx
    refine ⟨f.coeff 0, f.coeff 1, ?_⟩
    have h := congrArg (fun z : IntermediateField.adjoin ℚ {w} => (z : E)) hfx
    simp [pb] at h
    rw [h]
    simp [add_comm]
end

section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private theorem UpperTheory.Gal.W2.Seed.card_signs {n : ℕ} (hn : 1 ≤ n) (r : Fin n → ℝ)
    (h0 : ∀ i : Fin n, (i : ℕ) = 0 → 0 < r i) (h1 : ∀ i : Fin n, (i : ℕ) ≠ 0 → r i < 0) :
    Fintype.card {i // 0 < r i} = 1 ∧ Fintype.card {i // r i < 0} = n - 1 := by
  have hiff : ∀ i : Fin n, r i < 0 ↔ ¬ 0 < r i := by
    intro i
    by_cases hi : (i : ℕ) = 0
    · have hp := h0 i hi
      exact ⟨fun h => by linarith, fun h => absurd hp h⟩
    · have hq := h1 i hi
      exact ⟨fun _ h' => by linarith, fun _ => hq⟩
  have hc1 : Fintype.card {i // 0 < r i} = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨⟨0, hn⟩, h0 _ rfl⟩, fun ⟨j, hj⟩ => ?_⟩
    apply Subtype.ext
    apply Fin.ext
    by_contra hne
    exact absurd hj (not_lt.mpr (le_of_lt (h1 j hne)))
  refine ⟨hc1, ?_⟩
  rw [Fintype.card_congr (Equiv.subtypeEquivRight hiff), Fintype.card_subtype_compl, hc1,
    Fintype.card_fin]

theorem UpperTheory.Gal.W2.Seed.pSigSt :
    HdSign → SigSt := by
  intro hS E _ _ _ A n hn τ
  have hdiag : gramAt (A.H n) τ = diagonal (fun i => ((τ (A.hd n i : E)).re : ℂ)) := by
    ext i j
    simp only [gramAt, Arith.H, transpose_apply, map_apply, diagonal_apply]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl, if_pos rfl, Complex.ext_iff]
      simp [(hS E A n τ i).1]
    · simp [h, Ne.symm h]
  have aux : ∀ (r : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian),
      M = diagonal (fun i => (r i : ℂ)) →
      sigPosH hM = Fintype.card {i // 0 < r i} ∧ sigNegH hM = Fintype.card {i // r i < 0} := by
    rintro r M hM rfl
    exact sigPosH_sigNegH_diagonal n r hM
  obtain ⟨hp, hneg⟩ := aux _ _ (isHermitian_gramAt (A.herm n) τ) hdiag
  refine ⟨fun hτ => ?_, fun hτ => ?_⟩
  · have hcs := card_signs hn _ (fun i hi => (hS E A n τ i).2.2.1 ⟨hτ, hi⟩)
      (fun i hi => (hS E A n τ i).2.2.2 (fun h => hi h.2))
    exact ⟨hp.trans hcs.1, hneg.trans hcs.2⟩
  · have hall : ∀ i : Fin n, (τ (A.hd n i : E)).re < 0 := fun i =>
      (hS E A n τ i).2.2.2 (fun h => hτ h.1)
    refine ⟨hp.trans ?_, hneg.trans ?_⟩
    · rw [Fintype.card_eq_zero_iff]
      exact ⟨fun ⟨i, hi⟩ => absurd hi (not_lt.mpr (le_of_lt (hall i)))⟩
    · rw [Fintype.card_congr (Equiv.subtypeUnivEquiv hall), Fintype.card_fin]
end

section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pAtPEx :
    KqEx → UEx → OrbEx → LiftEx → AtPEx := by
  intro hK hU hO hL E _ _ _ A p _ hs
  obtain ⟨Kq, hω, hKq, hgen⟩ := hK E A
  obtain ⟨s, iotaC, hsC⟩ := hL E A.τ₀
  haveI : CharZero (PadicAlgCl p) := charZero_of_injective_algebraMap (algebraMap ℚ_[p] (PadicAlgCl p)).injective
  haveI hAlg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert (AlgebraicClosure.isAlgebraic ℚ)
    · rfl
    · exact Subsingleton.elim _ _
  let iotaA : AlgebraicClosure ℚ →ₐ[ℚ] PadicAlgCl p := IsAlgClosed.lift
  let iotaP : AlgebraicClosure ℚ →+* PadicAlgCl p := iotaA.toRingHom
  let τ₁ : E →+* PadicAlgCl p := iotaP.comp s
  obtain ⟨u, ρ, hover, hρ⟩ := hU E A p hs Kq hω hgen τ₁
  obtain ⟨m, emb, w, hw, hov, hinj, hall⟩ := hO E p Kq u τ₁ hover
  exact ⟨{ Kq := Kq, hKq := hKq, u := u, m := m, emb := emb, emb_over := hov, emb_inj := hinj, emb_all := hall,
           iotaP := iotaP, iotaC := iotaC, ρp := ρ, ρp_eq := ⟨hω, hρ⟩, s := s, s_C := hsC, w := w,
           s_P := fun x => by rw [hw]; rfl }⟩
end

section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pPosGen :
    CodiffUnit → PosGen := by
  intro hCU E _ _ _ M hM t htc hg
  obtain ⟨hin, e, he, hz⟩ := id hg

  have h1 : InCodiff (1 : E) := by
    intro x
    have hx : IsIntegral ℤ (Algebra.trace ℚ E (x : E)) := Algebra.isIntegral_trace x.2
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx
    exact ⟨m, by rw [one_mul, ← hm]; simp⟩

  obtain ⟨N, hN⟩ := exists_nat_gt (∑ τ : E →+* ℂ, |(τ t).re|)
  have hbound : ∀ τ : E →+* ℂ, |(τ t).re| < N := fun τ =>
    lt_of_le_of_lt (Finset.single_le_sum (f := fun τ : E →+* ℂ => |(τ t).re|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)) hN
  have hin' : InCodiff (t + (M : E) * (N : E)) := by
    intro x
    obtain ⟨a, ha⟩ := hin x
    obtain ⟨b, hb⟩ := h1 x
    refine ⟨a + M * N * b, ?_⟩
    have hs : (t + (M : E) * (N : E)) * (x : E) = t * x + ((M : ℚ) * (N : ℚ)) • (1 * (x : E)) := by
      rw [Algebra.smul_def]; simp; ring
    rw [hs, map_add, map_smul, ha, hb]
    simp
  obtain ⟨x, hx⟩ := hz 1 h1
  have hgen : GenCodiff M (t + (M : E) * (N : E)) := by
    refine hCU E M hM t _ hg hin' ?_
    intro P hP hMP
    have heP : (e : 𝓞 E) ∉ P := by
      intro h
      have hc : ((e.gcdA M : ℤ) : 𝓞 E) * (e : 𝓞 E) + ((e.gcdB M : ℤ) : 𝓞 E) * (M : 𝓞 E) = 1 := by
        have := Nat.gcd_eq_gcd_ab e M
        rw [he.gcd_eq_one] at this
        have h2 : ((e : ℤ) * e.gcdA M + (M : ℤ) * e.gcdB M) = 1 := by
          rw [← this]; simp
        have h3 := congrArg (Int.cast : ℤ → 𝓞 E) h2
        push_cast at h3
        rw [← h3]; ring
      apply hP.ne_top
      rw [Ideal.eq_top_iff_one, ← hc]
      exact P.add_mem (P.mul_mem_left _ h) (P.mul_mem_left _ hMP)
    refine ⟨(e : 𝓞 E), (e : 𝓞 E) + (M : 𝓞 E) * ((N : 𝓞 E) * x), heP, ?_, ?_⟩
    · intro h
      exact heP ((P.add_mem_iff_left (P.mul_mem_right _ hMP)).mp h)
    · have hx' : (e : E) = t * x := by simpa using hx
      push_cast
      linear_combination ((M : E) * (N : E)) * hx'
  refine ⟨t + (M : E) * (N : E), ?_, hgen, ?_⟩
  · simp [htc]
  · intro τ
    have hb := abs_lt.mp (hbound τ)
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hre : (τ (t + (M : E) * (N : E))).re = (τ t).re + (M : ℝ) * (N : ℝ) := by
      simp
    rw [hre]
    nlinarith [hb.1]
end

section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed

private noncomputable def repOf {E V : Type} [Field E] [Algebra ℚ E] [AddCommGroup V] [Module ℚ V] {n : ℕ}
    (β : V ≃ₗ[ℚ] (Fin n → E)) : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ V :=
  AlgHom.ofLinearMap
    { toFun := fun x => β.symm.toLinearMap ∘ₗ (x.mulVecLin.restrictScalars ℚ) ∘ₗ β.toLinearMap
      map_add' := fun x y => by
        ext v
        simp [Matrix.add_mulVec]
      map_smul' := fun c x => by
        ext v
        simp [Matrix.smul_mulVec] }
    (by ext v; simp)
    (fun x y => by ext v; simp [Matrix.mulVec_mulVec])

private theorem repOf_apply {E V : Type} [Field E] [Algebra ℚ E] [AddCommGroup V] [Module ℚ V] {n : ℕ}
    (β : V ≃ₗ[ℚ] (Fin n → E)) (x : Matrix (Fin n) (Fin n) E) (z : V) : β (repOf β x z) = x *ᵥ β z := by
  simp [repOf]

end UpperTheory.Gal.W2.Seed

theorem UpperTheory.Gal.W2.Seed.pSetupEx :
    FormOKSt → FormPerfSt → SigSt → DomSt → AtPEx → RepEx → RepLaws → RepAdj → Orient → SetupEx := by
  intro hF hFP hS hD hP hR hL hA hO E _ _ _ A n p _ hn hg
  have facts : A.Facts n := ⟨hn, hF E A n, hD E A n hn⟩
  have hs : A.SigOK n := hS E A n hn
  have perf : A.FormPerf n p := hFP E A n p hg.2
  obtain ⟨P⟩ := hP E A p hg.1
  obtain ⟨β, hβ⟩ := hR E n
  have hok : RepOK A n (repOf β) := ⟨β, hβ, repOf_apply β⟩
  obtain ⟨r1, r2, r3, r4⟩ := hL E A n (repOf β) hok
  have radj := hA E A n (repOf β) hok
  obtain ⟨J, j1, j2, j3, j4⟩ := hO E A n hn hs p P (repOf β) hok
  have hsig : ∀ v : InfinitePlace E, sigPos (A.herm n) v.embedding = 1 ↔
      ∃ _ : Fin 1, v = InfinitePlace.mk (P.iotaC.comp P.s) := fun v => by
    have hv := hs v.embedding
    rw [InfinitePlace.mk_embedding] at hv
    have hc : P.iotaC.comp P.s = A.τ₀ := RingHom.ext P.s_C
    rw [hc]
    constructor
    · intro h
      by_cases hv0 : v = InfinitePlace.mk A.τ₀
      · exact ⟨0, hv0⟩
      · have h0 := (hv.2 hv0).1
        omega
    · rintro ⟨_, h⟩
      exact (hv.1 h).1
  refine ⟨⟨facts, hs, hg, perf, P, ?_, ?_, ?_⟩⟩
  · exact
      { e := RingEquiv.refl E
        n_eq := rfl
        rep := repOf β
        rep_inj := r1
        rep_range := r2
        rep_F := fun c => r3 c
        adj := radj
        ρp := P.ρp
        ρp_eq := P.ρp_eq
        s := fun _ => P.s
        s_C := fun _ x => P.s_C x
        w := fun _ => P.w
        s_P := fun _ x => P.s_P x
        sig := hsig
        orient := ⟨J, j1, j2, j3, j4⟩ }
  · intro x; rfl
  · exact r4
end

section
namespace UpperTheory.Gal.W2.Seed

theorem BarEx_holds : BarEx := pBarEx
theorem CEx_holds : CEx := pCEx
theorem CodiffGen_holds : CodiffGen := pCodiffGen
theorem DeltaEx_holds : DeltaEx := pDeltaEx
theorem DiagTrace_holds : DiagTrace := pDiagTrace
theorem FormOKSt_holds : FormOKSt := pFormOKSt
theorem FormPerfSt_holds : FormPerfSt := pFormPerfSt
theorem HdSign_holds : HdSign := pHdSign
theorem IdemEx_holds : IdemEx := pIdemEx
theorem LiftEx_holds : LiftEx := pLiftEx
theorem OrbEx_holds : OrbEx := pOrbEx
theorem PerfCof_holds : PerfCof := pPerfCof
theorem PerfOf_holds : PerfOf := pPerfOf
theorem QuadEx_holds : QuadEx := pQuadEx
theorem RepAdj_holds : RepAdj := pRepAdj
theorem RepEx_holds : RepEx := pRepEx
theorem RepLaws_holds : RepLaws := pRepLaws
theorem SetupBasic_holds : SetupBasic := pSetupBasic
theorem TraceType_holds : TraceType := pTraceType
theorem UEx_holds : UEx := pUEx
theorem UnitMod_holds : UnitMod := pUnitMod
theorem CodiffUnit_holds : CodiffUnit := pCodiffUnit UnitMod_holds
theorem FormCoord_holds : FormCoord := pFormCoord TraceType_holds
theorem KqEx_holds : KqEx := pKqEx TraceType_holds
theorem Orient_holds : Orient := pOrient TraceType_holds HdSign_holds
theorem RealIso_holds : RealIso := pRealIso TraceType_holds
theorem SigSt_holds : SigSt := pSigSt HdSign_holds
theorem AtPEx_holds : AtPEx := pAtPEx KqEx_holds UEx_holds OrbEx_holds LiftEx_holds
theorem DomSt_holds : DomSt := pDomSt TraceType_holds RealIso_holds FormCoord_holds HdSign_holds DiagTrace_holds
theorem PosGen_holds : PosGen := pPosGen CodiffUnit_holds
theorem RealGen_holds : RealGen := pRealGen CodiffGen_holds CodiffUnit_holds
theorem SetupEx_holds : SetupEx := pSetupEx FormOKSt_holds FormPerfSt_holds SigSt_holds DomSt_holds AtPEx_holds RepEx_holds RepLaws_holds RepAdj_holds Orient_holds

end UpperTheory.Gal.W2.Seed
end
