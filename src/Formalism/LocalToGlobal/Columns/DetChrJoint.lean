import Mathlib
import Formalism.LocalToGlobal.Columns.RecChainUnfOne
import Formalism.LocalToGlobal.Columns.ColumnsProofs.ChainCounts
import Formalism.LocalToGlobal.Columns.HeckeEx
import Formalism.LocalToGlobal.Columns.CyclotomicIsCyclotomicExtension
import Formalism.LocalToGlobal.Columns.ChainInstY
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PenultimateKernelDiamondInvariant

section
open NumberField IsDedekindDomain Module
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Loc

variable {X : Fields} {Pr : Primes X} {R : Ranks}

structure DetChr.Loc (Dc : DetChr X R.m) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (σ : X.E →ₐ[X.F] X.E) : Prop where
  trivF : ∀ i, i < R.m → (Formalism.L2.DIV.h90 σ).ker ≤ (Dc.muAt i * (mu : Chr X.F X.E X.K)).ker
  unr : ∀ i, i < R.m → ∀ y ∈ intU X.F X.E,
    (∀ P ∈ rowSG Pr sel mu, ∀ v : HeightOneSpectrum (𝓞 X.F), P.asIdeal.under (𝓞 X.F) = v.asIdeal → Units.map (Formalism.UG.prV (E := X.E) v).toMonoidHom y = 1) →
    (Dc.muAt i * (mu : Chr X.F X.E X.K)) y = 1
  unif : ∀ i, i < R.m → ∀ P : HeightOneSpectrum (𝓞 X.E),
    (¬ ∃ P' ∈ rowSG Pr sel mu, P'.asIdeal.under (𝓞 X.F) = P.asIdeal.under (𝓞 X.F)) →
    IsUnifVal (Dc.muAt i * (mu : Chr X.F X.E X.K)) P (mUof Ch mu i P)⁻¹
  tame : ∀ i, i < R.m → ∀ P ∈ rowSG Pr sel mu, ∀ v : HeightOneSpectrum (𝓞 X.F), P.asIdeal.under (𝓞 X.F) = v.asIdeal →
    wildAt X.E v ≤ (Dc.muAt i * (mu : Chr X.F X.E X.K)).ker
  res : ∀ i, i < R.m → ∀ P : rowSG Pr sel mu,
    IsResChar (Dc.muAt i * (mu : Chr X.F X.E X.K)) P.1
      (open Classical in if P.1 ∈ Pr.vGs then (chiP Ch P.1 i)⁻¹ else resChar (mu : Chr X.F X.E X.K) P.1)
  atq : ∀ i, i < R.m → ∀ (P : rowSG Pr sel mu) (k : X.Kˣ), IsQValC (Dc.muAt i * (mu : Chr X.F X.E X.K)) P.1 k →
    cst.muq (i + 1) P = ((k⁻¹ : X.Kˣ) : X.K)
  atq_ex : ∀ i, i < R.m → ∀ P : rowSG Pr sel mu, ∃ k : X.Kˣ, IsQValC (Dc.muAt i * (mu : Chr X.F X.E X.K)) P.1 k
  trivChi : (Formalism.L2.DIV.h90 σ).ker ≤ Dc.chi.ker
  unrChi : ∀ y ∈ intU X.F X.E, Dc.chi y = 1

def PtSurjAll (hc : Formalism.BasicNotions.CMData X.F X.E) (Pr : Primes X) (R : Ranks) (u : Pr.Word) : Prop :=
  ∀ n, n ≤ R.m → ∀ p : DecoSet X.E (R.N n) (Pr.vT u) Pr.vGs,
    letI : NeZero (R.N n) := ⟨(R.N_pos n).ne'⟩
    decoOf (Pr.vT u) Pr.vGs (ptOf hc (R.N n) (Pr.vT u) Pr.vGs p : GL (Fin (R.N n)) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) = p

def MuDetOfLoc : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (cst : LocCst X (rowSG Pr sel (mu0 X.F X.E X.K S))) (Dc : DetChr X R.m) (hc : Formalism.BasicNotions.CMData X.F X.E) (u : Pr.Word),
    X.Ok → Pr.Ok → (∀ v, (sel v).asIdeal.under (𝓞 X.F) = v.asIdeal) → Dc.Loc Ch sel (mu0 X.F X.E X.K S) cst hc.sig → PtSurjAll hc Pr R u →
    ∀ i, i < R.m → ∀ n, (n = i ∨ n = i + 1) → ∀ p : DecoSet X.E (R.N n) (Pr.vT u) Pr.vGs,
      letI : NeZero (R.N n) := ⟨(R.N_pos n).ne'⟩
      (((Formalism.L2.DIV.detTw hc.sig (Dc.muAt i)
          (ptOf hc (R.N n) (Pr.vT u) Pr.vGs p : GL (Fin (R.N n)) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)))⁻¹ : X.Kˣ) : X.K) =
        muInvDet sel (rowSG Pr sel (mu0 X.F X.E X.K S)) (mUof Ch (mu0 X.F X.E X.K S) i) (muAt Ch sel (mu0 X.F X.E X.K S) cst i) p.1.N
          (frsD sel (mu0 X.F X.E X.K S) p)

end Loc

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

namespace DetChrL

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker

section Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IntAtI (P : HeightOneSpectrum (𝓞 E)) (y : AfE F E) : Prop :=
  ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ Formalism.UG.inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E s) * y ∈ RInt F E

def UnitAtI (P : HeightOneSpectrum (𝓞 E)) (y : (AfE F E)ˣ) : Prop := IntAtI P (y : AfE F E) ∧ IntAtI P ((y⁻¹ : (AfE F E)ˣ) : AfE F E)

def CongOneAtI (P : HeightOneSpectrum (𝓞 E)) (y : AfE F E) : Prop :=
  ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ z ∈ P.asIdeal.map (toRInt F E),
    Formalism.UG.inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E s) * (y - 1) = (z : AfE F E)

end Defs

def HilbertNinetyDeterminant : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n]
    (g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)), g ∈ UAd hc n →
      ∃ x : (AfE F E)ˣ, h90 hc.sig x = Matrix.GeneralLinearGroup.det g

def DetAtP : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n]
    (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)), g ∈ UAd hc n →
      (∀ P : HeightOneSpectrum (𝓞 E), ∃ f : Sp E n ≃ₗ[E] Sp E n, ∀ z, f z ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (decoOf ST SG g).1.N ↔ z ∈ stdAt E n P) ∧
      (∀ (P : HeightOneSpectrum (𝓞 E)) (f : Sp E n ≃ₗ[E] Sp E n),
        (∀ z, f z ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (decoOf ST SG g).1.N ↔ z ∈ stdAt E n P) →
        UnitAtI P (Matrix.GeneralLinearGroup.det g * (ratId F E (LinearEquiv.det f))⁻¹)) ∧
      ∀ w : SG, CongOneAtI w.1
        ((Matrix.GeneralLinearGroup.det g * (ratId F E (LinearEquiv.det ((decoOf ST SG g).1.liftFr w)))⁻¹ : (AfE F E)ˣ) : AfE F E)

def CharFactor : Prop :=
  ∀ (F E L : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field L]
    (hc : CMData F E) (ξ : Chr F E L) (S : Finset (HeightOneSpectrum (𝓞 E))) (sel : HeightOneSpectrum (𝓞 F) → HeightOneSpectrum (𝓞 E))
    (c : HeightOneSpectrum (𝓞 E) → Lˣ) (χ : ∀ P : HeightOneSpectrum (𝓞 E), (𝓞 E ⧸ P.asIdeal)ˣ →* Lˣ)
    (k : HeightOneSpectrum (𝓞 E) → Lˣ) (a : HeightOneSpectrum (𝓞 E) → Eˣ) (x : (AfE F E)ˣ),
    (∀ v, (sel v).asIdeal.under (𝓞 F) = v.asIdeal) →
    (∀ P ∈ S, ∃ P' : HeightOneSpectrum (𝓞 E), P' ≠ P ∧ P'.asIdeal.under (𝓞 F) = P.asIdeal.under (𝓞 F) ∧ P' ∉ S) →
    (∀ P ∈ S, ChainCounts.UnifAt P) →
    (h90 hc.sig).ker ≤ ξ.ker →
    (∀ y ∈ intU F E, (∀ P ∈ S, ∀ v : HeightOneSpectrum (𝓞 F), P.asIdeal.under (𝓞 F) = v.asIdeal →
      Units.map (Formalism.UG.prV (E := E) v).toMonoidHom y = 1) → ξ y = 1) →
    (∀ P : HeightOneSpectrum (𝓞 E), (¬ ∃ P' ∈ S, P'.asIdeal.under (𝓞 F) = P.asIdeal.under (𝓞 F)) → IsUnifVal ξ P (c P)) →
    (∀ P ∈ S, ∀ v : HeightOneSpectrum (𝓞 F), P.asIdeal.under (𝓞 F) = v.asIdeal → wildAt E v ≤ ξ.ker) →
    (∀ P ∈ S, IsResChar ξ P (χ P)) →
    (∀ P ∈ S, IsQValC ξ P (k P)) →
    {P : HeightOneSpectrum (𝓞 E) | ordE P (a P : E) ≠ 0}.Finite →
    (∀ P : HeightOneSpectrum (𝓞 E), UnitAtI P (h90 hc.sig x * (ratId F E (a P))⁻¹)) →
    (∀ P ∈ S, CongOneAtI P ((h90 hc.sig x * (ratId F E (a P))⁻¹ : (AfE F E)ˣ) : AfE F E)) →
    (((ξ x)⁻¹ : Lˣ) : L) =
      (∏ᶠ v : HeightOneSpectrum (𝓞 F),
        open Classical in
        if ∃ P ∈ S, P.asIdeal.under (𝓞 F) = v.asIdeal then (1 : L) else (((c (sel v))⁻¹ ^ ordE (sel v) (a (sel v) : E) : Lˣ) : L)) *
      ∏ P ∈ S, LocE.locChar (qOf P) (((k P)⁻¹ : Lˣ) : L) (χ P)⁻¹ (a P : E)

end DetChrL

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

namespace HeckeExHost

open Formalism.L2.Host Formalism.L2.Host.CharEx Formalism.L2.Col.HeckeEx Formalism.L2.DIV
open scoped Pointwise

section Gen

variable {X : Fields}

theorem unram_of (hX : X.AbelianUnramifiedExtensionConditions) (P : HeightOneSpectrum (𝓞 X.E)) : P.asIdeal.ramificationIdx (𝓞 X.F) = 1 := by
  have hne : P.asIdeal.under (𝓞 X.F) ≠ ⊥ := (P.under (𝓞 X.F)).ne_bot
  have := P.isPrime
  have : P.asIdeal.LiesOver (P.asIdeal.under (𝓞 X.F)) := ⟨rfl⟩
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (P.asIdeal.under (𝓞 X.F)) P.asIdeal hne]
  apply Ideal.ramificationIdx'_spec
  · rw [pow_one]
    exact Ideal.map_comap_le
  · exact hX.unram P

theorem algebraMap_ne_imaginary (hX : X.Ok) {s0 : X.E} (hne : s0 ≠ 0) (hc : star s0 = -s0) (a : X.F) : algebraMap X.F X.E a ≠ s0 := by
  intro h
  have h1 := hX.star_F a
  rw [h, hc] at h1
  apply hne
  have h2 : s0 + s0 = 0 := by
    nth_rewrite 1 [← h1]
    exact neg_add_cancel s0
  exact add_self_eq_zero.mp h2

theorem li_pair (hX : X.Ok) {s0 : X.E} (hne : s0 ≠ 0) (hc : star s0 = -s0) : LinearIndependent X.F ![(1 : X.E), s0] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have ht : t = 0 := by
    by_contra ht
    apply algebraMap_ne_imaginary hX hne hc (-s / t)
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    have htE : algebraMap X.F X.E t ≠ 0 := (map_ne_zero _).mpr ht
    rw [map_div₀, map_neg, div_eq_iff htE]
    linear_combination -hst
  subst ht
  refine ⟨?_, rfl⟩
  rw [zero_smul, add_zero, Algebra.smul_def, mul_one] at hst
  exact (map_eq_zero (algebraMap X.F X.E)).mp hst

theorem exists_pair (hX : X.Ok) {s0 : X.E} (hne : s0 ≠ 0) (hc : star s0 = -s0) (x : X.E) :
    ∃ a b : X.F, x = algebraMap X.F X.E a + algebraMap X.F X.E b * s0 := by
  have hli := li_pair hX hne hc
  have hcard : Fintype.card (Fin 2) = Module.finrank X.F X.E := by rw [hX.rankE]; rfl
  set b := basisOfLinearIndependentOfCardEqFinrank hli hcard with hb
  refine ⟨b.repr x 0, b.repr x 1, ?_⟩
  conv_lhs => rw [← b.sum_repr x]
  simp [hb, Fin.sum_univ_two, Algebra.smul_def]

theorem fixF_of (hX : X.Ok) {s0 : X.E} (hne : s0 ≠ 0) (hc : star s0 = -s0) (x : X.E) (hx : star x = x) :
    ∃ a : X.F, algebraMap X.F X.E a = x := by
  obtain ⟨a, b, rfl⟩ := exists_pair hX hne hc x
  refine ⟨a, ?_⟩
  have hb : algebraMap X.F X.E b * s0 = 0 := by
    rw [star_add, star_mul, hX.star_F, hX.star_F, hc] at hx
    have h2 : (2 : X.E) * (algebraMap X.F X.E b * s0) = 0 := by linear_combination -hx
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h two_ne_zero
    · exact h
  rcases mul_eq_zero.mp hb with h | h
  · rw [h, zero_mul, add_zero]
  · exact absurd h hne

theorem conj_alg (hX : X.Ok) (φ : X.E →+* ℂ) (a : X.F) :
    starRingEnd ℂ (φ (algebraMap X.F X.E a)) = φ (algebraMap X.F X.E a) := by
  rw [← hX.conjE, hX.star_F]

open Classical in

theorem onePsi_of (hX : X.Ok) (σ₀ : X.K →+* ℂ) {s0 : X.E} (hne : s0 ≠ 0) (hc : star s0 = -s0)
    (hpos : ∀ i, ∃ r : ℝ, 0 < r ∧ X.embC σ₀ i s0 = Complex.I * r) (w : InfinitePlace X.F) :
    (Finset.univ.filter (fun i => InfinitePlace.mk (X.embC σ₀ i) ∈ aboveInf (L := X.E) X.F w)).card = 1 := by

  have hinj : Function.Injective (X.embC σ₀) := by
    intro τ τ' h
    apply hX.emb_inj
    ext x
    exact σ₀.injective (RingHom.congr_fun h x)
  let Φ : X.Tau ⊕ X.Tau → (X.E →+* ℂ) := Sum.elim (X.embC σ₀) fun τ => (starRingEnd ℂ).comp (X.embC σ₀ τ)
  have hΦ : Function.Injective Φ := by
    have hcs : ∀ τ τ', X.embC σ₀ τ ≠ (starRingEnd ℂ).comp (X.embC σ₀ τ') := by
      intro τ τ' h
      obtain ⟨r, hr, h1⟩ := hpos τ
      obtain ⟨r', hr', h2⟩ := hpos τ'
      have h3 := RingHom.congr_fun h s0
      rw [RingHom.comp_apply, h1, h2, map_mul, Complex.conj_I, Complex.conj_ofReal] at h3
      have h4 := congrArg Complex.im h3
      simp at h4
      linarith
    rintro (τ | τ) (τ' | τ') h
    · exact congrArg Sum.inl (hinj h)
    · exact absurd h (hcs τ τ')
    · exact absurd h.symm (hcs τ' τ)
    · congr 1
      apply hinj
      ext x
      have := RingHom.congr_fun h x
      simp only [Φ, Sum.elim_inr, RingHom.comp_apply] at this
      exact (starRingEnd ℂ).injective this
  have hcardE : Fintype.card (X.E →+* ℂ) = 2 * Fintype.card X.Tau := by
    rw [Embeddings.card, ← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, hX.card_Tau, mul_comm]
  have hsurj : Function.Surjective Φ := by
    have hc2 : Fintype.card (X.Tau ⊕ X.Tau) = Fintype.card (X.E →+* ℂ) := by
      rw [Fintype.card_sum, hcardE]; ring
    exact ((Fintype.bijective_iff_injective_and_card Φ).2 ⟨hΦ, hc2⟩).2

  have hs2 : ∃ a : X.F, algebraMap X.F X.E a = s0 ^ 2 := fixF_of hX hne hc _ (by rw [star_pow, hc]; ring)
  have huniq : ∀ i τ, (InfinitePlace.mk (X.embC σ₀ i)).comap (algebraMap X.F X.E) =
      (InfinitePlace.mk (X.embC σ₀ τ)).comap (algebraMap X.F X.E) → i = τ := by
    intro i τ h
    have hagree : ∀ a : X.F, X.embC σ₀ i (algebraMap X.F X.E a) = X.embC σ₀ τ (algebraMap X.F X.E a) := by
      rw [InfinitePlace.comap_mk, InfinitePlace.comap_mk, InfinitePlace.mk_eq_iff] at h
      intro a
      rcases h with h | h
      · exact RingHom.congr_fun h a
      · have h1 := RingHom.congr_fun h a
        rw [ComplexEmbedding.conjugate_coe_eq] at h1
        change starRingEnd ℂ (X.embC σ₀ i (algebraMap X.F X.E a)) = _ at h1
        rw [conj_alg hX] at h1
        exact h1
    obtain ⟨r, hr, h1⟩ := hpos i
    obtain ⟨r', hr', h2⟩ := hpos τ
    obtain ⟨a2, ha2⟩ := hs2
    have hrr : r = r' := by
      have h3 := hagree a2
      rw [ha2, map_pow, map_pow, h1, h2] at h3
      have h4 : ((r : ℂ) ^ 2) = (r' : ℂ) ^ 2 := by
        have : (Complex.I * r) ^ 2 = -(r : ℂ) ^ 2 := by rw [mul_pow, Complex.I_sq]; ring
        have h' : (Complex.I * r') ^ 2 = -(r' : ℂ) ^ 2 := by rw [mul_pow, Complex.I_sq]; ring
        rw [this, h'] at h3
        linear_combination -h3
      have h5 : r ^ 2 = r' ^ 2 := by exact_mod_cast h4
      nlinarith [sq_nonneg (r - r'), sq_nonneg (r + r')]
    apply hinj
    ext x
    obtain ⟨a, b, rfl⟩ := exists_pair hX hne hc x
    rw [map_add, map_add, map_mul, map_mul, hagree a, hagree b, h1, h2, hrr]

  have : Algebra.IsAlgebraic X.F X.E := inferInstance
  obtain ⟨w', hw'⟩ := InfinitePlace.comap_surjective (k := X.F) (K := X.E) w
  obtain ⟨τ, hτ⟩ : ∃ τ, InfinitePlace.mk (X.embC σ₀ τ) = w' := by
    obtain ⟨t, ht⟩ := hsurj w'.embedding
    rcases t with τ | τ
    · exact ⟨τ, by rw [show X.embC σ₀ τ = w'.embedding from ht, InfinitePlace.mk_embedding]⟩
    · refine ⟨τ, ?_⟩
      have : (starRingEnd ℂ).comp (X.embC σ₀ τ) = w'.embedding := ht
      have h2 : (starRingEnd ℂ).comp (X.embC σ₀ τ) = ComplexEmbedding.conjugate (X.embC σ₀ τ) := by ext x; rfl
      rw [← InfinitePlace.mk_conjugate_eq, ← h2, this, InfinitePlace.mk_embedding]
  rw [Finset.card_eq_one]
  refine ⟨τ, Finset.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, aboveInf]
    rw [hτ]
    exact hw'
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, aboveInf] at hi
    exact huniq i τ (by rw [hi, hτ]; exact hw'.symm)

theorem conjO_conjO' (x : 𝓞 X.E) : X.conjO (X.conjO x) = x := by
  apply RingOfIntegers.ext
  show starRingEnd X.E (starRingEnd X.E (x : X.E)) = (x : X.E)
  simp

def conjPrime₂ (P : HeightOneSpectrum (𝓞 X.E)) : HeightOneSpectrum (𝓞 X.E) where
  asIdeal := P.asIdeal.comap X.conjO
  isPrime := Ideal.IsPrime.comap _
  ne_bot := by
    intro h
    apply P.ne_bot
    rw [eq_bot_iff]
    intro x hx
    have : X.conjO x ∈ P.asIdeal.comap X.conjO := by
      rw [Ideal.mem_comap, conjO_conjO']
      exact hx
    rw [h, Ideal.mem_bot] at this
    rw [Ideal.mem_bot]
    have := congrArg X.conjO this
    rwa [conjO_conjO', map_zero] at this

theorem conjO_alg (hX : X.Ok) (a : 𝓞 X.F) : X.conjO (algebraMap (𝓞 X.F) (𝓞 X.E) a) = algebraMap (𝓞 X.F) (𝓞 X.E) a := by
  apply RingOfIntegers.ext
  show starRingEnd X.E (algebraMap (𝓞 X.E) X.E (algebraMap (𝓞 X.F) (𝓞 X.E) a)) =
    algebraMap (𝓞 X.E) X.E (algebraMap (𝓞 X.F) (𝓞 X.E) a)
  rw [starRingEnd_apply, ← IsScalarTower.algebraMap_apply (𝓞 X.F) (𝓞 X.E) X.E,
    IsScalarTower.algebraMap_apply (𝓞 X.F) X.F X.E]
  exact hX.star_F _

theorem conjP_under (hX : X.Ok) (P : HeightOneSpectrum (𝓞 X.E)) : (conjPrime₂ P).under (𝓞 X.F) = P.under (𝓞 X.F) := by
  have key : (P.asIdeal.comap X.conjO).comap (algebraMap (𝓞 X.F) (𝓞 X.E)) =
      P.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) := by
    rw [Ideal.comap_comap, show X.conjO.comp (algebraMap (𝓞 X.F) (𝓞 X.E)) = algebraMap (𝓞 X.F) (𝓞 X.E) from
      RingHom.ext fun a => conjO_alg hX a]
  ext1
  exact key



end Gen

section Host

variable {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R) (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL]
  (hE : H.EQ ≤ LL)

open Classical in

def sqrtH : (hostFields H.toHostRaw ι LL hE).E :=
  if ∃ τ, 0 < ((hostFields H.toHostRaw ι LL hE).embC (sig0 ι LL) τ (hwE H.toHostRaw ι LL hE)).im
  then hwE H.toHostRaw ι LL hE else -hwE H.toHostRaw ι LL hE

open Classical in

def sqrtHO : 𝓞 (hostFields H.toHostRaw ι LL hE).E :=
  if ∃ τ, 0 < ((hostFields H.toHostRaw ι LL hE).embC (sig0 ι LL) τ (hwE H.toHostRaw ι LL hE)).im
  then hwO H.toHostRaw ι LL hE else -hwO H.toHostRaw ι LL hE






def toX (y : H.EQ) : (hostFields H.toHostRaw ι LL hE).E := y

theorem frame_conj (T : Frame H) (x : H.E) :
    toX H ι LL hE (T.iso (H.conj x)) = star (toX H ι LL hE (T.iso x)) := by
  let φ : (hostFields H.toHostRaw ι LL hE).E →+* ℂ :=
    (T.ι.comp T.j.toRingHom).comp (T.iso.symm : H.EQ ≃ₐ[ℚ] H.E).toRingEquiv.toRingHom
  have hφ : ∀ y : H.E, φ (toX H ι LL hE (T.iso y)) = T.ι (T.j y) := by
    intro y
    show T.ι (T.j (T.iso.symm (T.iso y))) = _
    rw [AlgEquiv.symm_apply_apply]
  apply φ.injective
  rw [(hostFields_ok H ι LL hE).conjE φ, hφ, hφ, T.conj]





end Host

end HeckeExHost

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

namespace DetChrL

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker

section Joint

open Classical

variable {X : Fields} {Pr : Primes X}

theorem trivialTuple_coe (S : Set ℕ) : ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K) = 1 := rfl

theorem twistPrimes_trivialTuple_empty (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) :
    QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K) = ∅ := by
  unfold QE Qprime
  split_ifs with h
  · rw [Finset.image_eq_empty, Set.Finite.toFinset_eq_empty]
    ext v
    simp [trivialTuple_coe]
  · rfl

theorem conjP_vGs (hX : X.Ok) (hPr : Pr.Ok) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs) :
    HeckeExHost.conjPrime₂ P ≠ P ∧ HeckeExHost.conjPrime₂ P ∉ Pr.vGs := by
  have hmem : ∀ j, P ∈ Pr.vG j → X.conjO (Pr.piG j) ∈ P.asIdeal := fun j h => ChainCounts.mem_of_mem_divs h
  have hcomap : ∀ y : 𝓞 X.E, y ∈ (HeckeExHost.conjPrime₂ P).asIdeal ↔ X.conjO y ∈ P.asIdeal := fun y => Iff.rfl
  have hcop : ∀ j, Pr.piG j ∈ P.asIdeal → X.conjO (Pr.piG j) ∈ P.asIdeal → False := by
    intro j h1 h2
    obtain ⟨a, b, hab⟩ := hPr.piG_cop j
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)
  obtain ⟨i, hi⟩ : ∃ i, P ∈ Pr.vG i := by
    rcases Finset.mem_union.1 hP with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 : Pr.piG i ∈ (HeckeExHost.conjPrime₂ P).asIdeal := (hcomap _).2 (hmem i hi)
    rw [h] at h1
    exact hcop i h1 (hmem i hi)
  · obtain ⟨j, hj⟩ : ∃ j, HeckeExHost.conjPrime₂ P ∈ Pr.vG j := by
      rcases Finset.mem_union.1 h with h' | h'
      · exact ⟨0, h'⟩
      · exact ⟨1, h'⟩
    have h1 : Pr.piG j ∈ P.asIdeal := by
      have := (hcomap _).1 (ChainCounts.mem_of_mem_divs hj)
      rwa [HeckeExHost.conjO_conjO'] at this
    by_cases hij : j = i
    · subst hij
      exact hcop j h1 (hmem j hi)
    · have hg1 : ((Pr.g j : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
        rw [← hPr.piG_norm j]
        exact Ideal.mul_mem_right _ _ h1
      have hg2 : ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
        rw [← hPr.piG_norm i]
        exact Ideal.mul_mem_left _ _ (hmem i hi)
      have hne : Pr.g j ≠ Pr.g i := by
        have key : ∀ a b : Fin 2, a ≠ b → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by decide
        rcases key j i hij with ⟨h0, h1'⟩ | ⟨h0, h1'⟩
        · rw [h0, h1']; exact hPr.g_ne
        · rw [h0, h1']; exact hPr.g_ne.symm
      have hcopZ : Nat.Coprime (Pr.g j) (Pr.g i) := (Nat.coprime_primes (hPr.g_prime j) (hPr.g_prime i)).2 hne
      obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * (Pr.g j : ℤ) + b * (Pr.g i : ℤ) = 1 := by
        refine ⟨Nat.gcdA (Pr.g j) (Pr.g i), Nat.gcdB (Pr.g j) (Pr.g i), ?_⟩
        have := Nat.gcd_eq_gcd_ab (Pr.g j) (Pr.g i)
        rw [hcopZ] at this
        push_cast at this
        linarith
      apply P.isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have e : (1 : 𝓞 X.E) = (a : 𝓞 X.E) * ((Pr.g j : ℕ) : 𝓞 X.E) + (b : 𝓞 X.E) * ((Pr.g i : ℕ) : 𝓞 X.E) := by
        have := congrArg (fun z : ℤ => (z : 𝓞 X.E)) hab
        push_cast at this
        exact this.symm
      rw [e]
      exact add_mem (Ideal.mul_mem_left _ _ hg1) (Ideal.mul_mem_left _ _ hg2)

end Joint

section Core

open Classical

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem core (h1 : HilbertNinetyDeterminant) (h3 : DetAtP) (h2 : CharFactor) {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
    {cst : LocCst X (rowSG Pr sel (mu0 X.F X.E X.K S))} {Dc : DetChr X R.m} {hc : Formalism.BasicNotions.CMData X.F X.E}
    (hX : X.Ok) (hPr : Pr.Ok) (hsel : ∀ v, (sel v).asIdeal.under (𝓞 X.F) = v.asIdeal)
    (hLoc : Dc.Loc Ch sel (mu0 X.F X.E X.K S) cst hc.sig) {i : ℕ} (hi : i < R.m) {N : ℕ} [NeZero N]
    {ST : Finset (HeightOneSpectrum (𝓞 X.E))} (p : DecoSet X.E N ST Pr.vGs)
    (hdec : decoOf ST Pr.vGs (ptOf hc N ST Pr.vGs p : GL (Fin N) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) = p) :
    (((detTw hc.sig (Dc.muAt i) (ptOf hc N ST Pr.vGs p : GL (Fin N) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)))⁻¹ : X.Kˣ) : X.K) =
      muInvDet sel (rowSG Pr sel (mu0 X.F X.E X.K S)) (mUof Ch (mu0 X.F X.E X.K S) i) (muAt Ch sel (mu0 X.F X.E X.K S) cst i) p.1.N
        (frsD sel (mu0 X.F X.E X.K S) p) := by
  set mu := mu0 X.F X.E X.K S with hmu
  set SB := rowSG Pr sel mu with hSBdef
  set ξ : Chr X.F X.E X.K := Dc.muAt i * (mu : Chr X.F X.E X.K) with hξdef
  have hξ' : ξ = Dc.muAt i := by rw [hξdef, hmu, trivialTuple_coe, mul_one]
  set g : GL (Fin N) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F) := (ptOf hc N ST Pr.vGs p : GL (Fin N) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) with hgdef
  have hg : g ∈ UAd hc N := (ptOf hc N ST Pr.vGs p).2
  obtain ⟨x, hx⟩ := h1 X.F X.E hc N g hg
  have htriv : (h90 hc.sig).ker ≤ ξ.ker := hLoc.trivF i hi
  have hdet : detTw hc.sig (Dc.muAt i) g = ξ x := by
    rw [← hξ']
    exact Formalism.L2.DIV.detTw_of_det hc.sig ξ htriv g x hx
  have hSB : SB = Pr.vGs := ChainCounts.rowSG_eq_of_QE sel mu (twistPrimes_trivialTuple_empty sel S)
  obtain ⟨hfr, hunitL, hcongL⟩ := h3 X.F X.E hc N ST Pr.vGs g hg
  rw [hdec] at hfr hunitL hcongL

  have hframe : ∀ P : HeightOneSpectrum (𝓞 X.E), ∀ z, frameAt P p.1.N z ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal p.1.N ↔ z ∈ stdAt X.E N P := by
    intro P
    obtain ⟨f, hf⟩ := hfr P
    exact Classical.epsilon_spec (p := fun f : Sp X.E N ≃ₗ[X.E] Sp X.E N => ∀ z, f z ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal p.1.N ↔ z ∈ stdAt X.E N P) ⟨f, hf⟩
  have hfrs : ∀ (P : HeightOneSpectrum (𝓞 X.E)) (h : P ∈ SB), ∃ hw : P ∈ Pr.vGs, frsD sel mu p ⟨P, h⟩ = p.1.liftFr ⟨P, hw⟩ := by
    intro P h
    have hw : P ∈ Pr.vGs := hSB ▸ h
    exact ⟨hw, by unfold frsD; rw [dif_pos hw]⟩
  have hlift : ∀ w : Pr.vGs, ∀ z, p.1.liftFr w z ∈ Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal p.1.N ↔ z ∈ stdAt X.E N w.1 :=
    fun w => (Deco.liftFr_spec (p.2.hasLift w)).1

  let a : HeightOneSpectrum (𝓞 X.E) → X.Eˣ := fun P =>
    if h : P ∈ SB then LinearEquiv.det (frsD sel mu p ⟨P, h⟩) else LinearEquiv.det (frameAt P p.1.N)
  have haS : ∀ (P : HeightOneSpectrum (𝓞 X.E)) (h : P ∈ SB), a P = LinearEquiv.det (frsD sel mu p ⟨P, h⟩) :=
    fun P h => dif_pos h
  have haN : ∀ P : HeightOneSpectrum (𝓞 X.E), P ∉ SB → a P = LinearEquiv.det (frameAt P p.1.N) := fun P h => dif_neg h
  have hunit : ∀ P : HeightOneSpectrum (𝓞 X.E), UnitAtI P (h90 hc.sig x * (ratId X.F X.E (a P))⁻¹) := by
    intro P
    rw [hx]
    by_cases h : P ∈ SB
    · obtain ⟨hw, he⟩ := hfrs P h
      rw [haS P h, he]
      exact hunitL P _ (hlift ⟨P, hw⟩)
    · rw [haN P h]
      exact hunitL P _ (hframe P)
  have hcong : ∀ P ∈ SB, CongOneAtI P ((h90 hc.sig x * (ratId X.F X.E (a P))⁻¹ : (AfE X.F X.E)ˣ) : AfE X.F X.E) := by
    intro P h
    rw [hx]
    obtain ⟨hw, he⟩ := hfrs P h
    rw [haS P h, he]
    exact hcongL ⟨P, hw⟩

  have hfin : {P : HeightOneSpectrum (𝓞 X.E) | ordE P (a P : X.E) ≠ 0}.Finite := by
    have hF := frame_det_unit_almost_all_primes (E := X.E) N p.1.N ⟨p.2.lat, p.2.uni⟩
    refine (hF.union (SB : Set (HeightOneSpectrum (𝓞 X.E))).toFinite).subset ?_
    intro P hP
    by_cases h : P ∈ SB
    · exact Or.inr h
    · left
      show ordDet P p.1.N ≠ 0
      have := hP
      simp only [Set.mem_ofPred_eq] at this
      rw [haN P h] at this
      exact this

  let k : HeightOneSpectrum (𝓞 X.E) → X.Kˣ := fun P =>
    if h : P ∈ SB then Classical.choose (hLoc.atq_ex i hi ⟨P, h⟩) else 1
  have hk : ∀ P (h : P ∈ SB), IsQValC ξ P (k P) := by
    intro P h
    show IsQValC ξ P (if h : P ∈ SB then Classical.choose (hLoc.atq_ex i hi ⟨P, h⟩) else 1)
    rw [dif_pos h]
    exact Classical.choose_spec (hLoc.atq_ex i hi ⟨P, h⟩)
  let χ : ∀ P : HeightOneSpectrum (𝓞 X.E), (𝓞 X.E ⧸ P.asIdeal)ˣ →* X.Kˣ := fun P =>
    if P ∈ Pr.vGs then (chiP Ch P i)⁻¹ else resChar (mu : Chr X.F X.E X.K) P

  have hsplit : ∀ P ∈ SB, ∃ P' : HeightOneSpectrum (𝓞 X.E), P' ≠ P ∧ P'.asIdeal.under (𝓞 X.F) = P.asIdeal.under (𝓞 X.F) ∧ P' ∉ SB := by
    intro P h
    have hw : P ∈ Pr.vGs := hSB ▸ h
    obtain ⟨hne, hnot⟩ := conjP_vGs hX hPr hw
    refine ⟨HeckeExHost.conjPrime₂ P, hne, ?_, by rw [hSB]; exact hnot⟩
    exact congrArg HeightOneSpectrum.asIdeal (HeckeExHost.conjP_under hX P)
  have hfac := h2 X.F X.E X.K hc ξ SB sel (fun P => (mUof Ch mu i P)⁻¹) χ k a x hsel hsplit
    (fun P h => ChainCounts.unifG_of hX hPr P (hSB ▸ h)) htriv (hLoc.unr i hi) (fun P h => hLoc.unif i hi P h)
    (fun P h v hv => hLoc.tame i hi P h v hv) (fun P h => hLoc.res i hi ⟨P, h⟩) hk hfin hunit hcong
  rw [hdet, hfac]
  unfold muInvDet muOff
  congr 1
  · refine finprod_congr fun v => ?_
    split_ifs with hv
    · rfl
    · have hsv : sel v ∉ SB := fun h => hv ⟨sel v, h, hsel v⟩
      rw [inv_inv, haN (sel v) hsv]
      rfl
  · rw [← Finset.prod_coe_sort SB]
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [haS P.1 P.2]
    have hq := hLoc.atq i hi P (k P.1) (hk P.1 P.2)
    unfold muAt
    rw [hq]
    congr 1
    change ((if P.1 ∈ Pr.vGs then (chiP Ch P.1 i)⁻¹ else resChar (mu : Chr X.F X.E X.K) P.1) : (𝓞 X.E ⧸ P.1.asIdeal)ˣ →* X.Kˣ)⁻¹ = _
    split_ifs <;> simp [hmu]


end Core

end DetChrL

end Formalism.L2.Col
end
end
