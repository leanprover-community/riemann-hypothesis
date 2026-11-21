import Mathlib
import GroundTheory.AutomorphicForms.HermitianExistence
import GroundTheory.GlobalFields.Adele.Approximation

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Theta

open Module Matrix NumberField IsDedekindDomain TensorProduct GroundTheory.Automorphic

section Objects

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

def IsCMUnramified : Prop :=
  IsTotallyReal F ∧ IsTotallyComplex E ∧
    ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.ramificationIdx (𝓞 F) = 1

def locIntegers (v : HeightOneSpectrum (𝓞 F)) :
    Subalgebra (v.adicCompletionIntegers F) (v.adicCompletion F ⊗[F] E) :=
  integralClosure _ _

variable {F E}

def baseGram (R : Type*) [Field R] [Algebra F R] {M : ℕ} (h : HermitianForm F E (Fin M → E)) :
    Matrix (Fin M) (Fin M) (R ⊗[F] E) :=
  (gram h.toSesq (Pi.basisFun E (Fin M))).map
    (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E)

def matForm (R : Type*) {A : Type*} [Field R] [CommRing A] [Algebra R A]
    [Algebra.IsQuadraticExtension R A] {ι : Type*} [Fintype ι] (G : Matrix ι ι A)
    (x y : ι → A) : A :=
  ∑ i, ∑ j, conj R A (x i) * G i j * y j

def signVector (A : Type*) [Ring A] (M p : ℕ) : Fin M → A :=
  fun i => if (i : ℕ) < p then 1 else -1

def HasSignatureAt {M : ℕ} (h : HermitianForm F E (Fin M → E)) (w : InfinitePlace F)
    (p q : ℕ) : Prop :=
  p + q = M ∧
    IsCongr (conjHom w.Completion (w.Completion ⊗[F] E)) (baseGram w.Completion h)
      (diagonal (signVector (w.Completion ⊗[F] E) M p))

variable (v : HeightOneSpectrum (𝓞 F))

def IsLocLattice {M : ℕ}
    (L : Submodule (locIntegers F E v) (Fin M → v.adicCompletion F ⊗[F] E)) : Prop :=
  L.FG ∧ Submodule.span (v.adicCompletion F ⊗[F] E)
    (L : Set (Fin M → v.adicCompletion F ⊗[F] E)) = ⊤

def IsSelfDualAt {M : ℕ} (h : HermitianForm F E (Fin M → E))
    (L : Submodule (locIntegers F E v) (Fin M → v.adicCompletion F ⊗[F] E)) : Prop :=
  IsLocLattice v L ∧
    ∀ x, x ∈ L ↔
      ∀ y ∈ L, matForm (v.adicCompletion F) (baseGram (v.adicCompletion F) h) x y ∈
        locIntegers F E v

def IsGlobalLattice {M : ℕ} (Λ : Submodule (𝓞 E) (Fin M → E)) : Prop :=
  Λ.FG ∧ Submodule.span E (Λ : Set (Fin M → E)) = ⊤

def latticeAt {M : ℕ} (Λ : Submodule (𝓞 E) (Fin M → E)) :
    Submodule (locIntegers F E v) (Fin M → v.adicCompletion F ⊗[F] E) :=
  Submodule.span _ ((fun x i => (1 : v.adicCompletion F) ⊗ₜ[F] x i) '' (Λ : Set (Fin M → E)))

end Objects

section Statements

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

def SelfDualHermitianExists.Statement : Prop :=
  IsCMUnramified F E →
    ∀ (M : ℕ), 1 ≤ M → ∀ p q : InfinitePlace F → ℕ, (∀ τ, p τ + q τ = M) →
      ((∃ h : HermitianForm F E (Fin M → E), (∀ τ, HasSignatureAt h τ (p τ) (q τ)) ∧
          ∀ v : HeightOneSpectrum (𝓞 F), ∃ L, IsSelfDualAt v h L) ↔
        Even (∑ τ, q τ))

def SelfDualHermitianUnique.Statement : Prop :=
  IsCMUnramified F E →
    ∀ (M : ℕ), 1 ≤ M → ∀ p q : InfinitePlace F → ℕ, (∀ τ, p τ + q τ = M) →
      ∀ h h' : HermitianForm F E (Fin M → E),
        (∀ τ, HasSignatureAt h τ (p τ) (q τ)) → (∀ τ, HasSignatureAt h' τ (p τ) (q τ)) →
        (∀ v : HeightOneSpectrum (𝓞 F), ∃ L, IsSelfDualAt v h L) →
        (∀ v : HeightOneSpectrum (𝓞 F), ∃ L', IsSelfDualAt v h' L') →
        h.Isometric h'

def SelfDualHermitianLocal.Statement : Prop :=
  IsCMUnramified F E →
    ∀ (M : ℕ), 1 ≤ M → ∀ h h' : HermitianForm F E (Fin M → E),
      ∀ (v : HeightOneSpectrum (𝓞 F)) (L L' : Submodule (locIntegers F E v)
          (Fin M → v.adicCompletion F ⊗[F] E)),
        IsSelfDualAt v h L → IsSelfDualAt v h' L' →
        ∃ P : Matrix (Fin M) (Fin M) (v.adicCompletion F ⊗[F] E), IsUnit P.det ∧
          (P.map (conjHom (v.adicCompletion F) (v.adicCompletion F ⊗[F] E)))ᵀ *
              baseGram (v.adicCompletion F) h' * P = baseGram (v.adicCompletion F) h ∧
          (fun x => P *ᵥ x) '' (L : Set (Fin M → v.adicCompletion F ⊗[F] E)) = L'

def SelfDualHermitianGlobalLattice.Statement : Prop :=
  IsCMUnramified F E →
    ∀ (M : ℕ), 1 ≤ M → ∀ h : HermitianForm F E (Fin M → E),
      (∀ v : HeightOneSpectrum (𝓞 F), ∃ L, IsSelfDualAt v h L) →
      ∃ Λ : Submodule (𝓞 E) (Fin M → E), IsGlobalLattice Λ ∧
        ∀ v : HeightOneSpectrum (𝓞 F), IsSelfDualAt v h (latticeAt v Λ)

end Statements

section Inhabitants

set_option linter.unusedSectionVars false

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

abbrev unitForm (F E : Type*) [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
    (M : ℕ) : HermitianForm F E (Fin M → E) :=
  diagForm (E := E) fun _ : Fin M => (1 : Fˣ)




variable (v : HeightOneSpectrum (𝓞 F))


def stdLatticeAt (M : ℕ) :
    Submodule (locIntegers F E v) (Fin M → v.adicCompletion F ⊗[F] E) where
  carrier := {x | ∀ i, x i ∈ locIntegers F E v}
  add_mem' hx hy i := add_mem (hx i) (hy i)
  zero_mem' _ := zero_mem _
  smul_mem' c x hx i := by
    rw [Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul]
    exact mul_mem c.2 (hx i)






def stdLattice (M : ℕ) : Submodule (𝓞 E) (Fin M → E) where
  carrier := {x | ∀ i, IsIntegral ℤ (x i)}
  add_mem' hx hy i := (hx i).add (hy i)
  zero_mem' _ := isIntegral_zero
  smul_mem' c x hx i := by
    rw [Pi.smul_apply, Algebra.smul_def]
    exact (RingOfIntegers.isIntegral_coe c).mul (hx i)

theorem single_mem_stdLattice {M : ℕ} (i : Fin M) : Pi.single i (1 : E) ∈ stdLattice (E := E) M := by
  intro j
  rcases eq_or_ne j i with rfl | hj
  · rw [Pi.single_eq_same]; exact isIntegral_one
  · rw [Pi.single_eq_of_ne hj]; exact isIntegral_zero





end Inhabitants

end GroundTheory.Heights₂.Theta
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Theta

open Module Matrix NumberField IsDedekindDomain TensorProduct GroundTheory.Automorphic

set_option linter.unusedSectionVars false

section LocalIntegers

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] (v : HeightOneSpectrum (𝓞 F))

theorem one_tmul_mem_locIntegers {x : E} (hx : IsIntegral ℤ x) :
    (1 : v.adicCompletion F) ⊗ₜ[F] x ∈ locIntegers F E v := by
  rw [locIntegers, mem_integralClosure_iff]
  obtain ⟨p, hp, hpx⟩ := hx
  refine ⟨p.map (Int.castRingHom (v.adicCompletionIntegers F)), hp.map _, ?_⟩
  set g : E →+* v.adicCompletion F ⊗[F] E :=
    (Algebra.TensorProduct.includeRight : E →ₐ[F] v.adicCompletion F ⊗[F] E).toRingHom
  have e : (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F ⊗[F] E)).comp
      (Int.castRingHom (v.adicCompletionIntegers F)) = g.comp (algebraMap ℤ E) :=
    RingHom.ext_int _ _
  rw [Polynomial.eval₂_map, e]
  show Polynomial.eval₂ (g.comp (algebraMap ℤ E)) (g x) p = 0
  rw [← Polynomial.hom_eval₂, hpx, map_zero]

end LocalIntegers

namespace Ex1GL

section Scaling

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] (v : HeightOneSpectrum (𝓞 F))

theorem inv_mem_of_notMem {c : 𝓞 F} (hc : c ∉ v.asIdeal) :
    (algebraMap F (v.adicCompletion F) (c : F))⁻¹ ∈ v.adicCompletionIntegers F := by
  have hv : Valued.v (algebraMap F (v.adicCompletion F) (c : F)) = v.valuation F (c : F) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (c : F)
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv,
    show (c : F) = algebraMap (𝓞 F) F c from rfl, HeightOneSpectrum.valuation_of_algebraMap,
    (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl v c).2 hc, inv_one]

end Scaling

end Ex1GL

namespace Ex1GL

section Finite

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

variable (v : HeightOneSpectrum (𝓞 F))

theorem algebraMap_mem_iff (x : F) :
    algebraMap F (v.adicCompletion F) x ∈ v.adicCompletionIntegers F ↔ v.valuation F x ≤ 1 := by
  have hv : Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, hv]

theorem algebraMap_integer_mem (c : 𝓞 F) :
    algebraMap F (v.adicCompletion F) (c : F) ∈ v.adicCompletionIntegers F := by
  rw [algebraMap_mem_iff]
  exact HeightOneSpectrum.valuation_le_one v c

theorem exists_approx (S : Finset (HeightOneSpectrum (𝓞 F))) (N : 𝓞 F) (hN : N ≠ 0)
    {r : v.adicCompletion F} (hr : r ∈ v.adicCompletionIntegers F) :
    ∃ b : 𝓞 F, (∃ o ∈ v.adicCompletionIntegers F,
        algebraMap F (v.adicCompletion F) (b : F) - r = algebraMap F (v.adicCompletion F) (N : F) * o) ∧
      ∀ u ∈ S, u ≠ v → ∃ o ∈ u.adicCompletionIntegers F,
        algebraMap F (u.adicCompletion F) (b : F) = algebraMap F (u.adicCompletion F) (N : F) * o := by
  classical
  have hNF : (N : F) ≠ 0 := by exact_mod_cast hN
  set n := algebraMap F (v.adicCompletion F) (N : F) with hn_def
  have hn0 : n ≠ 0 := by rw [hn_def, map_ne_zero]; exact hNF
  have hnO : n ∈ v.adicCompletionIntegers F := algebraMap_integer_mem v N

  have hcont : Continuous fun y : v.adicCompletion F => (y - r) * n⁻¹ :=
    (continuous_id.sub continuous_const).mul continuous_const
  have hopen : IsOpen ((fun y : v.adicCompletion F => (y - r) * n⁻¹) ⁻¹'
      (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    (Valued.isOpen_valuationSubring (v.adicCompletion F)).preimage hcont
  have hr0 : r ∈ (fun y : v.adicCompletion F => (y - r) * n⁻¹) ⁻¹'
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    show (r - r) * n⁻¹ ∈ v.adicCompletionIntegers F
    rw [sub_self, zero_mul]
    exact zero_mem _
  obtain ⟨f, hf⟩ := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 F) (K := F) v).exists_mem_open
    hopen ⟨r, hr0⟩
  change (algebraMap F (v.adicCompletion F) f - r) * n⁻¹ ∈ v.adicCompletionIntegers F at hf
  have hfO : algebraMap F (v.adicCompletion F) f ∈ v.adicCompletionIntegers F := by
    have : algebraMap F (v.adicCompletion F) f =
        ((algebraMap F (v.adicCompletion F) f - r) * n⁻¹) * n + r := by
      field_simp; ring
    rw [this]
    exact add_mem (mul_mem hf hnO) hr

  obtain ⟨k, hk1, hk2⟩ := GroundTheory.Global.exists_valuation_sub_le_one (R := 𝓞 F) (K := F)
    (insert v S) (fun u => if u = v then f / N else 0)
  have hkv : algebraMap F (v.adicCompletion F) (k - f / N) ∈ v.adicCompletionIntegers F := by
    rw [algebraMap_mem_iff]
    simpa using hk1 v (Finset.mem_insert_self v S)
  have hkS : ∀ u ∈ S, u ≠ v → algebraMap F (u.adicCompletion F) k ∈ u.adicCompletionIntegers F := by
    intro u hu huv
    rw [algebraMap_mem_iff]
    simpa [huv] using hk1 u (Finset.mem_insert_of_mem hu)
  have hint : ∀ u : HeightOneSpectrum (𝓞 F), u.valuation F ((N : F) * k) ≤ 1 := by
    intro u
    rw [← algebraMap_mem_iff]
    by_cases huv : u = v
    · subst huv
      have : algebraMap F (u.adicCompletion F) ((N : F) * k) =
          algebraMap F (u.adicCompletion F) (N : F) *
            algebraMap F (u.adicCompletion F) (k - f / N) + algebraMap F (u.adicCompletion F) f := by
        rw [← map_mul, ← map_add]
        congr 1
        field_simp
        ring
      rw [this]
      exact add_mem (mul_mem (algebraMap_integer_mem u N) hkv) hfO
    · rw [map_mul]
      refine mul_mem (algebraMap_integer_mem u N) ?_
      by_cases huS : u ∈ S
      · exact hkS u huS huv
      · rw [algebraMap_mem_iff]
        exact hk2 u (by simp [huv, huS])
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F ((N : F) * k) hint
  have hbF : (b : F) = (N : F) * k := hb
  refine ⟨b, ⟨algebraMap F (v.adicCompletion F) (k - f / N) +
      (algebraMap F (v.adicCompletion F) f - r) * n⁻¹, add_mem hkv hf, ?_⟩, fun u hu huv =>
      ⟨algebraMap F (u.adicCompletion F) k, hkS u hu huv, by rw [hbF, map_mul]⟩⟩
  rw [hbF, map_mul, mul_add, map_sub, map_div₀, ← hn_def]
  field_simp
  ring

end Finite

end Ex1GL

namespace Ex1GL

section Duality

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] (v : HeightOneSpectrum (𝓞 F)) {M : ℕ}

end Duality

end Ex1GL

namespace Ex1GL

section Bounds

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] (v : HeightOneSpectrum (𝓞 F)) {M : ℕ}

end Bounds

section Disc

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

end Disc

end Ex1GL

namespace Ex1GL

section Construction

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] {M : ℕ}

def latticeOf (S : Finset (HeightOneSpectrum (𝓞 F))) (c : F)
    (L' : (v : HeightOneSpectrum (𝓞 F)) →
      Submodule (locIntegers F E v) (Fin M → v.adicCompletion F ⊗[F] E)) :
    Submodule (𝓞 E) (Fin M → E) where
  carrier := {x | (∀ i, IsIntegral ℤ (c • x i)) ∧
    ∀ v ∈ S, (fun i => (1 : v.adicCompletion F) ⊗ₜ[F] x i) ∈ L' v}
  add_mem' {x y} hx hy := by
    refine ⟨fun i => ?_, fun v hv => ?_⟩
    · rw [Pi.add_apply, smul_add]; exact (hx.1 i).add (hy.1 i)
    · have : (fun i => (1 : v.adicCompletion F) ⊗ₜ[F] (x + y) i) =
          (fun i => (1 : v.adicCompletion F) ⊗ₜ[F] x i) +
            (fun i => (1 : v.adicCompletion F) ⊗ₜ[F] y i) := by
        ext i; simp [TensorProduct.tmul_add]
      rw [this]; exact add_mem (hx.2 v hv) (hy.2 v hv)
  zero_mem' := by
    refine ⟨fun i => ?_, fun v hv => ?_⟩
    · rw [Pi.zero_apply, smul_zero]; exact isIntegral_zero
    · have : (fun i => (1 : v.adicCompletion F) ⊗ₜ[F] (0 : Fin M → E) i) = 0 := by
        ext i; simp
      rw [this]; exact zero_mem _
  smul_mem' a x hx := by
    refine ⟨fun i => ?_, fun v hv => ?_⟩
    · show IsIntegral ℤ (c • ((a : E) * x i))
      rw [← mul_smul_comm]
      exact (RingOfIntegers.isIntegral_coe a).mul (hx.1 i)
    · have : (fun i => (1 : v.adicCompletion F) ⊗ₜ[F] (a • x) i) =
          (⟨(1 : v.adicCompletion F) ⊗ₜ[F] (a : E),
            one_tmul_mem_locIntegers v (RingOfIntegers.isIntegral_coe a)⟩ : locIntegers F E v) •
            (fun i => (1 : v.adicCompletion F) ⊗ₜ[F] x i) := by
        ext i
        show (1 : v.adicCompletion F) ⊗ₜ[F] (a • x i) =
          ((1 : v.adicCompletion F) ⊗ₜ[F] (a : E)) * ((1 : v.adicCompletion F) ⊗ₜ[F] x i)
        rw [Algebra.smul_def, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [this]; exact Submodule.smul_mem _ _ (hx.2 v hv)

end Construction

end Ex1GL

end GroundTheory.Heights₂.Theta
end
end
