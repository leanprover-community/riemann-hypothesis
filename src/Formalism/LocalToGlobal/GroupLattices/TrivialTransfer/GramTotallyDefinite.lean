import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsStab
import Formalism.LocalToGlobal.GroupLattices.TrivialTransfer.OneAddPowOfSq
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AdelstabL
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.FiniteClassSetOfFiniteIndex
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.GramDetIsUnit

section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P

namespace Formalism.L2.G.Triv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)

abbrev SV (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    Subring (E ⊗[F] v.adicCompletion F) :=
  tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring

section Trace

theorem T_mul (c : 𝔸) (z : 𝒜) : adelstabT F E (((1 : E) ⊗ₜ[F] c) * z) = c * adelstabT F E z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e a =>
    simp [adelstabT, Algebra.TensorProduct.tmul_mul_tmul, mul_smul_comm]
  | add x y hx hy => rw [mul_add, map_add, map_add, hx, hy, mul_add]

theorem T_int (z : 𝒜) (hz : ∀ v, prV (E := E) v z ∈ SV E v) : adelstabT F E z ∈ intAd F := by
  intro v
  have h1 := adelstabT_mem (afsplit_IE_int v _ (hz v))
  rw [afsplit_decomp, afsplitEps, Algebra.TensorProduct.one_def, afsplitIE_tmul, T_mul] at h1
  have h2 := h1 v
  rw [afsplit_mul_apply, afsplitI_self, one_mul] at h2
  exact h2

theorem expand {ι : Type} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι F E) (z : 𝒜) :
    z = ∑ i, ((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β i) ⊗ₜ[F]
      adelstabT F E ((β i ⊗ₜ[F] (1 : 𝔸)) * z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e a =>
    have he := ((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β).sum_repr e
    simp only [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply] at he
    conv_lhs => rw [← he]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.smul_tmul, mul_comm e (β i)]
    simp [adelstabT]
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_add, map_add, TensorProduct.tmul_add]

theorem exists_den : ∃ d : ℤ, d ≠ 0 ∧ ∀ z : 𝒜, (∀ v, prV (E := E) v z ∈ SV E v) →
    inclE (F := F) 𝔸 (d : E) * z ∈ 𝒮 := by
  classical
  let β₀ := Module.finBasis F E
  obtain ⟨m₁, hm₁, hi₁⟩ := adelstabL_den (fun i => β₀ i)
  have hu : ∀ _ : Fin (Module.finrank F E), IsUnit ((m₁ : ℤ) : F) := fun _ => (Int.cast_ne_zero.2 hm₁).isUnit
  let β := β₀.isUnitSMul hu
  have hβ : ∀ i, IsIntegral ℤ (β i) := by
    intro i
    have : β i = (m₁ : E) * β₀ i := by
      rw [Module.Basis.isUnitSMul_apply, Algebra.smul_def, map_intCast]
    rw [this]; exact hi₁ i
  obtain ⟨m₂, hm₂, hi₂⟩ := adelstabL_den (fun i => (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β i)
  refine ⟨m₂, hm₂, fun z hz => ?_⟩
  rw [expand β z, Finset.mul_sum]
  refine sum_mem fun i _ => ?_
  have ht : adelstabT F E ((β i ⊗ₜ[F] (1 : 𝔸)) * z) ∈ intAd F := by
    refine T_int _ fun v => ?_
    rw [map_mul]
    refine mul_mem ?_ (hz v)
    exact Subring.subset_closure (Or.inl ⟨⟨β i, ⟨⟨β i, hβ i⟩, rfl⟩⟩, rfl⟩)
  have h1 : inclE (F := F) 𝔸 (m₂ : E) * ((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β i ⊗ₜ[F]
      adelstabT F E ((β i ⊗ₜ[F] (1 : 𝔸)) * z)) =
      algebraMap (𝓞 E) E ⟨_, hi₂ i⟩ ⊗ₜ[F] adelstabT F E ((β i ⊗ₜ[F] (1 : 𝔸)) * z) := by
    show ((m₂ : E) ⊗ₜ[F] (1 : 𝔸)) * _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rfl
  rw [h1]
  exact levelaf_tmul_mem _ ht

end Trace

section Lattice

variable {n : Type} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] [NumberField F] [Algebra F E] in
theorem den_upper (Λ : Submodule (𝓞 E) (n → E)) [Finite n] (hfin : Module.Finite (𝓞 E) Λ) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ x ∈ Λ, ∀ k, IsIntegral ℤ ((m : E) * x k) := by
  classical
  have := Fintype.ofFinite n
  obtain ⟨s, hs⟩ : Λ.FG := Module.Finite.iff_fg.mp hfin
  obtain ⟨m, hm0, hm⟩ := adelstabL_den (fun p : s × n => (p.1 : n → E) p.2)
  refine ⟨m, hm0, ?_⟩
  intro x hx
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem x hx => intro k; exact hm (⟨x, hx⟩, k)
  | zero => intro k; simp [isIntegral_zero]
  | add x y _ _ hx hy => intro k; simpa [mul_add] using (hx k).add (hy k)
  | smul r x _ hx =>
    intro k
    have : (m : E) * (r • x) k = algebraMap (𝓞 E) E r * ((m : E) * x k) := by
      simp [Algebra.smul_def]; ring
    rw [this]
    exact (RingOfIntegers.isIntegral_coe r).mul (hx k)

omit [NumberField F] [Algebra F E] in
theorem den_lower (Λ : Submodule (𝓞 E) (n → E)) (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ k, (Pi.single k (m : E) : n → E) ∈ Λ := by
  classical
  have hk : ∀ k : n, ∃ N : ℕ, ∃ f : Fin N → E, ∃ w : Fin N → Λ,
      ∑ j, f j • (w j : n → E) = Pi.single k 1 := by
    intro k
    have : (Pi.single k 1 : n → E) ∈ Submodule.span E (Λ : Set (n → E)) := by
      rw [hspan]; exact Submodule.mem_top
    obtain ⟨N, f, w, h⟩ := Submodule.mem_span_set'.1 this
    exact ⟨N, f, fun j => ⟨w j, (w j).2⟩, h⟩
  choose N f w hw using hk
  obtain ⟨m, hm0, hm⟩ := adelstabL_den (fun p : Σ k : n, Fin (N k) => f p.1 p.2)
  refine ⟨m, hm0, fun k => ?_⟩
  have : (Pi.single k (m : E) : n → E) =
      ∑ j, (⟨(m : E) * f k j, hm ⟨k, j⟩⟩ : 𝓞 E) • (w k j : n → E) := by
    have h1 : (Pi.single k (m : E) : n → E) = (m : E) • (Pi.single k 1 : n → E) := by
      rw [← Pi.single_smul', smul_eq_mul, mul_one]
    rw [h1, ← hw k, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul E, smul_smul]
    rfl
  rw [this]
  exact sum_mem fun j _ => Λ.smul_mem _ (w k j).2

theorem incl_int (v : HeightOneSpectrum (𝓞 F)) (e : E) (he : IsIntegral ℤ e) :
    inclE (F := F) (v.adicCompletion F) e ∈ SV E v := by
  apply Subring.subset_closure
  left
  exact ⟨⟨e, ⟨⟨e, he⟩, rfl⟩⟩, rfl⟩

theorem loc_upper (Λ : Submodule (𝓞 E) (n → E)) (m : ℤ) (hm : ∀ x ∈ Λ, ∀ k, IsIntegral ℤ ((m : E) * x k))
    (v : HeightOneSpectrum (𝓞 F)) (y : n → E ⊗[F] v.adicCompletion F)
    (hy : y ∈ latS (F := F) (v.adicCompletion F) (SV E v) Λ) (i : n) :
    inclE (F := F) (v.adicCompletion F) (m : E) * y i ∈ SV E v := by
  induction hy using Submodule.span_induction with
  | mem y hy' =>
    obtain ⟨x, hx, rfl⟩ := hy'
    rw [← map_mul]
    exact incl_int v _ (hm x hx i)
  | zero => simp
  | add a b _ _ ha hb =>
    simp only [Pi.add_apply, mul_add]
    exact add_mem ha hb
  | smul s a _ ha =>
    simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
    rw [mul_left_comm]
    exact mul_mem s.2 ha

theorem loc_lower (Λ : Submodule (𝓞 E) (n → E)) (m : ℤ) (hm : ∀ k, (Pi.single k (m : E) : n → E) ∈ Λ)
    (v : HeightOneSpectrum (𝓞 F)) (y : n → E ⊗[F] v.adicCompletion F) (hy : ∀ i, y i ∈ SV E v) :
    (fun i => inclE (F := F) (v.adicCompletion F) (m : E) * y i) ∈ latS (F := F) (v.adicCompletion F) (SV E v) Λ := by
  have key : (fun i => inclE (F := F) (v.adicCompletion F) (m : E) * y i) =
      ∑ k, (⟨y k, hy k⟩ : SV E v) • (fun i => inclE (F := F) (v.adicCompletion F) ((Pi.single k (m : E) : n → E) i)) := by
    ext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · show _ = y i * inclE (F := F) (v.adicCompletion F) ((Pi.single i (m : E) : n → E) i)
      rw [Pi.single_eq_same, mul_comm]
    · intro k _ hk
      show y k * inclE (F := F) (v.adicCompletion F) ((Pi.single k (m : E) : n → E) i) = 0
      rw [Pi.single_eq_of_ne (Ne.symm hk), map_zero, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [key]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hm k, rfl⟩)

def latLoc (F : Type) [Field F] [NumberField F] [Algebra F E] (Λ : Submodule (𝓞 E) (n → E)) :
    Submodule (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) where
  carrier := {x | ∀ v : HeightOneSpectrum (𝓞 F),
    (fun i => prV (E := E) v (x i)) ∈ latS (F := F) (v.adicCompletion F) (SV E v) Λ}
  add_mem' := by
    intro a b ha hb v
    have : (fun i => prV (E := E) v ((a + b) i)) = (fun i => prV (E := E) v (a i)) + fun i => prV (E := E) v (b i) := by
      ext i; simp
    rw [this]; exact add_mem (ha v) (hb v)
  zero_mem' := by
    intro v
    have : (fun i => prV (E := E) v ((0 : n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) i)) = 0 := by ext i; simp
    rw [this]; exact zero_mem _
  smul_mem' := by
    intro s a ha v
    have : (fun i => prV (E := E) v ((s • a) i)) =
        (⟨prV (E := E) v s, afsplit_prV_int v _ s.2⟩ : SV E v) • fun i => prV (E := E) v (a i) := by
      ext i
      show prV (E := E) v ((s : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * a i) = prV (E := E) v s * prV (E := E) v (a i)
      rw [map_mul]
    rw [this]; exact Submodule.smul_mem _ _ (ha v)

theorem levelafC_int (m : ℤ) : levelafC E (m : 𝓞 F) = inclE (F := F) 𝔸 (m : E) := by
  simp only [levelafC, inclE, map_intCast]
  rw [← Algebra.TensorProduct.includeRight_apply, map_intCast]

theorem finite_stabAt_of_local (σ : E →ₐ[F] E) (J : Matrix n n E)
    (hτ : ∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ)
    (hH : IsHerm (σ : E →+* E) J) (hdet : IsUnit J.det) (hdef : IsTotDef σ J)
    (Λ : Submodule (𝓞 E) (n → E)) (hfin : Module.Finite (𝓞 E) Λ) (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤)
    (U : Subgroup (GL n 𝒜))
    (hU : ∀ x ∈ U, ∀ v : HeightOneSpectrum (𝓞 F),
      bc (prV (E := E) v) x ∈ stabGL (latS (F := F) (v.adicCompletion F) (SV E v) Λ))
    (g : UPts σ J 𝔸) :
    Finite (stabAt ((ratPts σ J 𝔸).subgroupOf (UPts σ J 𝔸)) (U.subgroupOf (UPts σ J 𝔸)) g) := by
  obtain ⟨m₁, hm₁, h₁⟩ := den_lower Λ hspan
  obtain ⟨m₂, hm₂, h₂⟩ := den_upper Λ hfin
  obtain ⟨d, hd, h₃⟩ := exists_den (F := F) (E := E)
  refine adelstab_core σ J hτ hH hdet hdef (latLoc F Λ) U ?_ (m₁ : 𝓞 F) ((d * m₂ : ℤ) : 𝓞 F) (Int.cast_ne_zero.2 hm₁)
    (Int.cast_ne_zero.2 (mul_ne_zero hd hm₂)) ?_ ?_ g
  · intro x hx y
    have key : ∀ v : HeightOneSpectrum (𝓞 F), (fun i => prV (E := E) v (((x : Matrix n n 𝒜) *ᵥ y) i)) =
        ((bc (prV (E := E) v) x : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ
          fun i => prV (E := E) v (y i) := by
      intro v
      ext i
      exact RingHom.map_mulVec (prV (E := E) v) (x : Matrix n n 𝒜) y i
    constructor
    · intro hy v
      rw [key v]
      exact (hU x hx v _).1 (hy v)
    · intro hy v
      have := hy v
      rw [key v] at this
      exact (hU x hx v _).2 this
  · intro w hw v
    have : (fun i => prV (E := E) v (levelafC E (m₁ : 𝓞 F) * w i)) =
        fun i => inclE (F := F) (v.adicCompletion F) (m₁ : E) * prV (E := E) v (w i) := by
      ext i
      rw [levelafC_int, map_mul, afsplit_prV_inclE]
    rw [this]
    exact loc_lower Λ m₁ h₁ v _ fun i => afsplit_prV_int v _ (hw i)
  · intro w hw i
    rw [levelafC_int, Int.cast_mul, map_mul, mul_assoc]
    refine h₃ _ fun v => ?_
    rw [map_mul, afsplit_prV_inclE]
    exact loc_upper Λ m₂ h₂ v _ (hw v) i

end Lattice

end Formalism.L2.G.Triv

end
end

section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P Formalism.BasicNotions

namespace Formalism.L2.G.Triv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {k : ℕ}

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F

theorem gen_coprime (U : Subgroup (GL (Fin k) 𝒜)) (g : ℕ) (hg : g.Prime) (v : HeightOneSpectrum (𝓞 F))
    (hv : (g : 𝓞 F) ∈ v.asIdeal) (ρ : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F)
    (h : GL (Fin k) (v.adicCompletion F))
    (hU : ∀ z ∈ U, h⁻¹ * bc ρ (bc (prV (E := E) v) z) * h ∈ iwU F k v)
    (x : GL (Fin k) 𝒜) (γ : GL (Fin k) E) (hγ : x⁻¹ * bc (inclE (F := F) 𝔸) γ * x ∈ U) (N : ℕ) (hN : Nat.Coprime N g)
    (hγN : bc (inclE (F := F) 𝔸) γ ^ N = 1) : γ = 1 := by
  have hφ : ∀ A : GL (Fin k) E, bc ρ (bc (prV (E := E) v) (bc (inclE (F := F) 𝔸) A))
      = bc (ρ.comp ((prV (E := E) v).comp (inclE (F := F) 𝔸))) A := by
    intro A
    apply Units.ext
    ext i j
    simp [bc]
  have hinj : Function.Injective (ρ.comp ((prV (E := E) v).comp (inclE (F := F) 𝔸))) :=
    RingHom.injective _
  have hz : (x⁻¹ * bc (inclE (F := F) 𝔸) γ * x) ^ N = 1 := by
    rw [show x⁻¹ * bc (inclE (F := F) 𝔸) γ * x = MulAut.conj x⁻¹ (bc (inclE (F := F) 𝔸) γ) by
      simp [MulAut.conj_apply], ← map_pow, hγN, map_one]
  have hmem := hU _ hγ
  have hwN : (bc ρ (bc (prV (E := E) v) (x⁻¹ * bc (inclE (F := F) 𝔸) γ * x))) ^ N = 1 := by
    rw [← map_pow, ← map_pow, hz, map_one, map_one]
  have hδN : (h⁻¹ * bc ρ (bc (prV (E := E) v) (x⁻¹ * bc (inclE (F := F) 𝔸) γ * x)) * h) ^ N = 1 := by
    rw [show h⁻¹ * bc ρ (bc (prV (E := E) v) (x⁻¹ * bc (inclE (F := F) 𝔸) γ * x)) * h
        = MulAut.conj h⁻¹ (bc ρ (bc (prV (E := E) v) (x⁻¹ * bc (inclE (F := F) 𝔸) γ * x))) by
      simp only [MulAut.conj_apply, inv_inv], ← map_pow, hwN, map_one]
  have hδ1 := iwU_coprime v g hg hv _ hmem N hN hδN
  have hw1 : bc ρ (bc (prV (E := E) v) (x⁻¹ * bc (inclE (F := F) 𝔸) γ * x)) = 1 := by
    calc _ = h * (h⁻¹ * bc ρ (bc (prV (E := E) v) (x⁻¹ * bc (inclE (F := F) 𝔸) γ * x)) * h) * h⁻¹ := by
          group
      _ = 1 := by rw [hδ1]; group
  simp only [map_mul, map_inv] at hw1
  rw [hφ] at hw1
  have hγ1 : bc (ρ.comp ((prV (E := E) v).comp (inclE (F := F) 𝔸))) γ = 1 := by
    calc _ = bc ρ (bc (prV (E := E) v) x) * ((bc ρ (bc (prV (E := E) v) x))⁻¹
          * bc (ρ.comp ((prV (E := E) v).comp (inclE (F := F) 𝔸))) γ * bc ρ (bc (prV (E := E) v) x))
          * (bc ρ (bc (prV (E := E) v) x))⁻¹ := by group
      _ = 1 := by rw [hw1]; group
  apply Units.ext
  ext i j
  apply hinj
  have e := congrArg (fun A : GL (Fin k) (v.adicCompletion F) => A.1 i j) hγ1
  simpa [bc, Matrix.one_apply, apply_ite] using e

private lemma inv_mul_mul_pow {G : Type} [Group G] (x y : G) (n : ℕ) :
    (x⁻¹ * y * x) ^ n = x⁻¹ * y ^ n * x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, pow_succ]; group

theorem gen_triv (σ : E →ₐ[F] E) (J : Matrix (Fin k) (Fin k) E)
    (hτ : ∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ)
    (hH : IsHerm (σ : E →+* E) J) (hdet : IsUnit J.det) (hdef : IsTotDef σ J)
    (Λ : Submodule (𝓞 E) (Fin k → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hspan : Submodule.span E (Λ : Set (Fin k → E)) = ⊤)
    (U : Subgroup (GL (Fin k) 𝒜))
    (hU : ∀ x ∈ U, ∀ v : HeightOneSpectrum (𝓞 F),
      bc (prV (E := E) v) x ∈ stabGL (latS (F := F) (v.adicCompletion F) (SV E v) Λ))
    (g : Fin 2 → ℕ) (hg : ∀ i, (g i).Prime) (hne : g 0 ≠ g 1) (v : Fin 2 → HeightOneSpectrum (𝓞 F))
    (hv : ∀ i, (g i : 𝓞 F) ∈ (v i).asIdeal) (ρ : ∀ i, E ⊗[F] (v i).adicCompletion F →+* (v i).adicCompletion F)
    (h : ∀ i, GL (Fin k) ((v i).adicCompletion F))
    (hUg : ∀ i, ∀ z ∈ U, (h i)⁻¹ * bc (ρ i) (bc (prV (E := E) (v i)) z) * h i ∈ iwU F k (v i))
    (x : UPts σ J 𝔸) (γ : GL (Fin k) E) (hγJ : γ ∈ UJ (σ : E →+* E) J)
    (hγ : (x : GL (Fin k) 𝒜)⁻¹ * bc (inclE (F := F) 𝔸) γ * x ∈ U) : γ = 1 := by
  have hyR : bc (inclE (F := F) 𝔸) γ ∈ ratPts σ J 𝔸 := ⟨γ, hγJ, rfl⟩
  have hyU : bc (inclE (F := F) 𝔸) γ ∈ UPts σ J 𝔸 :=
    Formalism.UG.P.rational_points_le_holds F E (Fin k) σ J 𝔸 hyR
  have hpowU : ∀ m : ℕ, (x : GL (Fin k) 𝒜)⁻¹ * bc (inclE (F := F) 𝔸) γ ^ m * x ∈ U := by
    intro m
    rw [← inv_mul_mul_pow]
    exact U.pow_mem hγ m
  haveI hfinS := finite_stabAt_of_local σ J hτ hH hdet hdef Λ hfin hspan U hU x
  let f : ℕ → stabAt ((ratPts σ J 𝔸).subgroupOf (UPts σ J 𝔸)) (U.subgroupOf (UPts σ J 𝔸)) x :=
    fun m => ⟨⟨⟨bc (inclE (F := F) 𝔸) γ ^ m, pow_mem hyU m⟩, Subgroup.mem_subgroupOf.2 (pow_mem hyR m)⟩,
      by
        show _ ∈ U.subgroupOf (UPts σ J 𝔸)
        exact Subgroup.mem_subgroupOf.2 (hpowU m)⟩
  obtain ⟨m₁, m₂, hne12, heq⟩ := Finite.exists_ne_map_eq_of_infinite f
  have hpow : bc (inclE (F := F) 𝔸) γ ^ m₁ = bc (inclE (F := F) 𝔸) γ ^ m₂ := by
    have e := congrArg (fun s => ((s.1 : UPts σ J 𝔸) : GL (Fin k) 𝒜)) heq
    exact e

  obtain ⟨N, hN0, hyN⟩ : ∃ N : ℕ, 0 < N ∧ bc (inclE (F := F) 𝔸) γ ^ N = 1 := by
    rcases Nat.lt_or_gt_of_ne hne12 with hlt | hlt
    · refine ⟨m₂ - m₁, Nat.sub_pos_of_lt hlt, ?_⟩
      have e : bc (inclE (F := F) 𝔸) γ ^ m₂
          = bc (inclE (F := F) 𝔸) γ ^ m₁ * bc (inclE (F := F) 𝔸) γ ^ (m₂ - m₁) := by
        rw [← pow_add, Nat.add_sub_cancel' hlt.le]
      rw [← hpow] at e
      exact mul_left_cancel (a := bc (inclE (F := F) 𝔸) γ ^ m₁) (by rw [mul_one]; exact e.symm)
    · refine ⟨m₁ - m₂, Nat.sub_pos_of_lt hlt, ?_⟩
      have e : bc (inclE (F := F) 𝔸) γ ^ m₁
          = bc (inclE (F := F) 𝔸) γ ^ m₂ * bc (inclE (F := F) 𝔸) γ ^ (m₁ - m₂) := by
        rw [← pow_add, Nat.add_sub_cancel' hlt.le]
      rw [hpow] at e
      exact mul_left_cancel (a := bc (inclE (F := F) 𝔸) γ ^ m₂) (by rw [mul_one]; exact e.symm)

  obtain ⟨a, m, hm, hNam⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0.ne' (g 0) (hg 0).one_lt.ne'
  have hg0m : Nat.Coprime m (g 0) :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (hg 0)).mpr hm)
  have hγ1 : γ ^ (g 0 ^ a) = 1 := by
    refine gen_coprime U (g 0) (hg 0) (v 0) (hv 0) (ρ 0) (h 0) (hUg 0) (x : GL (Fin k) 𝒜)
      (γ ^ (g 0 ^ a)) ?_ m hg0m ?_
    · rw [map_pow]
      exact hpowU _
    · rw [map_pow, ← pow_mul, ← hNam]
      exact hyN
  have hcop : Nat.Coprime (g 0 ^ a) (g 1) :=
    Nat.Coprime.pow_left a ((Nat.coprime_primes (hg 0) (hg 1)).mpr hne)
  refine gen_coprime U (g 1) (hg 1) (v 1) (hv 1) (ρ 1) (h 1) (hUg 1) (x : GL (Fin k) 𝒜) γ hγ
    (g 0 ^ a) hcop ?_
  rw [← map_pow, hγ1, map_one]

end Formalism.L2.G.Triv

end
end

section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G.Triv

open Formalism.L2.G.Cmp

section Reindex

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n m : Type} [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

omit [NumberField F] [Algebra F E] [DecidableEq n] [DecidableEq m] [Field F] in
theorem hform_reindex (e : n ≃ m) (σ : E →+* E) (J : Matrix n n E) (x y : m → E) :
    hform σ (J.reindex e e) x y = hform σ J (x ∘ e) (y ∘ e) := by
  simp only [hform, Matrix.reindex_apply, Matrix.submatrix_apply, Function.comp_apply]
  exact Fintype.sum_equiv e.symm _ _ fun i => Fintype.sum_equiv e.symm _ _ fun j => by simp

omit [DecidableEq n] [DecidableEq m] in
theorem totDef_reindex (e : n ≃ m) (σ : E →ₐ[F] E) (J : Matrix n n E) (h : IsTotDef σ J) : IsTotDef σ (J.reindex e e) := by
  refine ⟨h.1, fun ι => ?_⟩
  have hne : ∀ x : m → E, x ≠ 0 → x ∘ e ≠ 0 := fun x hx h0 =>
    hx (funext fun i => by simpa using congrFun h0 (e.symm i))
  have h2 := h.2 ι
  unfold IsDefiniteAt at h2 ⊢
  rcases h2 with h2 | h2
  · left
    intro x hx
    obtain ⟨a, ha, hpos⟩ := h2 (x ∘ e) (hne x hx)
    exact ⟨a, by rw [hform_reindex]; exact ha, hpos⟩
  · right
    intro x hx
    obtain ⟨a, ha, hpos⟩ := h2 (x ∘ e) (hne x hx)
    exact ⟨a, by rw [hform_reindex]; exact ha, hpos⟩

end Reindex

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

theorem gram_totally_definite (sp : Spaces R F E) : IsTotDef sp.cm.sig sp.gram0 :=
  totDef_reindex _ _ _ (gram_totDef sp.cm (sp.X 0) (sp.X_sig 0) (sp.X_def 0 (Nat.zero_le _)))

theorem U_stab (L : ColLevel R F E sp gp C A clsLat) (x : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hx : x ∈ L.U)
    (v : HeightOneSpectrum (𝓞 F)) :
    bc (prV (E := E) v) x ∈ stabGL (latS (F := F) (v.adicCompletion F) (SV E v) L.Lb) :=
  (Subgroup.mem_inf.1 (L.Uloc_lev v (((L.U_eq x).1 hx).2 v))).2

theorem trivStabU (L : ColLevel R F E sp gp C A clsLat) (hp : ∀ i, (gp i).Prime) (hne : gp 0 ≠ gp 1) : TrivStabU L := by
  intro x γ hγ
  choose v hv using fun i => exists_place (F := F) (gp i) (hp i)
  apply Subtype.ext
  exact gen_triv sp.cm.sig sp.gram0 (sig_conj sp.cm) sp.baseGram_isHermitian (isUnit_det_gram0 sp) (gram_totally_definite sp)
    L.Lb L.Lb_fin L.Lb_span L.U (fun z hz w => U_stab L z hz w) gp hp hne v hv
    (fun i => (RingHom.fst _ _).comp (L.splitG i (v i) (hv i)).toRingHom)
    (fun i => L.frG i (v i) (hv i))
    (fun i z hz => (L.Uloc_g i (v i) (hv i) _ (L.Uloc_le (v i) (((L.U_eq z).1 hz).2 (v i)))).1
      (((L.U_eq z).1 hz).2 (v i)))
    x γ γ.2 (Subgroup.mem_subgroupOf.1 hγ)

theorem card_stab (L : ColLevel R F E sp gp C A clsLat) (hp : ∀ i, (gp i).Prime) (hne : gp 0 ≠ gp 1) (c : C.cls 0) :
    Nat.card (C.stab 0 c) = 1 := by
  rw [Nat.card_congr (stabRec (L := L) c)]
  refine Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨1, ?_⟩⟩⟩
  · exact (trivStabU L hp hne _ _ a.2).trans (trivStabU L hp hne _ _ b.2).symm
  · rw [map_one, mul_one, inv_mul_cancel]
    exact one_mem _

section Record

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem trivStabU_rec (D : D7) (lev : LevelData D) (u : D.what₂.Word) : TrivStabU (lev u) :=
  trivStabU (lev u) D.host.g_prime D.host.g_ne

theorem stabZero_rec (D : D7) (lev : LevelData D) (u : D.what₂.Word) : (D.mem u).C.StabZero := fun c =>
  (Nat.card_eq_one_iff_unique.1 (card_stab (lev u) D.host.g_prime D.host.g_ne c)).1

end Record

end Formalism.L2.G.Triv

end
end
