import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatCoreB
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLIwasawaDecompositionStandardParabolic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDiscreteUOfIsDiscrete

section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace PositivityTheory.Rg.Rs.SatakeVectors.Core

section Corner

variable {R S : Type} [CommRing R] [CommRing S]

theorem cc_cornerGL_leviEmb {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (s : R →ₙ+* S)
    (l : ∀ i, GL (Fin (n i)) R) :
    cornerGL N s (leviEmb R (stdBlocks n h) l) = leviEmb S (stdBlocks n h) (fun i => cornerGL (n i) s (l i)) := by
  apply Units.ext
  ext p q
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks n h).surjective p
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks n h).surjective q
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    by_cases hij : i = j
    · subst hij
      rw [GlobalTheory.IwasawaAdelic.cornerGL_entry_same, GlobalTheory.IwasawaAdelic.cornerGL_entry_same, leviEmb_apply_same]
    · have hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨a, j⟩ := fun he =>
        hij (by simpa using (stdBlocks n h).injective he)
      rw [GlobalTheory.IwasawaAdelic.cornerGL_entry_ne _ _ hne, GlobalTheory.IwasawaAdelic.cornerGL_entry_ne _ _ hij,
        leviEmb_apply_same]
  · have hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨b, j⟩ := fun he =>
      hab (congrArg Sigma.fst ((stdBlocks n h).injective he))
    rw [leviEmb_apply_ne _ _ _ hab, GlobalTheory.IwasawaAdelic.cornerGL_entry_ne _ _ hne, leviEmb_apply_ne _ _ _ hab, map_zero]

theorem cc_cornerGL_mem_unipRad {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (s : R →ₙ+* S) {u : GL (Fin N) R}
    (hu : u ∈ unipRad R (stdBlocks n h)) : cornerGL N s u ∈ unipRad S (stdBlocks n h) := by
  rw [mem_unipRad] at hu ⊢
  obtain ⟨hP, hD⟩ := hu
  refine ⟨mem_parab_iff.2 fun a b i j hlt => ?_, fun a i j => ?_⟩
  · have hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨b, j⟩ := fun he => by
      have := congrArg Sigma.fst ((stdBlocks n h).injective he)
      exact (ne_of_gt hlt) this
    rw [GlobalTheory.IwasawaAdelic.cornerGL_entry_ne _ _ hne, mem_parab_iff.1 hP a b i j hlt, map_zero]
  · by_cases hij : i = j
    · subst hij
      rw [GlobalTheory.IwasawaAdelic.cornerGL_entry_same, hD a i i]; simp
    · have hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨a, j⟩ := fun he => by
        exact hij (by simpa using (stdBlocks n h).injective he)
      rw [GlobalTheory.IwasawaAdelic.cornerGL_entry_ne _ _ hne, hD a i j, Matrix.one_apply_ne hij, Matrix.one_apply_ne hij,
        map_zero]

end Corner

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem iwasawa_inf {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (x : GA E N) :
    ∃ u ∈ unipRad (Ad E) (stdBlocks n h), ∃ (m : ∀ i, GL (Fin (n i)) (Cinf E)) (k : Kinf E N),
      x = u * leviEmb (Ad E) (stdBlocks n h) (fun i => infGL E (n i) (m i)) *
        (infGL E N (Unitary.toUnits k) * finGL E N (Matrix.GeneralLinearGroup.map (pFin E) x)) := by
  obtain ⟨b, hb, k, hy⟩ :=
    GlobalTheory.IwasawaAdelic.exists_upper_mul_unitary_inf E N (Matrix.GeneralLinearGroup.map (pInf E) x)
  have hbP := GlobalTheory.IwasawaAdelic.mem_parab_of_upper n h b hb
  obtain ⟨u, hu, hbu⟩ := exists_levi_mul_unip (Cinf E) (stdBlocks n h) ⟨b, hbP⟩
  set L := leviEmb (Cinf E) (stdBlocks n h) (leviProj (Cinf E) (stdBlocks n h) ⟨b, hbP⟩) with hL
  have hN := leviEmb_mem_normalizer (Cinf E) (stdBlocks n h) (leviProj (Cinf E) (stdBlocks n h) ⟨b, hbP⟩)
  have hu' : L * u * L⁻¹ ∈ unipRad (Cinf E) (stdBlocks n h) := (Subgroup.mem_normalizer_iff.1 hN u).1 hu
  refine ⟨infGL E N (L * u * L⁻¹), GlobalTheory.IwasawaAdelic.infGL_mem_unipRad E n h _ hu',
    fun i => leviProj (Cinf E) (stdBlocks n h) ⟨b, hbP⟩ i, k, ?_⟩
  rw [← GlobalTheory.IwasawaAdelic.infGL_leviEmb, ← hL]
  conv_lhs => rw [← infGL_mul_finGL x, hy]
  simp only [Subtype.coe_mk] at hbu
  rw [hbu]
  simp only [map_mul, map_inv]
  group

theorem finGL_locGL_leviEmb {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (w : HeightOneSpectrum (𝓞 E))
    (μ : ∀ i, GL (Fin (n i)) (w.adicCompletion E)) :
    finGL E N (locGL E N w (leviEmb (w.adicCompletion E) (stdBlocks n h) μ)) =
      leviEmb (Ad E) (stdBlocks n h) (fun i => finGL E (n i) (locGL E (n i) w (μ i))) := by
  rw [locGL, cc_cornerGL_leviEmb, finGL, cc_cornerGL_leviEmb]
  rfl

theorem finGL_locGL_mem_unipRad {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (w : HeightOneSpectrum (𝓞 E))
    {u : GL (Fin N) (w.adicCompletion E)} (hu : u ∈ unipRad (w.adicCompletion E) (stdBlocks n h)) :
    finGL E N (locGL E N w u) ∈ unipRad (Ad E) (stdBlocks n h) := by
  exact cc_cornerGL_mem_unipRad n h _ (cc_cornerGL_mem_unipRad n h _ hu)

theorem commute_finGL_locGL {N : ℕ} (w : HeightOneSpectrum (𝓞 E)) {y : GA E N}
    (hy : Matrix.GeneralLinearGroup.map (pLoc E w) (Matrix.GeneralLinearGroup.map (pFin E) y) = 1)
    (g : GL (Fin N) (w.adicCompletion E)) :
    y * finGL E N (locGL E N w g) = finGL E N (locGL E N w g) * y := by
  have hc := LocSph.comm_locGL w _ hy g
  conv_lhs => rw [← infGL_mul_finGL y]
  conv_rhs => rw [← infGL_mul_finGL y]
  rw [mul_assoc, ← (finGL E N).map_mul, hc, (finGL E N).map_mul, ← mul_assoc, infGL_comm, mul_assoc]

theorem exists_split_at {N : ℕ} (w : HeightOneSpectrum (𝓞 E)) (y : GA E N) :
    ∃ (y₀ : GA E N) (g : GL (Fin N) (w.adicCompletion E)),
      Matrix.GeneralLinearGroup.map (pLoc E w) (Matrix.GeneralLinearGroup.map (pFin E) y₀) = 1 ∧
        y = y₀ * finGL E N (locGL E N w g) := by
  set g := Matrix.GeneralLinearGroup.map (pLoc E w) (Matrix.GeneralLinearGroup.map (pFin E) y)
  refine ⟨y * (finGL E N (locGL E N w g))⁻¹, g, ?_, by group⟩
  rw [map_mul, map_mul, map_inv, map_inv, pFin_finGL, pLoc_locGL, mul_inv_cancel]

end PositivityTheory.Rg.Rs.SatakeVectors.Core

end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.SmGL GlobalTheory.CuspRep
open scoped TensorProduct

namespace PositivityTheory.Rg.Rs.SatakeVectors.Core

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem heckeVec_apply {N : ℕ} (w : HeightOneSpectrum (𝓞 E)) {F : Sm E N}
    {f : GL (Fin N) (w.adicCompletion E) → ℂ} (hf : f ∈ Hecke ℂ (KGL w N)) (y : GA E N) :
    (heckeVec ((finRep E N).comp (locGL E N w)) (KGL w N) f F).1 y =
      heckeVec (rightReg ℂ _ ℂ) (KGL w N) f (fun g => F.1 (y * finGL E N (locGL E N w g))) 1 := by
  have hK := Final.GLintComm E w N
  rw [heckeVec, heckeVec]
  have e1 := ((LinearMap.proj (R := ℂ) (φ := fun _ : GA E N => ℂ) y).comp (Sm E N).subtype).toAddMonoidHom.map_finsum
    (finite_heckeVec hK hf ((finRep E N).comp (locGL E N w)) F)
  have e2 := (LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin N) (w.adicCompletion E) => ℂ)
    (1 : GL (Fin N) (w.adicCompletion E))).toAddMonoidHom.map_finsum
    (finite_heckeVec hK hf (rightReg ℂ _ ℂ) (fun g => F.1 (y * finGL E N (locGL E N w g))))
  refine e1.trans (Eq.trans (finsum_congr fun c => ?_) e2.symm)
  show f c.out • F.1 (y * finGL E N (locGL E N w c.out)) = f c.out • F.1 (y * finGL E N (locGL E N w (1 * c.out)))
  rw [one_mul]

def evAt {m : ℕ} (U : Submodule ℂ (Sm E m)) (x : GA E m) : U →ₗ[ℂ] ℂ :=
  LinearMap.proj x ∘ₗ (Sm E m).subtype ∘ₗ U.subtype

@[simp] theorem evAt_apply {m : ℕ} (U : Submodule ℂ (Sm E m)) (x : GA E m) (ψ : U) : evAt U x ψ = ψ.1.1 x := rfl

theorem exists_tensor {c : ℕ} {n : Fin c → ℕ} (U : ∀ i, Submodule ℂ (Sm E (n i)))
    {Φ : (∀ i, GA E (n i)) → ℂ} (hΦ : Φ ∈ GlobalTheory.BCWords.tensorSp U) :
    ∃ v : ⨂[ℂ] i, U i, ∀ m, Φ m = evT (fun i => evAt (U i) (m i)) v := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, rfl⟩ := hx
    exact ⟨PiTensorProduct.tprod ℂ φ, fun m => by rw [evT_tprod]; rfl⟩
  | zero => exact ⟨0, fun m => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨v, hv⟩ := hx
    obtain ⟨v', hv'⟩ := hy
    exact ⟨v + v', fun m => by rw [Pi.add_apply, hv, hv', map_add]⟩
  | smul a x _ hx =>
    obtain ⟨v, hv⟩ := hx
    exact ⟨a • v, fun m => by rw [Pi.smul_apply, hv, map_smul, smul_eq_mul]⟩

end PositivityTheory.Rg.Rs.SatakeVectors.Core

end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open scoped TensorProduct

namespace PositivityTheory.Rg.Rs.SatakeVectors

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

namespace Core

def locFn {N : ℕ} (w : HeightOneSpectrum (𝓞 E)) (F : Sm E N) (y : GA E N) : GL (Fin N) (w.adicCompletion E) → ℂ :=
  fun g => F.1 (y * finGL E N (locGL E N w g))

def locRepU {m : ℕ} (w : HeightOneSpectrum (𝓞 E)) (U : Submodule ℂ (Sm E m))
    (hst : ∀ g : GL (Fin m) (Af E), ∀ ψ ∈ U, finRep E m g ψ ∈ U) :
    Representation ℂ (GL (Fin m) (w.adicCompletion E)) U :=
  GlobalTheory.PRep.sub ((finRep E m).comp (locGL E m w)) U fun g ψ hψ => hst _ ψ hψ

theorem evT_piTensor_locRepU {c : ℕ} {n : Fin c → ℕ} (w : HeightOneSpectrum (𝓞 E)) (U : ∀ i, Submodule ℂ (Sm E (n i)))
    (hst : ∀ i (g : GL (Fin (n i)) (Af E)), ∀ ψ ∈ U i, finRep E (n i) g ψ ∈ U i) (x : ∀ i, GA E (n i))
    (μ : ∀ i, GL (Fin (n i)) (w.adicCompletion E)) (v : ⨂[ℂ] i, U i) :
    evT (fun i => evAt (U i) (x i)) (piTensor (fun i => locRepU w (U i) (hst i)) μ v) =
      evT (fun i => evAt (U i) (x i * finGL E (n i) (locGL E (n i) w (μ i)))) v := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r ψ =>
    rw [map_smul, map_smul, map_smul, piTensor_tprod, evT_tprod, evT_tprod]
    rfl
  | add v₁ v₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]

end Core

open PositivityTheory.Rg.Rs.SatakeVectors.Core in

theorem isSatVecGL_of_ind {c N : ℕ} {n : Fin c → ℕ} (h : ∑ i, n i = N) {w : HeightOneSpectrum (𝓞 E)}
    (U : ∀ i, Submodule ℂ (Sm E (n i)))
    (hst : ∀ i (g : GL (Fin (n i)) (Af E)), ∀ ψ ∈ U i, finRep E (n i) g ψ ∈ U i)
    (hsm : ∀ i, ∀ ψ ∈ U i, IsOpen {g : GL (Fin (n i)) (w.adicCompletion E) | finRep E (n i) (locGL E (n i) w g) ψ = ψ})
    (S : Fin c → Multiset ℂˣ) (hS : ∀ i, SatLike (U i) w (S i))
    {F : Sm E N} (h0 : F ≠ 0) (hK : ∀ k ∈ GlobalTheory.LFun.KGL w N, finRep E N (locGL E N w k) F = F)
    (hu : ∀ u ∈ unipRad (Ad E) (stdBlocks n h), ∀ g, F.1 (u * g) = F.1 g)
    (ht : ∀ (k : Kinf E N) (g : GL (Fin N) (Af E)),
      (fun m => F.1 (leviEmb (Ad E) (stdBlocks n h) m * (infGL E N (Unitary.toUnits k) * finGL E N g))) ∈
        GlobalTheory.BCWords.tensorSp U) :
    GlobalTheory.LFun.IsSatVecGL w ((finRep E N).comp (locGL E N w)) F
      (∑ i, (S i).map (· * qU w ((modExp (fun i => Fin (n i)) i : ℂ) / 2))) := by
  classical
  set Bt := ∑ i, (S i).map (· * qU w ((modExp (fun i => Fin (n i)) i : ℂ) / 2)) with hBt

  have key : ∀ y₀ : GA E N,
      Matrix.GeneralLinearGroup.map (pLoc E w) (Matrix.GeneralLinearGroup.map (pFin E) y₀) = 1 →
      locFn w F y₀ = 0 ∨ GlobalTheory.LFun.IsSatVecGL w (GlobalTheory.PRep.rightReg ℂ _ ℂ) (locFn w F y₀) Bt := by
    intro y₀ hy₀
    by_cases hG0 : locFn w F y₀ = 0
    · exact Or.inl hG0
    right
    obtain ⟨u, hu₀, m, k, hy⟩ := iwasawa_inf n h y₀
    set g₀ := Matrix.GeneralLinearGroup.map (pFin E) y₀ with hg₀
    obtain ⟨v, hv⟩ := exists_tensor U (ht k g₀)
    have hs : ∀ i, GlobalTheory.PRep.IsSmooth (locRepU w (U i) (hst i)) := fun i ψ => by
      have e : {g : GL (Fin (n i)) (w.adicCompletion E) | locRepU w (U i) (hst i) g ψ = ψ} =
          {g | finRep E (n i) (locGL E (n i) w g) ψ.1 = ψ.1} := by
        ext g; exact Subtype.ext_iff
      rw [e]; exact hsm i ψ.1 ψ.2
    have hS' : ∀ i, ∀ x ∈ GlobalTheory.PRep.fixed (locRepU w (U i) (hst i)) (GlobalTheory.LFun.KGL w (n i)), x ≠ 0 →
        GlobalTheory.LFun.IsSatVecGL w (locRepU w (U i) (hst i)) x (S i) := fun i x hx hx0 =>
      GlobalTheory.LFun.IsSatVecGL.of_map (U i).subtype (fun _ _ => rfl) Subtype.val_injective
        (hS i x.1 x.2 (fun k' hk' => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hx k' hk'))
          fun e => hx0 (Subtype.ext e))

    have hcomm : ∀ x : GL (Fin N) (w.adicCompletion E),
        (infGL E N (Unitary.toUnits k) * finGL E N g₀) * finGL E N (locGL E N w x) =
          finGL E N (locGL E N w x) * (infGL E N (Unitary.toUnits k) * finGL E N g₀) := fun x => by
      rw [mul_assoc, ← map_mul, LocSph.comm_locGL w g₀ hy₀ x, map_mul, ← mul_assoc, ← mul_assoc, infGL_comm]
    refine isSatVecGL_of_levi h (X := fun i => U i) (π := fun i => locRepU w (U i) (hst i)) hs S hS'
      (fun i => qU w ((modExp (fun i => Fin (n i)) i : ℂ) / 2)) (fun i => rfl)
      (fun i => evAt (U i) (infGL E (n i) (m i))) (locFn w F y₀) (fun g k' hk' => ?_) (fun u' hu' g => ?_) v
      (fun μ => ?_) hG0
    · show F.1 (y₀ * finGL E N (locGL E N w (g * k'))) = F.1 (y₀ * finGL E N (locGL E N w g))
      rw [map_mul, map_mul, ← mul_assoc]
      exact congrArg (fun φ : Sm E N => φ.1 (y₀ * finGL E N (locGL E N w g))) (hK k' hk')
    · show F.1 (y₀ * finGL E N (locGL E N w (u' * g))) = F.1 (y₀ * finGL E N (locGL E N w g))
      rw [map_mul, map_mul, ← mul_assoc, commute_finGL_locGL w hy₀, mul_assoc]
      exact hu _ (finGL_locGL_mem_unipRad n h w hu') _
    · rw [evT_piTensor_locRepU, ← hv]
      show F.1 (y₀ * finGL E N (locGL E N w (leviEmb (w.adicCompletion E) (stdBlocks n h) μ))) = _
      rw [hy, mul_assoc (u * _), hcomm, finGL_locGL_leviEmb, ← mul_assoc, mul_assoc u, ← map_mul, mul_assoc, hu _ hu₀]
      rfl
  have hL : ∀ (y₀ : GA E N) (g₁ : GL (Fin N) (w.adicCompletion E)),
      locFn w F (y₀ * finGL E N (locGL E N w g₁)) = fun g => locFn w F y₀ (g₁ * g) := fun y₀ g₁ => funext fun g => by
    show F.1 (y₀ * finGL E N (locGL E N w g₁) * finGL E N (locGL E N w g)) =
      F.1 (y₀ * finGL E N (locGL E N w (g₁ * g)))
    rw [map_mul, map_mul, mul_assoc]
  let large₂ : GL (Fin N) (w.adicCompletion E) →
      ((GL (Fin N) (w.adicCompletion E) → ℂ) →ₗ[ℂ] (GL (Fin N) (w.adicCompletion E) → ℂ)) :=
    fun g₁ => LinearMap.funLeft ℂ ℂ (g₁ * ·)
  have hLe : ∀ g₁ x (φ : GL (Fin N) (w.adicCompletion E) → ℂ),
      large₂ g₁ (GlobalTheory.PRep.rightReg ℂ _ ℂ x φ) = GlobalTheory.PRep.rightReg ℂ _ ℂ x (large₂ g₁ φ) := fun g₁ x φ => funext fun g => by
    show φ (g₁ * g * x) = φ (g₁ * (g * x))
    rw [mul_assoc]
  obtain ⟨y, hy⟩ : ∃ y, F.1 y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (Subtype.ext (funext hc))
  obtain ⟨y₀, g₁, hy₀, rfl⟩ := exists_split_at w y
  have hne : locFn w F y₀ ≠ 0 := fun e => hy (congrFun e g₁)
  have hsat := (key y₀ hy₀).resolve_left hne
  refine ⟨h0, GlobalTheory.LGrp.mem_fixed.2 fun k' hk' => hK k' hk', hsat.2.2.1, fun ϖ hϖ j hj => ?_⟩
  refine Subtype.ext (funext fun y' => ?_)
  obtain ⟨y₁, g₂, hy₁, rfl⟩ := exists_split_at w y'
  rw [heckeVec_apply w (GlobalTheory.LFun.Tj_mem_hecke hϖ j)]
  change GlobalTheory.LFun.heckeVec _ _ _ (locFn w F (y₁ * finGL E N (locGL E N w g₂))) 1 =
    GlobalTheory.LFun.satEig (Formalism.UG.qV E w) N Bt j * F.1 (y₁ * finGL E N (locGL E N w g₂))
  rw [hL, show (fun g => locFn w F y₁ (g₂ * g)) = large₂ g₂ (locFn w F y₁) from rfl,
    ← GlobalTheory.LFun.map_heckeVec (Formalism.UG.Final.GLintComm E w N) (GlobalTheory.LFun.Tj_mem_hecke hϖ j) (large₂ g₂) (hLe g₂)]
  show GlobalTheory.LFun.heckeVec _ _ _ (locFn w F y₁) (g₂ * 1) = _
  rcases key y₁ hy₁ with h1 | h1
  · have e0 : F.1 (y₁ * finGL E N (locGL E N w g₂)) = 0 := congrFun h1 g₂
    rw [h1, e0, mul_zero]
    have := (GlobalTheory.LFun.SatCompare.heckeLin (Formalism.UG.Final.GLintComm E w N) (GlobalTheory.LFun.Tj_mem_hecke hϖ j)
      (GlobalTheory.PRep.rightReg ℂ (GL (Fin N) (w.adicCompletion E)) ℂ)).map_zero
    exact congrFun this _
  · rw [h1.2.2.2 ϖ hϖ j hj, mul_one]
    rfl

end PositivityTheory.Rg.Rs.SatakeVectors

end
end
