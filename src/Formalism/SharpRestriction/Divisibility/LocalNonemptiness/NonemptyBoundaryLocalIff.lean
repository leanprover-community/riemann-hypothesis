import Formalism.SharpRestriction.Divisibility.BoundaryLocalData

noncomputable section

namespace Formalism.MainNotions.DIV.Inh

open Formalism.BasicNotions NumberField Formalism.MainNotions

def integersConjugation (D : D7) : 𝓞 D.host.E →+* 𝓞 D.host.E :=
  RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)

theorem integers_conjugation_coe (D : D7) (c : 𝓞 D.host.E) : ((integersConjugation D c : 𝓞 D.host.E) : D.host.E) = D.host.conj (c : D.host.E) := rfl

def XT (_D : D7) (Y : Type) : Type := Y

instance (D : D7) (Y : Type) [AddCommGroup Y] : AddCommGroup (XT D Y) := inferInstanceAs (AddCommGroup Y)

instance (D : D7) (Y : Type) [AddCommGroup Y] [Module (𝓞 D.host.E) Y] : Module (𝓞 D.host.E) (XT D Y) :=
  Module.compHom Y (integersConjugation D)

def XT.mk (D : D7) (Y : Type) [AddCommGroup Y] : Y ≃+ XT D Y := AddEquiv.refl Y

theorem XT.smul_mk (D : D7) {Y : Type} [AddCommGroup Y] [Module (𝓞 D.host.E) Y] (c : 𝓞 D.host.E) (a : Y) :
    c • XT.mk D Y a = XT.mk D Y (integersConjugation D c • a) := rfl

theorem XT.symm_smul (D : D7) {Y : Type} [AddCommGroup Y] [Module (𝓞 D.host.E) Y] (c : 𝓞 D.host.E) (χ : XT D Y) :
    (XT.mk D Y).symm (c • χ) = integersConjugation D c • (XT.mk D Y).symm χ := rfl

def vHom (p : ℕ) (C : Type) [NormedField C] : Additive Cˣ →+ ℝ where
  toFun u := BoundaryLocalData.vU p (Additive.toMul u)
  map_zero' := by simp [BoundaryLocalData.vU]
  map_add' u v := by
    simp only [BoundaryLocalData.vU, toMul_add, Units.val_mul, norm_mul]
    rw [Real.logb_mul (by simp) (by simp)]
    ring

theorem exists_section (p : ℕ) {C : Type} [NormedField C] (M : Submodule ℤ ℝ) [Module.Finite ℤ M]
    (hM : ∀ m ∈ M, ∃ u : Additive Cˣ, vHom p C u = m) :
    ∃ s : M →ₗ[ℤ] Additive Cˣ, ∀ m : M, vHom p C (s m) = m := by
  classical
  haveI : Module.Free ℤ M := by
    first
    | exact Module.free_of_finite_type_torsion_free'
    | infer_instance
  let b := Module.Free.chooseBasis ℤ M
  choose u hu using fun i => hM _ (b i).2
  refine ⟨b.constr ℤ u, fun m => ?_⟩
  have key : (vHom p C).toIntLinearMap ∘ₗ b.constr ℤ u = M.subtype :=
    b.ext fun i => by simp [hu]
  simpa using LinearMap.congr_fun key m

theorem exists_tau (p : ℕ) {C : Type} [NormedField C] {Y : Type} [AddCommGroup Y] [Module.Finite ℤ Y]
    (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (h : ∀ a b, ∃ u : Cˣ, β a b = BoundaryLocalData.vU p u) :
    ∃ t : Y → Y → Cˣ, (∀ a a' b, t (a + a') b = t a b * t a' b) ∧ (∀ a b b', t a (b + b') = t a b * t a b') ∧
      (∀ a b a' b', β a b = β a' b' → t a b = t a' b') ∧ ∀ a b, β a b = BoundaryLocalData.vU p (t a b) := by
  classical
  have key : ∀ x : TensorProduct ℤ Y Y, ∃ u : Additive Cˣ, vHom p C u = TensorProduct.lift β x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
    | tmul a b =>
      obtain ⟨u, hu⟩ := h a b
      exact ⟨Additive.ofMul u, by rw [TensorProduct.lift.tmul, hu]; rfl⟩
    | add x y hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨v, hv⟩ := hy
      exact ⟨u + v, by rw [map_add, map_add, hu, hv]⟩
  have hM : ∀ m ∈ LinearMap.range (TensorProduct.lift β), ∃ u : Additive Cˣ, vHom p C u = m := by
    rintro m ⟨x, rfl⟩
    exact key x
  obtain ⟨s, hs⟩ := exists_section (C := C) p _ hM
  have mem : ∀ a b, β a b ∈ LinearMap.range (TensorProduct.lift β) :=
    fun a b => ⟨a ⊗ₜ b, TensorProduct.lift.tmul _ _⟩
  refine ⟨fun a b => Additive.toMul (s ⟨β a b, mem a b⟩), ?_, ?_, ?_, ?_⟩
  · intro a a' b
    have e : (⟨β (a + a') b, mem _ _⟩ : LinearMap.range (TensorProduct.lift β)) =
        ⟨β a b, mem a b⟩ + ⟨β a' b, mem a' b⟩ := Subtype.ext (by simp)
    show Additive.toMul (s ⟨β (a + a') b, mem _ _⟩) =
      Additive.toMul (s ⟨β a b, mem a b⟩) * Additive.toMul (s ⟨β a' b, mem a' b⟩)
    first
    | (rw [e, map_add]; rfl)
    | (rw [e, map_add, toMul_add])
    | (simp only [e, map_add]; rfl)
  · intro a b b'
    have e : (⟨β a (b + b'), mem _ _⟩ : LinearMap.range (TensorProduct.lift β)) =
        ⟨β a b, mem a b⟩ + ⟨β a b', mem a b'⟩ := Subtype.ext (by simp)
    show Additive.toMul (s ⟨β a (b + b'), mem _ _⟩) =
      Additive.toMul (s ⟨β a b, mem a b⟩) * Additive.toMul (s ⟨β a b', mem a b'⟩)
    first
    | (rw [e, map_add]; rfl)
    | (rw [e, map_add, toMul_add])
    | (simp only [e, map_add]; rfl)
  · intro a b a' b' hab
    have e : (⟨β a b, mem a b⟩ : LinearMap.range (TensorProduct.lift β)) = ⟨β a' b', mem a' b'⟩ :=
      Subtype.ext hab
    show Additive.toMul (s ⟨β a b, mem a b⟩) = Additive.toMul (s ⟨β a' b', mem a' b'⟩)
    rw [e]
  · intro a b
    show β a b = BoundaryLocalData.vU p (Additive.toMul (s ⟨β a b, mem a b⟩))
    have hab := (hs ⟨β a b, mem a b⟩).symm
    first
    | exact hab
    | (simp only [vHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hab; exact hab)
    | (rw [hab]; rfl)

theorem exists_lin {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] {v : V}
    (hv : v ≠ 0) (w : W) : ∃ f : V →ₗ[K] W, f v = w := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K V, φ v ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hv
    first
    | exact (Module.forall_dual_apply_eq_zero_iff K v).1 hc
    | exact (Module.forall_dual_apply_eq_zero_iff v).1 hc
  refine ⟨(φ v)⁻¹ • φ.smulRight w, ?_⟩
  simp [LinearMap.smulRight_apply, smul_smul, inv_mul_cancel₀ hφ]

theorem exists_alp (D : D7) (p n : ℕ) (h : ModuliIntegralCharts.NHyp D p n) : ∃ α : 𝓞 D.host.E,
    (α : D.host.E) * D.host.conj (α : D.host.E) = (n : D.host.E) ∧
    ((∃ mm : ℕ, n = mm ^ 2 ∧ α = (mm : 𝓞 D.host.E)) ∨ (α : D.host.E) ∈ D.host.K) := by
  obtain ⟨-, -, h⟩ := h
  rcases h with ⟨mm, rfl⟩ | ⟨π, hK, hπ⟩
  · refine ⟨(mm : 𝓞 D.host.E), ?_, Or.inl ⟨mm, rfl, rfl⟩⟩
    have h1 : ((mm : 𝓞 D.host.E) : D.host.E) = (mm : D.host.E) := by
      first
      | simp
      | norm_cast
    rw [h1, map_natCast]
    push_cast
    ring
  · exact ⟨π, hπ, Or.inr hK⟩

structure LocBHyp (D : D7) {r j p : ℕ} (L : ModuliIntegralCharts.Loc D r j p) : Prop where

  be_val : ∀ (Z : L.Mdl) (y : L.Pt Z) (a b : L.Ylat y), ∃ u : ((L.fld y).C)ˣ, L.be y a b = BoundaryLocalData.vU p u

  psiV_val : ∀ (Z : L.Mdl) (y : L.Pt Z) (a : L.Ylat y), ∃ u : ((L.fld y).C)ˣ, L.psiV y a = BoundaryLocalData.vU p u

  oX : ∃ O : L.Sh L.Xm, L.IsInv O ∧ ∀ (F : L.Sh L.Xm) (φ : L.GIso O F), ∃ s : L.Sec F,
    ∀ y, L.nrm F s y = (p : ℝ) ^ (-(L.vrat φ y))

  keySh_inv : L.IsInv L.piPP → ∀ c, L.IsInv (L.keySh c)

  dP_le : ∀ y : L.Pt L.Xm, L.dP y ≤ D.R.f * r

  th_ne : ∀ y nW, (∃ s : L.Sn y (L.latStd nW) 1, s ≠ 0) ∨
    ∀ n, ModuliIntegralCharts.NHyp D p n → L.vth y (L.latStd nW) n = 0

  intJet_free : ∀ y nW n DF, ∃ (N : ℕ) (b : Module.Basis (Fin N) (L.fld y).C (L.Jet y (L.latStd nW) n DF)),
    ∀ v, v ∈ L.intJet y (L.latStd nW) n DF ↔ ∀ i, ‖b.repr v i‖ ≤ 1





end Formalism.MainNotions.DIV.Inh

end
