import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsOver
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjection
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicEigencomponentConjugateForm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.NineStatements GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

section Ip

variable (R : RiemLat E g Λ)

theorem ip_add_right (x y y' : Fin g → ℂ) : R.ip x (y + y') = R.ip x y + R.ip x y' := by
  simp [RiemLat.ip, add_dotProduct]

theorem ip_smul_right (c : ℂ) (x y : Fin g → ℂ) : R.ip x (c • y) = c * R.ip x y := by
  simp [RiemLat.ip, smul_dotProduct]

theorem ip_conj (x y : Fin g → ℂ) : starRingEnd ℂ (R.ip x y) = R.ip y x := by
  show star (y ⬝ᵥ R.Hm *ᵥ star x) = x ⬝ᵥ R.Hm *ᵥ star y
  rw [← star_dotProduct_star, star_mulVec, star_star, R.herm.eq, dotProduct_mulVec]

def ipL (x : Fin g → ℂ) : (Fin g → ℂ) →ₗ[ℂ] ℂ where
  toFun := R.ip x
  map_add' := ip_add_right R x
  map_smul' c y := ip_smul_right R c x y

theorem ip_add_left (x x' y : Fin g → ℂ) : R.ip (x + x') y = R.ip x y + R.ip x' y := by
  rw [← ip_conj R y, ip_add_right, map_add, ip_conj, ip_conj]

theorem ip_smul_left (c : ℂ) (x y : Fin g → ℂ) : R.ip (c • x) y = starRingEnd ℂ c * R.ip x y := by
  rw [← ip_conj R y, ip_smul_right, map_mul, ip_conj]

theorem ip_self_pos {x : Fin g → ℂ} (hx : x ≠ 0) : 0 < (R.ip x x).re := R.pos x hx

theorem ip_self_nonneg (x : Fin g → ℂ) : 0 ≤ (R.ip x x).re := by
  by_cases hx : x = 0
  · subst hx
    simp [RiemLat.ip]
  · exact (ip_self_pos R hx).le

theorem ip_self_eq_zero {x : Fin g → ℂ} (h : R.ip x x = 0) : x = 0 := by
  by_contra hx
  have := ip_self_pos R hx
  rw [h] at this
  simp at this

def TanSp (_ : RiemLat E g Λ) : Type := Fin g → ℂ

instance : AddCommGroup (TanSp R) := inferInstanceAs (AddCommGroup (Fin g → ℂ))

instance : Module ℂ (TanSp R) := inferInstanceAs (Module ℂ (Fin g → ℂ))

def core : InnerProductSpace.Core ℂ (TanSp R) where
  inner x y := R.ip x y
  conj_inner_symm x y := ip_conj R y x
  re_inner_nonneg x := ip_self_nonneg R x
  add_left x y z := ip_add_left R x y z
  smul_left x y r := ip_smul_left R r x y
  definite x h := ip_self_eq_zero R h

theorem ip_cs (x y : Fin g → ℂ) : ‖R.ip x y‖ ^ 2 ≤ (R.ip x x).re * (R.ip y y).re := by
  letI : NormedAddCommGroup (TanSp R) := (core R).toNormedAddCommGroup
  letI : InnerProductSpace ℂ (TanSp R) := InnerProductSpace.ofCore (core R).toCore
  have h1 : ‖(inner ℂ (show TanSp R from x) (show TanSp R from y) : ℂ)‖ ≤ _ := norm_inner_le_norm _ _
  have h2 : (R.ip x x).re = ‖(show TanSp R from x)‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) (show TanSp R from x)
  have h3 : (R.ip y y).re = ‖(show TanSp R from y)‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) (show TanSp R from y)
  have h4 : R.ip x y = (inner ℂ (show TanSp R from x) (show TanSp R from y) : ℂ) := rfl
  rw [h2, h3, h4, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

theorem exists_frame (S : Submodule ℂ (Fin g → ℂ)) (m : ℕ) (h : Module.finrank ℂ S = m) :
    ∃ e : Fin m → Fin g → ℂ, (∀ c, e c ∈ S) ∧
      ∀ x ∈ S, ∀ y ∈ S, ∑ c, starRingEnd ℂ (R.ip (e c) x) * R.ip (e c) y = R.ip x y := by
  letI : NormedAddCommGroup (TanSp R) := (core R).toNormedAddCommGroup
  letI : InnerProductSpace ℂ (TanSp R) := InnerProductSpace.ofCore (core R).toCore
  letI : FiniteDimensional ℂ (TanSp R) := inferInstanceAs (FiniteDimensional ℂ (Fin g → ℂ))
  let S' : Submodule ℂ (TanSp R) := S
  have h' : Module.finrank ℂ S' = m := h
  let b := (stdOrthonormalBasis ℂ S').reindex (finCongr h')
  refine ⟨fun c => ((b c : S') : TanSp R), fun c => (b c).2, fun x hx y hy => ?_⟩
  have key := b.sum_inner_mul_inner (⟨x, hx⟩ : S') (⟨y, hy⟩ : S')
  refine Eq.trans (Finset.sum_congr rfl fun c _ => ?_) key
  exact congrArg (· * R.ip (((b c : S') : TanSp R)) y) (ip_conj R (((b c : S') : TanSp R)) x)

end Ip

section Eig

variable (R : RiemLat E g Λ)

theorem ip_sum_right {A : Type} (t : Finset A) (f : A → Fin g → ℂ) (x : Fin g → ℂ) :
    R.ip x (∑ i ∈ t, f i) = ∑ i ∈ t, R.ip x (f i) := map_sum (ipL R x) f t

theorem ip_sum_left {A : Type} (t : Finset A) (f : A → Fin g → ℂ) (y : Fin g → ℂ) :
    R.ip (∑ i ∈ t, f i) y = ∑ i ∈ t, R.ip (f i) y := by
  rw [← ip_conj R y, ip_sum_right, map_sum]
  exact Finset.sum_congr rfl fun i _ => ip_conj R y (f i)

theorem mem_eigSp_iff' {s : 𝓞 E →+* ℂ} {x : Fin g → ℂ} : x ∈ eigSp R.B s ↔ ∀ a, R.B a x = s a • x := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

omit [IsCMField E] in

theorem comp_ne {s s' : E →+* ℂ} (h : s ≠ s') :
    s.comp (algebraMap (𝓞 E) E) ≠ s'.comp (algebraMap (𝓞 E) E) :=
  fun e => h (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) e)

omit [IsCMField E] in

theorem emb_injective (s : 𝓞 E →+* ℂ) : Function.Injective s := by
  have hc : (RingHom.ker s).comap (algebraMap ℤ (𝓞 E)) = ⊥ := by
    rw [RingHom.comap_ker]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (RingHom.injective_int _)
  exact (RingHom.injective_iff_ker_eq_bot s).2 (Ideal.eq_bot_of_comap_eq_bot hc)

def extEmb (s : 𝓞 E →+* ℂ) : E →+* ℂ := IsFractionRing.lift (emb_injective s)

omit [IsCMField E] in
theorem extEmb_apply (s : 𝓞 E →+* ℂ) (a : 𝓞 E) : extEmb s (algebraMap (𝓞 E) E a) = s a :=
  IsFractionRing.lift_algebraMap (emb_injective s) a

omit [IsCMField E] in
theorem extEmb_comp (s : 𝓞 E →+* ℂ) : (extEmb s).comp (algebraMap (𝓞 E) E) = s :=
  RingHom.ext (extEmb_apply s)




open Classical in

def frame (s : 𝓞 E →+* ℂ) (m : ℕ) : Fin m → Fin g → ℂ :=
  if h : Module.finrank ℂ (eigSp R.B s) = m then (exists_frame R _ m h).choose else 0


def lieOf (s : 𝓞 E →+* ℂ) (m : ℕ) (v : Λ) : Fin m → ℂ :=
  fun c => R.ip (frame R s m c) (eigComp R.B s (R.P v))





def lieL (s : 𝓞 E →+* ℂ) (m : ℕ) : (Fin g → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
  LinearMap.pi fun c => ipL R (frame R s m c)


end Eig

theorem gram_unit {F₀ : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ} (h : Function.Bijective F₀) {n : ℕ}
    (b : Module.Basis (Fin n) ℤ Λ) : IsUnit (Matrix.of fun a c => F₀ (b a) (b c)).det := by
  have hu := LinearEquiv.isUnit_det (LinearEquiv.ofBijective F₀ h) b b.dualBasis
  have e : LinearMap.toMatrix b b.dualBasis (LinearEquiv.ofBijective F₀ h : Λ →ₗ[ℤ] (Λ →ₗ[ℤ] ℤ)) =
      (Matrix.of fun a c => F₀ (b a) (b c))ᵀ := by
    ext i j
    simp [LinearMap.toMatrix_apply]
  rw [e, Matrix.det_transpose] at hu
  exact hu

section Family

variable {K : Type} {J : K → Type} {Ψ : Type}

open Classical in

def normFam (T : Set ((Σ k, J k) → ℂ)) (R : ((Σ k, J k) → ℂ) → RiemLat E g Λ) (w : (Σ k, J k) → ℂ) (v : Λ) : ℝ :=
  if w ∈ T then (R w).normSq v else 0

open Classical in

def lieFam (T : Set ((Σ k, J k) → ℂ)) (R : ((Σ k, J k) → ℂ) → RiemLat E g Λ) (emb : Ψ → (𝓞 E →+* ℂ)) (m : ℕ)
    (w : (Σ k, J k) → ℂ) (τ : Ψ) (v : Λ) : Fin m → ℂ :=
  if w ∈ T then lieOf (R w) (emb τ) m v else 0

variable {T : Set ((Σ k, J k) → ℂ)} {R : ((Σ k, J k) → ℂ) → RiemLat E g Λ} {w : (Σ k, J k) → ℂ}





theorem form_sq_le (R : RiemLat E g Λ) (v v' : Λ) :
    ((R.form v v' : ℤ) : ℝ) ^ 2 ≤ R.normSq v * R.normSq v' := by
  have h := R.im v v'
  have cs := ip_cs R (R.P v') (R.P v)
  have e : R.P v ⬝ᵥ R.Hm *ᵥ star (R.P v') = R.ip (R.P v') (R.P v) := rfl
  rw [e] at h
  rw [← h]
  have h2 : (R.ip (R.P v') (R.P v)).im ^ 2 ≤ ‖R.ip (R.P v') (R.P v)‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [mul_self_nonneg (R.ip (R.P v') (R.P v)).re]
  have e2 : R.normSq v * R.normSq v' = (R.ip (R.P v') (R.P v')).re * (R.ip (R.P v) (R.P v)).re := mul_comm _ _
  rw [e2]
  exact h2.trans cs

theorem normSq_pos' (R : RiemLat E g Λ) {v : Λ} (hv : v ≠ 0) : 0 < R.normSq v := by
  obtain ⟨h1, -⟩ := GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R
  exact R.pos (R.P v) fun h0 => hv (h1 (by rw [h0, map_zero]))


end Family


end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.Lin
