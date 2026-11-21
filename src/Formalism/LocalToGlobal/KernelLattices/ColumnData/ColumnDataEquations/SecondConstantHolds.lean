import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.HenselQuad
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.CharSingle
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.JNoEig
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.MemSmulLat
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.EqPOf
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.StarSqrtNeg

section
noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J

open Formalism.L2.PairingIndexBounds.Eq.J Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Car}

def NegOneNorm (D : Car) : Prop :=
  ∀ m : ℕ, 0 < m → ∃ lam s : 𝓞 D.host.E, star (s : D.host.E) = (s : D.host.E) ∧
    star (lam : D.host.E) * (lam : D.host.E) = -1 + (m : D.host.E) * (s : D.host.E)

def mulO (N N' : ℕ) (r : D.host.E) : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N' where
  toFun z := fun τ i j => TaylorLogMetric.embT D τ r * z τ i j
  map_add' x y := by funext τ i j; exact mul_add _ _ _
  map_smul' c x := by funext τ i j; exact mul_left_comm _ _ _

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Cd.Base D cc δ)

theorem mul_integer_mem_base_lattice {N N' : ℕ} (r : 𝓞 D.host.E) {x : TaylorLogMetric.VC D N N'} (hx : x ∈ La0 B N N') :
    mulO N N' (r : D.host.E) x ∈ La0 B N N' := by
  have hle : La0 B N N' ≤ (La0 B N N').comap (mulO N N' (r : D.host.E)).toAddMonoidHom := by
    show TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') ≤
      (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')).comap (mulO N N' (r : D.host.E)).toAddMonoidHom
    rw [TaylorLogMetric.La, AddSubgroup.closure_le]
    rintro _ ⟨w, hw, A, hA, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap]
    apply AddSubgroup.subset_closure
    refine ⟨w, hw, r • A, Submodule.smul_mem _ r hA, ?_⟩
    funext τ i j
    simp [mulO, TaylorLogMetric.embV, TaylorLogMetric.tor0, Algebra.smul_def, map_mul]
    ring
  exact hle hx

theorem star_int (r : 𝓞 D.host.E) : ∃ r' : 𝓞 D.host.E, (r' : D.host.E) = star (r : D.host.E) :=
  ⟨⟨star (r : D.host.E), by
    have h := (NumberField.RingOfIntegers.isIntegral_coe r).map (starRingEnd D.host.E).toIntAlgHom
    first
      | exact (mem_integralClosure_iff ℤ D.host.E).mpr h
      | exact h⟩, rfl⟩

theorem mulO_phi {N N' : ℕ} (r : D.host.E) (γ : Matrix.unitaryGroup (Fin N) D.host.E)
    (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (x : TaylorLogMetric.VC D N N') :
    mulO N N' r (phiU γ γ' x) = phiU γ γ' (mulO N N' r x) := by
  funext τ i j
  show TaylorLogMetric.embT D τ r * (gM (γ' : Matrix (Fin N') (Fin N') D.host.E) τ * Matrix.of (x τ) *
      (gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ) i j =
    (gM (γ' : Matrix (Fin N') (Fin N') D.host.E) τ * Matrix.of (fun i j => TaylorLogMetric.embT D τ r * x τ i j) *
      (gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ) i j
  have h1 : Matrix.of (fun i j => TaylorLogMetric.embT D τ r * x τ i j) = TaylorLogMetric.embT D τ r • Matrix.of (x τ) := by
    ext a b
    simp
  rw [h1, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]

theorem mulO_adj (A : ℝ) {N N' : ℕ} (r : D.host.E) (x y : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' (mulO N N' r x) y = Ker.formV A D.what₂.Tau N N' x (mulO N N' (star r) y) := by
  simp only [Formalism.L2.Ker.formV, LinearMap.mk₂'ₛₗ_apply, mulO, LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, embT_star', Complex.star_def, Complex.conj_conj]
  ring

theorem gaussRow_of (hS : B.StdOK) (hL : B.LatAll) (hNeg : NegOneNorm D) : GaussRow B := by
  intro N γ Ae₁ hN hA₁ S hS₁
  have hfix₁ : ∀ y : TaylorLogMetric.VC D N 1, (phiU γ 1 : TaylorLogMetric.VC D N 1 ≃ₗ[ℂ] TaylorLogMetric.VC D N 1).symm y = y → y = 0 := by
    intro y hy
    apply Ae₁.injective
    rw [hA₁, hy, sub_self, map_zero]
  have hfix : ∀ x : TaylorLogMetric.VC D N 2, (phiU γ 1 : TaylorLogMetric.VC D N 2 ≃ₗ[ℂ] TaylorLogMetric.VC D N 2).symm x = x → x = 0 := by
    intro x hx
    apply (rowE D N 2).injective
    funext i
    rw [map_zero]
    refine hfix₁ _ ?_
    rw [← symm_coord (rowE D N 2) _ _ (map_row γ), hx]
  obtain ⟨Ae, hA⟩ := exists_cay (phiU γ 1 : TaylorLogMetric.VC D N 2 ≃ₗ[ℂ] TaylorLogMetric.VC D N 2) hfix
  have c : Copies (rowE D N 2) (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N 2)
      (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N 1) (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)) (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ))
      (La0 B N 2) (La0 B N 1) (phiU γ 1) Ae (phiU γ 1) Ae₁ :=
    { form := form_row _ N 2
      char := al_row B hS N 2
      lat := lat_row B N 2
      map := map_row γ
      cay := fun x i => by
        rw [hA, hA₁, map_sub, Pi.sub_apply, symm_coord (rowE D N 2) _ _ (map_row γ)] }
  have hal0 : TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (0 : TaylorLogMetric.VC D N 1) = 1 := by
    unfold TaylorLogMetric.al TaylorLogMetric.Hf
    simp
  have hU₁ := c.unitaryData₁ 0 (unitaryData hL hN (by decide) γ 1 Ae hA) (formV_herm' _ _ _ _)
    (formV_pos (area_pos' B) _ _ _) (phiL_isom _ _ _ _ _ _ _) hA₁ hal0 (al_phi _ _ _ _ _ _)
  have hcard : 0 < S.card := by
    obtain ⟨x, hx, -⟩ := hS₁.2.2 0 (AddSubgroup.zero_mem _)
    exact Finset.card_pos.mpr ⟨x, hx⟩
  obtain ⟨lam, s, hs, hrel⟩ := hNeg (4 * S.card) (by omega)
  obtain ⟨lam', hlam'⟩ := star_int lam
  have hM : Multipliers (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N 1) (La0 B N 1) (phiU γ 1)
      (mulO N 1 (lam : D.host.E)) (mulO N 1 (star (lam : D.host.E))) (mulO N 1 (s : D.host.E)) S.card :=
    { lΛ := fun x hx => mul_integer_mem_base_lattice B lam hx
      l'Λ := fun x hx => by rw [← hlam']; exact mul_integer_mem_base_lattice B lam' hx
      sΛ := fun x hx => mul_integer_mem_base_lattice B s hx
      lδ := mulO_phi _ γ 1
      l'δ := mulO_phi _ γ 1
      sδ := mulO_phi _ γ 1
      adj := mulO_adj _ _
      sadj := fun x y => by rw [mulO_adj, hs]
      rel := fun x => by
        funext τ i j
        show TaylorLogMetric.embT D τ (star (lam : D.host.E)) * (TaylorLogMetric.embT D τ (lam : D.host.E) * x τ i j) =
          -x τ i j + (4 * S.card) • (TaylorLogMetric.embT D τ (s : D.host.E) * x τ i j)
        rw [← mul_assoc, ← map_mul, hrel, map_add, map_neg, map_one, map_mul, map_natCast, nsmul_eq_mul]
        ring }
  exact gauss_sq hU₁ hM (fun x hx => card_smul_mem hS₁ hx)
    (fun x hx => alpha_mult hM (Real.sqrt D.host.d / 2) _ (fun _ => rfl) (B.qInt0 hS N 1) hx) hS₁

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J
end
end

section
noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J

open Formalism.L2.PairingIndexBounds.Eq.J Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq

section Gen

variable {n : Type} [Fintype n]

def inj0 (n : Type) : (n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ) where
  toFun x := fun w => if w.1 = 0 then x w.2 else 0
  map_add' x y := by funext w; by_cases h : w.1 = 0 <;> simp [h]
  map_smul' c x := by funext w; by_cases h : w.1 = 0 <;> simp [h]

def sl0 (n : Type) : (Fin 4 × n → ℂ) →ₗ[ℂ] (n → ℂ) where
  toFun z := slice 0 z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem slice_zero_injection (x : n → ℂ) (a : Fin 4) : slice a (inj0 n x) = if a = 0 then x else 0 := by
  funext i
  by_cases h : a = 0 <;> simp [slice, inj0, h]

theorem zero_injection_mem_fourth_power (ΛM : AddSubgroup (n → ℂ)) {x : n → ℂ} (hx : x ∈ ΛM) : inj0 n x ∈ pow4 ΛM := by
  intro a
  rw [slice_zero_injection]
  split_ifs
  · exact hx
  · exact ΛM.zero_mem

theorem is_lattice_of_fourth_power (ΛM : AddSubgroup (n → ℂ)) (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ))
    (h : IsLat (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 ΛM))) : IsLat ΛM := by
  obtain ⟨hd, hs⟩ := h
  refine ⟨?_, ?_⟩
  · haveI := hd
    let φ : ΛM → imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 ΛM) :=
      fun x => ⟨g (inj0 n x), ⟨inj0 n x, zero_injection_mem_fourth_power ΛM x.2, rfl⟩⟩
    have hφc : Continuous φ := by
      apply Continuous.subtype_mk
      exact ((g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)).comp (inj0 n)).continuous_of_finiteDimensional.comp
        continuous_subtype_val
    have hφi : Function.Injective φ := by
      intro x y hxy
      have h1 := congrArg Subtype.val hxy
      have h2 := g.injective h1
      apply Subtype.ext
      have h3 := congrArg (slice 0) h2
      rwa [slice_zero_injection, slice_zero_injection, if_pos rfl, if_pos rfl] at h3
    exact DiscreteTopology.of_continuous_injective hφc hφi
  · rw [eq_top_iff]
    intro x _
    let G : (Fin 4 × n → ℂ) →ₗ[ℝ] (n → ℂ) := ((sl0 n).comp g.symm.toLinearMap).restrictScalars ℝ
    have hG : ∀ y ∈ (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 ΛM) : Set _), G y ∈ ΛM := by
      rintro _ ⟨z, hz, rfl⟩
      show slice 0 (g.symm (g z)) ∈ ΛM
      rw [g.symm_apply_apply]
      exact hz 0
    have hmap : Submodule.map G (Submodule.span ℝ
        (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 ΛM) : Set _)) ≤
        Submodule.span ℝ (ΛM : Set (n → ℂ)) := by
      rw [Submodule.map_span]
      exact Submodule.span_mono (by rintro _ ⟨y, hy, rfl⟩; exact hG y hy)
    rw [hs, Submodule.map_top] at hmap
    apply hmap
    refine ⟨g (inj0 n x), ?_⟩
    show slice 0 (g.symm (g (inj0 n x))) = x
    rw [g.symm_apply_apply, slice_zero_injection, if_pos rfl]

def putL (n : Type) (N N' : ℕ) (k : Fin N' × Fin N) : (n → ℂ) →ₗ[ℂ] (n → Fin N' → Fin N → ℂ) where
  toFun x := fun τ i j => if (i, j) = k then x τ else 0
  map_add' x y := by funext τ i j; by_cases h : (i, j) = k <;> simp [h]
  map_smul' c x := by funext τ i j; by_cases h : (i, j) = k <;> simp [h]

theorem putL_mem (ΛM : AddSubgroup (n → ℂ)) (N N' : ℕ) (k : Fin N' × Fin N) {x : n → ℂ} (hx : x ∈ ΛM) :
    putL n N N' k x ∈ Ker.powLat ΛM N N' := by
  intro i j
  by_cases h : (i, j) = k
  · have e : (fun τ => putL n N N' k x τ i j) = x := by
      funext τ
      simp [putL, h]
    rw [e]
    exact hx
  · have e : (fun τ => putL n N N' k x τ i j) = 0 := by
      funext τ
      simp [putL, h]
    rw [e]
    exact ΛM.zero_mem

theorem sum_putL (N N' : ℕ) (z : n → Fin N' → Fin N → ℂ) :
    z = ∑ k : Fin N' × Fin N, putL n N N' k (fun τ => z τ k.1 k.2) := by
  funext τ i j
  simp [putL, Finset.sum_apply]

theorem isLat_powLat (ΛM : AddSubgroup (n → ℂ)) (h : IsLat ΛM) (N N' : ℕ) : IsLat (Ker.powLat ΛM N N') := by
  obtain ⟨hd, hs⟩ := h
  refine ⟨?_, ?_⟩
  · haveI := hd
    let ψ : Ker.powLat ΛM N N' → (Fin N' × Fin N → ΛM) :=
      fun z k => ⟨fun τ => z.1 τ k.1 k.2, z.2 k.1 k.2⟩
    have hψc : Continuous ψ := by
      apply continuous_pi
      intro k
      apply Continuous.subtype_mk
      apply continuous_pi
      intro τ
      have hc : Continuous (fun z : Ker.powLat ΛM N N' => (z : n → Fin N' → Fin N → ℂ)) :=
        continuous_subtype_val
      have hc1 : Continuous (fun z : Ker.powLat ΛM N N' => (z : n → Fin N' → Fin N → ℂ) τ) :=
        (continuous_apply τ).comp hc
      have hc2 : Continuous (fun z : Ker.powLat ΛM N N' => (z : n → Fin N' → Fin N → ℂ) τ k.1) :=
        (continuous_apply k.1).comp hc1
      exact (continuous_apply k.2).comp hc2
    have hψi : Function.Injective ψ := by
      intro x y hxy
      apply Subtype.ext
      funext τ i j
      have h1 := congrArg (fun f => ((f (i, j) : ΛM) : n → ℂ) τ) hxy
      exact h1
    exact DiscreteTopology.of_continuous_injective hψc hψi
  · rw [eq_top_iff]
    intro z _
    rw [sum_putL N N' z]
    refine Submodule.sum_mem _ fun k _ => ?_
    have hk : (fun τ => z τ k.1 k.2) ∈ Submodule.span ℝ (ΛM : Set (n → ℂ)) := by
      rw [hs]
      trivial
    have hmap : Submodule.map ((putL n N N' k).restrictScalars ℝ) (Submodule.span ℝ (ΛM : Set (n → ℂ))) ≤
        Submodule.span ℝ (Ker.powLat ΛM N N' : Set _) := by
      rw [Submodule.map_span]
      exact Submodule.span_mono (by rintro _ ⟨y, hy, rfl⟩; exact putL_mem ΛM N N' k hy)
    exact hmap ⟨_, hk, rfl⟩

end Gen

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {B : Cd.Base D cc δ}

theorem isLat_lamM (hS : B.StdOK) : IsLat B.lamM := by
  unfold Formalism.L2.Ker.Cd.Base.StdOK Formalism.L2.Ker.StdOK at hS
  have hI : IsLat (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)) :=
    Formalism.L2.Th1.H.KR.isLat_of_comm (Formalism.L2.Th1.H.KR.isLat_stdLat B.L _) hS.idx₂ hS.idx₁
  exact is_lattice_of_fourth_power B.lamM B.gC hI

theorem lat0IsLat (hS : B.StdOK) (N N' : ℕ) : Lat0IsLat B N N' := by
  unfold Lat0IsLat La0
  rw [Formalism.L2.Ker.Cd.Lat0 (D := D) (N := N) (N' := N') cc δ]
  exact isLat_powLat _ (isLat_lamM hS) N N'

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J
end
end

section
noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J

open Formalism.L2.PairingIndexBounds.Eq.J Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq Formalism.L2.Ker

section Gen

variable {n : Type} [Fintype n] [DecidableEq n] {N N' : ℕ}

def ent (k : Fin N' × Fin N) (z : n → Fin N' → Fin N → ℂ) : n → ℂ := fun τ => z τ k.1 k.2

def setE (z : n → Fin N' → Fin N → ℂ) (k : Fin N' × Fin N) (w : n → ℂ) : n → Fin N' → Fin N → ℂ :=
  fun τ i j => if (i, j) = k then w τ else z τ i j

def repl (a : n → ℂ) (s : Finset (Fin N' × Fin N)) (z : n → Fin N' → Fin N → ℂ) : n → Fin N' → Fin N → ℂ :=
  fun τ i j => if (i, j) ∈ s then a τ else z τ i j

omit [Fintype n] [DecidableEq n] in
theorem ent_putL (k p : Fin N' × Fin N) (x : n → ℂ) : ent p (putL n N N' k x) = if p = k then x else 0 := by
  funext τ
  by_cases h : p = k
  · subst h
    simp [ent, putL]
  · simp [ent, putL, h]

omit [Fintype n] [DecidableEq n] in
theorem ent_setE (z : n → Fin N' → Fin N → ℂ) (k : Fin N' × Fin N) (w : n → ℂ) : ent k (setE z k w) = w := by
  funext τ
  simp [ent, setE]

omit [Fintype n] [DecidableEq n] in
theorem setE_ent (z : n → Fin N' → Fin N → ℂ) (k : Fin N' × Fin N) : setE z k (ent k z) = z := by
  funext τ i j
  unfold setE ent
  split_ifs with h
  · rw [← h]
  · rfl

omit [Fintype n] [DecidableEq n] in
theorem setE_add (z : n → Fin N' → Fin N → ℂ) (k : Fin N' × Fin N) (w x : n → ℂ) :
    setE z k w + putL n N N' k x = setE z k (w + x) := by
  funext τ i j
  by_cases h : (i, j) = k <;> simp [setE, putL, h]

theorem form_put (L : PeriodPair) (y : n → Fin N' → Fin N → ℂ) (k : Fin N' × Fin N) (x : n → ℂ) :
    formV (Formalism.L2.Th1.F.area L) n N N' y (putL n N N' k x) = matH (hOne L n) (ent k y) x := by
  have hs : ∀ τ, (∑ i, ∑ j, y τ i j * conj (if (i, j) = k then x τ else 0)) = y τ k.1 k.2 * conj (x τ) := by
    intro τ
    rw [Finset.sum_eq_single k.1, Finset.sum_eq_single k.2]
    · simp
    · intro j _ hj
      simp [Prod.ext_iff, hj]
    · simp
    · intro i _ hi
      apply Finset.sum_eq_zero
      intro j _
      simp [Prod.ext_iff, hi]
    · simp
  show (∑ τ, ∑ i, ∑ j, y τ i j * conj ((putL n N N' k x) τ i j)) / ((Formalism.L2.Th1.F.area L : ℝ) : ℂ) =
    ∑ i, ∑ j, ent k y i * hOne L n i j * conj (x j)
  simp only [putL, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [hs]
  simp only [hOne, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, ent]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  ring

theorem alphaQ_put (c : ℝ) (L : PeriodPair) (k : Fin N' × Fin N) (x : n → ℂ) :
    alphaQ c (formV (Formalism.L2.Th1.F.area L) n N N') (putL n N N' k x) = alphaQ c (matH (hOne L n)) x := by
  unfold alphaQ qOf
  rw [form_put, ent_putL, if_pos rfl]

theorem oneEntry_mem (c : ℝ) (L : PeriodPair) (ΛM : AddSubgroup (n → ℂ)) {F : (n → Fin N' → Fin N → ℂ) → ℂ}
    (hF : F ∈ Formalism.L2.Th1.H.Th (formV (Formalism.L2.Th1.F.area L) n N N') (alphaQ c (formV (Formalism.L2.Th1.F.area L) n N N'))
      (powLat ΛM N N')) (z : n → Fin N' → Fin N → ℂ) (k : Fin N' × Fin N) :
    (fun w => F (setE z k w)) ∈ Formalism.L2.Th1.H.Th (matH (hOne L n)) (alphaQ c (matH (hOne L n))) ΛM := by
  refine ⟨fun w _ => ?_, fun x hx w => ?_⟩
  · have e : (fun w => F (setE z k w)) = fun w => F (setE z k 0 + putL n N N' k w) := by
      funext w'
      rw [setE_add, zero_add]
    rw [e]
    exact AnalyticAt.comp (g := F) (f := fun w => setE z k 0 + putL n N N' k w) (hF.1 _ (Set.mem_univ _))
      (analyticAt_const.add ((LinearMap.toContinuousLinearMap (putL n N N' k)).analyticAt w))
  · have hX : putL n N N' k x ∈ powLat ΛM N N' := by
      intro i j
      by_cases h : (i, j) = k
      · simp only [putL, LinearMap.coe_mk, AddHom.coe_mk, h, if_true]
        exact hx
      · simp only [putL, LinearMap.coe_mk, AddHom.coe_mk, h, if_false]
        exact ΛM.zero_mem
    have h := hF.2 (putL n N N' k x) hX (setE z k w)
    simp only [Formalism.L2.Th1.H.opU] at h ⊢
    rw [setE_add, form_put, form_put, ent_setE, ent_putL, if_pos rfl, alphaQ_put] at h
    exact h

theorem tens_spans (c : ℝ) (L : PeriodPair) (ΛM : AddSubgroup (n → ℂ)) {θ : (n → ℂ) → ℂ} (hθ0 : θ ≠ 0)
    (hline : ∀ G ∈ Formalism.L2.Th1.H.Th (matH (hOne L n)) (alphaQ c (matH (hOne L n))) ΛM, ∃ a : ℂ, G = a • θ)
    (N N' : ℕ) :
    ∀ F ∈ Formalism.L2.Th1.H.Th (formV (Formalism.L2.Th1.F.area L) n N N') (alphaQ c (formV (Formalism.L2.Th1.F.area L) n N N'))
      (powLat ΛM N N'), ∃ a : ℂ, F = a • tensPow θ N N' := by
  intro F hF
  obtain ⟨a₀, ha₀⟩ : ∃ a₀, θ a₀ ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hθ0 (funext hno)
  have step : ∀ (z : n → Fin N' → Fin N → ℂ) (k : Fin N' × Fin N),
      F z * θ a₀ = F (setE z k a₀) * θ (ent k z) := by
    intro z k
    obtain ⟨a, ha⟩ := hline _ (oneEntry_mem c L ΛM hF z k)
    have h1 : F (setE z k (ent k z)) = a * θ (ent k z) := congrFun ha (ent k z)
    have h2 : F (setE z k a₀) = a * θ a₀ := congrFun ha a₀
    rw [setE_ent] at h1
    rw [h1, h2]
    ring
  have ind : ∀ (s : Finset (Fin N' × Fin N)) (z : n → Fin N' → Fin N → ℂ),
      F z * θ a₀ ^ s.card = F (repl a₀ s z) * ∏ p ∈ s, θ (ent p z) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro z
      have : repl a₀ (∅ : Finset (Fin N' × Fin N)) z = z := by
        funext τ i j
        simp [repl]
      simp [this]
    | insert k s hk ih =>
      intro z
      have key := step (repl a₀ s z) k
      have e1 : setE (repl a₀ s z) k a₀ = repl a₀ (insert k s) z := by
        funext τ i j
        by_cases h : (i, j) = k <;> simp [setE, repl, Finset.mem_insert, h]
      have e2 : ent k (repl a₀ s z) = ent k z := by
        funext τ
        simp [ent, repl, hk]
      rw [e1, e2] at key
      rw [Finset.card_insert_of_notMem hk, pow_succ, ← mul_assoc, ih z, Finset.prod_insert hk]
      linear_combination (∏ p ∈ s, θ (ent p z)) * key
  refine ⟨F (fun τ _ _ => a₀ τ) / θ a₀ ^ (Finset.univ : Finset (Fin N' × Fin N)).card, ?_⟩
  funext z
  have h := ind Finset.univ z
  have e1 : repl a₀ (Finset.univ : Finset (Fin N' × Fin N)) z = fun τ _ _ => a₀ τ := by
    funext τ i j
    simp [repl]
  have e2 : tensPow θ N N' z = ∏ p : Fin N' × Fin N, θ (ent p z) := by
    unfold tensPow
    exact (Fintype.prod_prod_type' (f := fun i j => θ fun τ => z τ i j)).symm
  rw [e1] at h
  show F z = _ * tensPow θ N N' z
  rw [e2, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero _ ha₀)]
  exact h

end Gen

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {B : Cd.Base D cc δ}

theorem thZeroSpans (hS : B.StdOK) (N N' : ℕ) : B.ThZeroSpans N N' := by
  intro F hF
  have e : TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) = Formalism.L2.Th1.F.area B.L := B.areaOK
  have h0' : TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') = powLat B.lamM N N' := B.lat0OK N N'
  have h1 : F ∈ Formalism.L2.Th1.H.Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N')
      (alphaQ B.cq (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N'))
      (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) := by
    refine Th_congr _ _ _ _ (fun x hx => ?_) hF
    obtain ⟨m, hm⟩ := B.qInt0 hS N N' x hx
    exact al_eq D B.tor x m hm
  rw [e, h0'] at h1
  exact tens_spans B.cq B.L B.lamM (B.thMM_ne_zero hS)
    (isThM_spans _ _ _ _ _ _ hS B.kappa_ne_zero (B.thMM_spec hS)) N N' F h1

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J
end
end

section
noncomputable section
open Classical Polynomial

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J

open Formalism.L2.PairingIndexBounds.Eq.J Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

section Abstract

variable {E : Type} [Field E] [CharZero E] [StarRing E]

theorem one_add_ne (s : E) (hs : star s = -s) (t : ℕ) : (1 : E) + t * s ≠ 0 := by
  intro h
  have e : star ((1:E) + t * s) = 1 - t * s := by
    rw [star_add, star_one, star_mul, hs, star_natCast]; ring
  have h2 : (1:E) - t * s = 0 := by rw [← e, h, star_zero]
  have h3 : (2:E) = 0 := by linear_combination h + h2
  exact two_ne_zero h3

theorem one_sub_ne (s : E) (hs : star s = -s) (t : ℕ) : (1 : E) - t * s ≠ 0 := by
  intro h
  have e : star ((1:E) - t * s) = 1 + t * s := by
    rw [star_sub, star_one, star_mul, hs, star_natCast]; ring
  have h2 : (1:E) + t * s = 0 := by rw [← e, h, star_zero]
  have h3 : (2:E) = 0 := by linear_combination h + h2
  exact two_ne_zero h3

def cay (s : E) (t : ℕ) : E := (1 + t * s) / (1 - t * s)

theorem cay_norm (s : E) (hs : star s = -s) (t : ℕ) : star (cay s t) * cay s t = 1 := by
  unfold cay
  have h1 := one_add_ne s hs t
  have h2 := one_sub_ne s hs t
  have e1 : star ((1:E) + t * s) = 1 - t * s := by
    rw [star_add, star_one, star_mul, hs, star_natCast]; ring
  have e2 : star ((1:E) - t * s) = 1 + t * s := by
    rw [star_sub, star_one, star_mul, hs, star_natCast]; ring
  rw [star_div₀, e1, e2, div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero h1 h2)]
  ring

theorem cay_inj (s : E) (hs : star s = -s) (hs0 : s ≠ 0) : Function.Injective (cay s) := by
  intro a b hab
  unfold cay at hab
  have ha1 := one_sub_ne s hs a
  have hb1 := one_sub_ne s hs b
  rw [div_eq_div_iff ha1 hb1] at hab
  have h0 : ((a:E) - b) * s * 2 = 0 := by linear_combination hab
  have hab' : ((a:E) - b) = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact h
      · exact absurd h hs0
    · exact absurd h two_ne_zero
  exact_mod_cast sub_eq_zero.mp hab'

theorem exists_norm_one (s : E) (hs : star s = -s) (hs0 : s ≠ 0) (p : E[X]) (hp : p ≠ 0) :
    ∃ z : E, star z * z = 1 ∧ z ≠ 1 ∧ p.eval z ≠ 0 := by
  classical
  let S : Finset E := insert 1 p.roots.toFinset
  have hfin : (cay s ⁻¹' (S : Set E)).Finite :=
    S.finite_toSet.preimage (cay_inj s hs hs0).injOn
  obtain ⟨t, ht⟩ := hfin.infinite_compl.nonempty
  simp only [Set.mem_compl_iff] at ht
  refine ⟨cay s t, cay_norm s hs t, ?_, ?_⟩
  · intro h
    apply ht
    simp [S, h]
  · intro h
    apply ht
    simp [S, Polynomial.mem_roots', hp, h]

theorem eval_charpolyRev' {n : ℕ} (M : Matrix (Fin n) (Fin n) E) (z : E) :
    M.charpolyRev.eval z = (1 - z • M).det := by
  rw [Matrix.charpolyRev, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.one_apply, apply_ite]
  exact mul_comm _ _

theorem split_unitary (s : E) (hs : star s = -s) (hs0 : s ≠ 0) {n : ℕ} (γ : Matrix.unitaryGroup (Fin n) E) :
    ∃ γ₁ γ₂ : Matrix.unitaryGroup (Fin n) E, γ = γ₁ * γ₂ ∧
      (1 - (γ₁ : Matrix (Fin n) (Fin n) E)).det ≠ 0 ∧ (1 - (γ₂ : Matrix (Fin n) (Fin n) E)).det ≠ 0 := by
  classical
  have hp : (γ : Matrix (Fin n) (Fin n) E).charpolyRev ≠ 0 := by
    intro h
    have h0 := congrArg (Polynomial.eval 0) h
    rw [eval_charpolyRev', zero_smul, sub_zero, Matrix.det_one, eval_zero] at h0
    exact one_ne_zero h0
  obtain ⟨z, hz, hz1, hev⟩ := exists_norm_one s hs hs0 _ hp
  rw [eval_charpolyRev'] at hev
  have hu : (z • (1 : Matrix (Fin n) (Fin n) E)) ∈ Matrix.unitaryGroup (Fin n) E := by
    rw [Matrix.mem_unitaryGroup_iff, star_smul, star_one, smul_mul_smul_comm, one_mul,
      mul_comm z, hz, one_smul]
  have hv : (star z • (1 : Matrix (Fin n) (Fin n) E)) ∈ Matrix.unitaryGroup (Fin n) E := by
    rw [Matrix.mem_unitaryGroup_iff, star_smul, star_one, star_star, smul_mul_smul_comm, one_mul,
      hz, one_smul]
  let u : Matrix.unitaryGroup (Fin n) E := ⟨_, hu⟩
  let v : Matrix.unitaryGroup (Fin n) E := ⟨_, hv⟩
  refine ⟨v, u * γ, ?_, ?_, ?_⟩
  · apply Subtype.ext
    show (γ : Matrix (Fin n) (Fin n) E) = (star z • 1) * ((z • 1) * (γ : Matrix (Fin n) (Fin n) E))
    rw [← mul_assoc, smul_mul_smul_comm, one_mul, hz, one_smul, one_mul]
  · show (1 - star z • (1 : Matrix (Fin n) (Fin n) E)).det ≠ 0
    have e : (1 : Matrix (Fin n) (Fin n) E) - star z • 1 = (1 - star z) • 1 := by
      rw [sub_smul, one_smul]
    rw [e, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    apply pow_ne_zero
    intro h
    apply hz1
    have h' : star z = 1 := (sub_eq_zero.mp h).symm
    simpa using congrArg star h'
  · show (1 - (z • 1) * (γ : Matrix (Fin n) (Fin n) E)).det ≠ 0
    rwa [smul_mul_assoc, one_mul]

end Abstract

open Formalism.BasicNotions Formalism.MainNotions NumberField

theorem exists_skew (D : Car) : letI := D.host.cmStar; ∃ s : D.host.E, star s = -s ∧ s ≠ 0 := by
  letI := D.host.cmStar
  haveI := D.host.isCMField_hostE
  by_contra hno
  push Not at hno
  apply NumberField.IsCMField.complexConj_ne_one D.host.E
  refine AlgEquiv.ext fun x => ?_
  have h := hno (x - star x) (by rw [star_sub, star_star]; ring)
  exact (sub_eq_zero.mp h).symm

theorem split_host (D : Car) {n : ℕ} :
    letI := D.host.cmStar
    ∀ γ : Matrix.unitaryGroup (Fin n) D.host.E,
    ∃ γ₁ γ₂ : Matrix.unitaryGroup (Fin n) D.host.E, γ = γ₁ * γ₂ ∧
      (1 - (γ₁ : Matrix (Fin n) (Fin n) D.host.E)).det ≠ 0 ∧ (1 - (γ₂ : Matrix (Fin n) (Fin n) D.host.E)).det ≠ 0 := by
  letI := D.host.cmStar
  intro γ
  obtain ⟨s, hs, hs0⟩ := exists_skew D
  exact split_unitary s hs hs0 γ

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J
end
end

section
noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J

open Formalism.L2.PairingIndexBounds.Eq.J Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {B : Cd.Base D cc δ}

theorem first_constant_of_triangles_data (hS : B.StdOK) (hL : B.LatAll) (hTL : Tr0L D B.tor) (hG : GaussRow B)
    (hLat : ∀ N N', Even N → Even N' → Lat0IsLat B N N') (hSp : ∀ N N', Even N → Even N' → B.ThZeroSpans N N') : J1 B := by
  intro N N' γ hN hN'
  obtain ⟨γ₁, γ₂, rfl, h1, h2⟩ := split_host D γ
  have h0 := Formalism.L2.Ker.Cd.Base.thZeroMem B hS N N'
  exact J1at_mul hL hTL hN hN' h0 γ₁ γ₂
    (J1at_of_ne hS hL hG hN hN' (hLat N N' hN hN') (hSp N N' hN hN') γ₁ h1)
    (J1at_of_ne hS hL hG hN hN' (hLat N N' hN hN') (hSp N N' hN hN') γ₂ h2)

theorem second_constant_of_triangles_data (hS : B.StdOK) (hL : B.LatAll) (hTR : Tr0R D B.tor) (hG : GaussRow B)
    (hLat : ∀ N N', Even N → Even N' → Lat0IsLat B N N') (hSp : ∀ N N', Even N → Even N' → B.ThZeroSpans N N') : J2 B := by
  intro N N' γ' hN hN'
  obtain ⟨γ₁, γ₂, rfl, h1, h2⟩ := split_host D γ'
  have h0 := Formalism.L2.Ker.Cd.Base.thZeroMem B hS N N'
  have key := J2at_mul hL hTR hN hN' h0 γ₁ γ₂
    (J2at_of_ne hS hL hG hN hN' (hLat N N' hN hN') (hSp N N' hN hN') γ₁ h1)
    (J2at_of_ne hS hL hG hN hN' (hLat N N' hN hN') (hSp N N' hN hN') γ₂ h2)
  have hhalf : B.thHalf N N' (StandardLatticesGL3.stdL D N) = B.thZero N N' := by
    unfold Formalism.L2.Ker.Cd.Base.thHalf
    exact iopSelf D B.tor N N' _ _ (Formalism.L2.Ker.Cd.mem_ThSp_of D B.tor _ _ h0)
  unfold J2at at key
  unfold Formalism.L2.Ker.Cd.Base.thMoved
  rw [hhalf]
  exact key

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J
end
end

section
noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J

open Formalism.L2.PairingIndexBounds.Eq.J Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {B : Cd.Base D cc δ}

theorem first_constant_of_gauss_sum (hS : B.StdOK) (hL : B.LatAll) (hTL : Tr0L D B.tor) (hG : GaussRow B) : J1 B :=
  first_constant_of_triangles_data hS hL hTL hG (fun N N' _ _ => lat0IsLat hS N N') (fun N N' _ _ => thZeroSpans hS N N')

theorem second_constant_of_gauss_sum (hS : B.StdOK) (hL : B.LatAll) (hTR : Tr0R D B.tor) (hG : GaussRow B) : J2 B :=
  second_constant_of_triangles_data hS hL hTR hG (fun N N' _ _ => lat0IsLat hS N N') (fun N N' _ _ => thZeroSpans hS N N')

theorem first_constant_of_pullback (hS : B.StdOK) (hL : B.LatAll) (hTL : Tr0L D B.tor) (hNeg : NegOneNorm D) : J1 B :=
  first_constant_of_gauss_sum hS hL hTL (gaussRow_of B hS hL hNeg)

theorem second_constant_of_pullback (hS : B.StdOK) (hL : B.LatAll) (hTR : Tr0R D B.tor) (hNeg : NegOneNorm D) : J2 B :=
  second_constant_of_gauss_sum hS hL hTR (gaussRow_of B hS hL hNeg)

theorem eqP_of_neg (B : Cd.Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0)
    (hS : B.StdOK) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ)
    (hSq : SqP D B.tor) (hTL : Tr0L D B.tor) (hTR : Tr0R D B.tor) (hNeg : NegOneNorm D) : B.EqP χ := by
  have hL := B.latAll hcc hδ hδ0
  exact eqP B hcc hδ hδ0 hS χ hχ hSq hTL hTR (first_constant_of_pullback hS hL hTL hNeg) (second_constant_of_pullback hS hL hTR hNeg)

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J
end
end

section
noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J

open Formalism.L2.PairingIndexBounds.Eq.J Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Car}

theorem star_sqrt_neg (x : D.host.E) (n : ℕ) (hn : 0 < n) (hx : x ^ 2 = -(n : D.host.E)) : star x = -x :=
  _root_.UpperTheory.Reformulated.B.StarSqrtNeg.star_sqrt_neg x n hn hx

theorem isIntegral_sqrt (x : D.host.E) (n : ℕ) (hx : x ^ 2 = -(n : D.host.E)) : IsIntegral ℤ x := by
  refine ⟨Polynomial.X ^ 2 + Polynomial.C (n : ℤ), Polynomial.monic_X_pow_add_C _ two_ne_zero, ?_⟩
  simp [hx]

theorem isIntegral_int (k : ℤ) : IsIntegral ℤ (k : D.host.E) := by
  have := isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := k)
  simpa using this

theorem negOneNorm (D : Car) : NegOneNorm D := by
  intro m hm
  obtain ⟨hq, hd, hq8, hd16, -⟩ := D.host.hyp
  have hqd : D.host.q ≠ D.host.d := by omega
  obtain ⟨α, β, γ, δ, s, h⟩ := Neg.rep_int D.host.q D.host.d hq hd hq8 hqd m hm
  have ha : (D.host.sqq : D.host.E) ^ 2 = -(D.host.q : D.host.E) :=
    D.host.sqq_sq
  have hb : (D.host.sqd : D.host.E) ^ 2 = -(D.host.d : D.host.E) :=
    D.host.sqd_sq
  obtain ⟨a, haa⟩ : ∃ a : D.host.E, a = D.host.sqq := ⟨_, rfl⟩
  obtain ⟨b, hbb⟩ : ∃ b : D.host.E, b = D.host.sqd := ⟨_, rfl⟩
  rw [← haa] at ha
  rw [← hbb] at hb
  have hsa := star_sqrt_neg a _ hq.pos ha
  have hsb := star_sqrt_neg b _ hd.pos hb
  have hint : IsIntegral ℤ (((α : D.host.E) + β * a) * ((γ : D.host.E) + δ * b)) :=
    ((isIntegral_int α).add ((isIntegral_int β).mul (isIntegral_sqrt a _ ha))).mul
      ((isIntegral_int γ).add ((isIntegral_int δ).mul (isIntegral_sqrt b _ hb)))
  refine ⟨⟨_, hint⟩, ⟨_, isIntegral_int s⟩, ?_, ?_⟩
  · show star (s : D.host.E) = (s : D.host.E)
    exact star_intCast s
  · show star (((α : D.host.E) + β * a) * ((γ : D.host.E) + δ * b)) * (((α : D.host.E) + β * a) * ((γ : D.host.E) + δ * b)) =
      -1 + (m : D.host.E) * (s : D.host.E)
    have hZ : ((α : D.host.E) ^ 2 + D.host.q * (β : D.host.E) ^ 2) * ((γ : D.host.E) ^ 2 + D.host.d * (δ : D.host.E) ^ 2) =
        -1 + (m : D.host.E) * (s : D.host.E) := by exact_mod_cast congrArg (Int.cast : ℤ → D.host.E) h
    rw [star_mul', star_add, star_add, star_mul', star_mul', star_intCast, star_intCast, star_intCast, star_intCast,
      hsa, hsb]
    linear_combination hZ + (-(β : D.host.E) ^ 2 * ((γ : D.host.E) ^ 2 - (δ : D.host.E) ^ 2 * b ^ 2)) * ha +
      (-((α : D.host.E) ^ 2 + D.host.q * (β : D.host.E) ^ 2) * (δ : D.host.E) ^ 2) * hb

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {B : Cd.Base D cc δ}

theorem eqP_of_paths (B : Cd.Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0)
    (hS : B.StdOK) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ)
    (hSq : SqP D B.tor) (hTL : Tr0L D B.tor) (hTR : Tr0R D B.tor) : B.EqP χ :=
  eqP_of_neg B hcc hδ hδ0 hS χ hχ hSq hTL hTR (negOneNorm D)

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J
end
end
