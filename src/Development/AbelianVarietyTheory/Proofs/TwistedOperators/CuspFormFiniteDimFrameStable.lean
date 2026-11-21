import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStableOfIsGKSub
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSmoothAutomorphicRightTranslateFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimKStableSesquilinearStatement

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

namespace GlobalTheory

theorem exists_proj_sesq_posDef_finiteDim : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (b : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (F : Submodule ℂ M), FiniteDimensional ℂ F →
    (∀ x ∈ F, x ≠ 0 → 0 < (b x x).re) → (∀ x ∈ F, ∀ y ∈ F, star (b x y) = b y x) →
    ∃ e : M →ₗ[ℂ] M, (∀ x, e x ∈ F) ∧ ∀ x, ∀ f ∈ F, b (e x) f = b x f := by
  intro M _ _ b F hF hpos hherm
  classical
  set n := Module.finrank ℂ F
  let v : Module.Basis (Fin n) ℂ F := Module.finBasis ℂ F
  let A : F →ₗ[ℂ] (Fin n → ℂ) := LinearMap.pi (fun i => (b (v i : M)).comp F.subtype)
  let B : M →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := fun x i => star (b x (v i : M))
      map_add' := by intro x y; funext i; simp [map_add]
      map_smul' := by intro c x; funext i; simp [mul_comm] }
  have key : ∀ (y : F) (x : M), (∀ i, b (v i : M) (y : M) = star (b x (v i : M))) →
      ∀ f ∈ F, b (y : M) f = b x f := by
    intro y x h f hf
    have hc : (b (y : M)).comp F.subtype = (b x).comp F.subtype := by
      refine v.ext (fun i => ?_)
      simp only [LinearMap.comp_apply, Submodule.coe_subtype]
      rw [← hherm _ (v i).2 _ y.2, h i, star_star]
    have := LinearMap.congr_fun hc ⟨f, hf⟩
    simpa using this
  have hinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h0 : ∀ i, b (v i : M) (y : M) = star (b (0 : M) (v i : M)) := by
      intro i
      have := congrFun hy i
      simpa [A] using this
    have hyy := key y 0 h0 y y.2
    by_contra hne
    have hne' : (y : M) ≠ 0 := by simpa using hne
    have := hpos y y.2 hne'
    rw [hyy] at this
    simp at this
  have hdim : Module.finrank ℂ F = Module.finrank ℂ (Fin n → ℂ) := by simp [n]
  let Aeq := LinearMap.linearEquivOfInjective A hinj hdim
  refine ⟨F.subtype.comp (Aeq.symm.toLinearMap.comp B), fun x => (Aeq.symm (B x)).2, ?_⟩
  intro x f hf
  show b ((Aeq.symm (B x) : F) : M) f = b x f
  refine key (Aeq.symm (B x)) x ?_ f hf
  intro i
  have h1 : A (Aeq.symm (B x)) = B x := by
    exact Aeq.apply_symm_apply (B x)
  have := congrFun h1 i
  simpa [A, B] using this

end GlobalTheory
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonalProjection_posDef_sesquilinear_finiteDim : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (b : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (F : Submodule ℂ M), FiniteDimensional ℂ F →
    (∀ x ∈ F, x ≠ 0 → 0 < (b x x).re) → (∀ x ∈ F, ∀ y ∈ F, star (b x y) = b y x) →
    ∃ e : M →ₗ[ℂ] M, (∀ x, e x ∈ F) ∧ ∀ x, ∀ f ∈ F, b (e x) f = b x f := by
  atlas_forward_decl GlobalTheory.exists_proj_sesq_posDef_finiteDim
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.KTypeProj

theorem typeSpan_proj_mem {M ι : Type} [AddCommGroup M] [Module ℂ M] (b : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (G : Submodule ℂ M)
    (ρ : ι → M →ₗ[ℂ] M) (inv : ι → ι) (hpos : ∀ x ∈ G, x ≠ 0 → 0 < (b x x).re)
    (hherm : ∀ x ∈ G, ∀ y ∈ G, star (b x y) = b y x)
    (_hρG : ∀ i, ∀ x ∈ G, ρ i x ∈ G) (hadj : ∀ i, ∀ x ∈ G, ∀ y ∈ G, b (ρ i x) y = b x (ρ (inv i) y))
    (hproj : ∀ F : Submodule ℂ M, F ≤ G → FiniteDimensional ℂ F →
      ∃ π : M →ₗ[ℂ] M, (∀ x, π x ∈ F) ∧ ∀ x, ∀ f ∈ F, b (π x) f = b x f)
    (Y₀ : Submodule ℂ M) (e : M →ₗ[ℂ] M) (he : ∀ x, e x ∈ typeSpan ρ Y₀ G)
    (he' : ∀ x, ∀ f ∈ typeSpan ρ Y₀ G, b (e x) f = b x f)
    (Y : Submodule ℂ M) (hYf : FiniteDimensional ℂ Y) (hYG : Y ≤ G) (hYρ : ∀ i, ∀ y ∈ Y, ρ i y ∈ Y) :
    ∀ x ∈ Y, e x ∈ Y := by
  intro x hx
  have hzero : ∀ d ∈ G, b d d = 0 → d = 0 := by
    intro d hd h
    by_contra hne
    have := hpos d hd hne
    rw [h] at this
    simp at this
  obtain ⟨π, hπY, hπ⟩ := hproj Y hYG hYf
  have hcomm : ∀ i, ∀ z ∈ G, π (ρ i z) = ρ i (π z) := by
    intro i z hz
    have hdY : π (ρ i z) - ρ i (π z) ∈ Y := Y.sub_mem (hπY _) (hYρ i _ (hπY z))
    have hpair : ∀ y ∈ Y, b (π (ρ i z) - ρ i (π z)) y = 0 := by
      intro y hy
      have h1 : b (π (ρ i z)) y = b (ρ i z) y := hπ _ y hy
      have h2 : b (ρ i z) y = b z (ρ (inv i) y) := hadj i z hz y (hYG hy)
      have h3 : b z (ρ (inv i) y) = b (π z) (ρ (inv i) y) := (hπ z _ (hYρ (inv i) y hy)).symm
      have h4 : b (ρ i (π z)) y = b (π z) (ρ (inv i) y) := hadj i (π z) (hYG (hπY z)) y (hYG hy)
      rw [map_sub, LinearMap.sub_apply, h1, h2, h3, h4, sub_self]
    exact sub_eq_zero.mp (hzero _ (hYG hdY) (hpair _ hdY))
  have hSG : typeSpan ρ Y₀ G ≤ G := typeSpan_le ρ Y₀ G
  have hY1f : FiniteDimensional ℂ (typeSpan ρ Y₀ G ⊓ Y : Submodule ℂ M) :=
    Submodule.finiteDimensional_of_le inf_le_right
  obtain ⟨π₁, hπ₁Y, hπ₁⟩ := hproj (typeSpan ρ Y₀ G ⊓ Y) (inf_le_left.trans hSG) hY1f
  have hpS : π₁ x ∈ typeSpan ρ Y₀ G := (hπ₁Y x).1
  have hpY : π₁ x ∈ Y := (hπ₁Y x).2
  have hxp : x - π₁ x ∈ Y := Y.sub_mem hx hpY
  have hle : typeSpan ρ Y₀ G ≤ LinearMap.ker (b (x - π₁ x)) := by
    refine iSup₂_le fun T hT => ?_
    rintro _ ⟨w, hw, rfl⟩
    rw [LinearMap.mem_ker]
    have hTw : T w ∈ G := hT.1 ⟨w, hw, rfl⟩
    have hπT : π (T w) ∈ typeSpan ρ Y₀ G ⊓ Y := by
      refine ⟨?_, hπY _⟩
      have hm := map_le_typeSpan ρ (Y₀ := Y₀) (G := G) (π ∘ₗ T) ?_ ?_
      · exact hm ⟨w, hw, rfl⟩
      · rintro _ ⟨v, -, rfl⟩; exact hYG (hπY _)
      · intro i v hv
        simp only [LinearMap.comp_apply]
        rw [hT.2 i v hv, hcomm i _ (hT.1 ⟨v, hv, rfl⟩)]
    have e1 : b (x - π₁ x) (π (T w)) = 0 := by
      rw [map_sub, LinearMap.sub_apply, hπ₁ x _ hπT, sub_self]
    have e2 : b (T w - π (T w)) (x - π₁ x) = 0 := by
      rw [map_sub b (T w) (π (T w)), LinearMap.sub_apply, hπ (T w) _ hxp, sub_self]
    have e3 : b (x - π₁ x) (T w - π (T w)) = 0 := by
      rw [← hherm _ (G.sub_mem hTw (hYG (hπY _))) _ (hYG hxp), e2, star_zero]
    have hsplit : T w = π (T w) + (T w - π (T w)) := by abel
    rw [hsplit, map_add, e1, e3, add_zero]
  have hd : e x - π₁ x ∈ typeSpan ρ Y₀ G := Submodule.sub_mem _ (he x) hpS
  have hdd : b (e x - π₁ x) (e x - π₁ x) = 0 := by
    have h1 := he' x _ hd
    have h2 := LinearMap.mem_ker.mp (hle hd)
    rw [map_sub b x (π₁ x), LinearMap.sub_apply] at h2
    rw [map_sub b (e x) (π₁ x), LinearMap.sub_apply]
    rw [h1, sub_eq_zero.mp h2, sub_self]
  have h0 := hzero _ (hSG hd) hdd
  rw [sub_eq_zero.mp h0]
  exact hpY

end GlobalTheory.KTypeProj

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typeSpanProjection_preserves_finiteDim_invariant_subspace : ∀ {M ι : Type} [AddCommGroup M] [Module ℂ M] (b : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (G : Submodule ℂ M) (ρ : ι → M →ₗ[ℂ] M)
    (inv : ι → ι), (∀ x ∈ G, x ≠ 0 → 0 < (b x x).re) → (∀ x ∈ G, ∀ y ∈ G, star (b x y) = b y x) →
    (∀ i, ∀ x ∈ G, ρ i x ∈ G) → (∀ i, ∀ x ∈ G, ∀ y ∈ G, b (ρ i x) y = b x (ρ (inv i) y)) →
    (∀ F : Submodule ℂ M, F ≤ G → FiniteDimensional ℂ F →
      ∃ π : M →ₗ[ℂ] M, (∀ x, π x ∈ F) ∧ ∀ x, ∀ f ∈ F, b (π x) f = b x f) →
    ∀ (Y₀ : Submodule ℂ M) (e : M →ₗ[ℂ] M), (∀ x, e x ∈ GlobalTheory.KTypeProj.typeSpan ρ Y₀ G) →
    (∀ x, ∀ f ∈ GlobalTheory.KTypeProj.typeSpan ρ Y₀ G, b (e x) f = b x f) →
    ∀ Y : Submodule ℂ M, FiniteDimensional ℂ Y → Y ≤ G → (∀ i, ∀ y ∈ Y, ρ i y ∈ Y) → ∀ x ∈ Y, e x ∈ Y := by
  atlas_forward_decl GlobalTheory.KTypeProj.typeSpan_proj_mem
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

open Matrix in

theorem GlobalTheory.CuspGK.inK_inv {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel V S)
    (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (h : GlobalTheory.CuspGK.InK M τ g) :
    GlobalTheory.CuspGK.InK M τ g⁻¹ ∧ g⁻¹⁻¹ = g := by
  obtain ⟨hU, hK1, hK2⟩ := h
  set P := M.fr τ with hPdef
  have hP : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  set u := P * g * P⁻¹ with hu
  have huu : IsUnit u.det := Matrix.UnitaryGroup.det_isUnit ⟨u, hK1⟩
  have hg : IsUnit g.det := by
    have hdet : u.det = P.det * g.det * P⁻¹.det := by simp [hu, Matrix.det_mul]
    rw [hdet] at huu
    exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left huu)
  have hinv : P * g⁻¹ * P⁻¹ = u⁻¹ := by
    rw [hu, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hP, Matrix.mul_assoc]
  have hsu : star u * u = 1 := Unitary.star_mul_self_of_mem hK1
  have hustar : u⁻¹ = star u := Matrix.inv_eq_left_inv hsu
  have h1 : u⁻¹ * u = 1 := Matrix.nonsing_inv_mul _ huu
  have h2 : u * u⁻¹ = 1 := Matrix.mul_nonsing_inv _ huu
  refine ⟨⟨?_, ?_, ?_⟩, Matrix.nonsing_inv_nonsing_inv _ hg⟩
  · have hU' : gᴴ * gramAt D V τ * g = gramAt D V τ := hU
    show (g⁻¹)ᴴ * gramAt D V τ * g⁻¹ = gramAt D V τ
    have hgg : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hg
    calc (g⁻¹)ᴴ * gramAt D V τ * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * gramAt D V τ * g) * g⁻¹ := by rw [hU']
      _ = (g * g⁻¹)ᴴ * gramAt D V τ * (g * g⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = gramAt D V τ := by rw [hgg]; simp
  · show P * g⁻¹ * P⁻¹ ∈ _
    rw [hinv, hustar]
    exact Unitary.star_mem hK1
  · show P * g⁻¹ * P⁻¹ * _ = _ * (P * g⁻¹ * P⁻¹)
    rw [hinv]
    clear_value u
    calc u⁻¹ * Formalism.REAL.Jm (M.ε τ) = u⁻¹ * Formalism.REAL.Jm (M.ε τ) * (u * u⁻¹) := by rw [h2, Matrix.mul_one]
      _ = u⁻¹ * (Formalism.REAL.Jm (M.ε τ) * u) * u⁻¹ := by simp only [Matrix.mul_assoc]
      _ = u⁻¹ * (u * Formalism.REAL.Jm (M.ε τ)) * u⁻¹ := by rw [hK2]
      _ = (u⁻¹ * u) * Formalism.REAL.Jm (M.ε τ) * u⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (M.ε τ) * u⁻¹ := by rw [h1, Matrix.one_mul]
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inMaxCompactOfModelFrame_inv : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel V S) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ), GlobalTheory.CuspGK.InK M τ g → GlobalTheory.CuspGK.InK M τ g⁻¹ ∧ g⁻¹⁻¹ = g := by
  atlas_forward_decl GlobalTheory.CuspGK.inK_inv
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.GKGenKFin

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

def kGrp : Subgroup (GA D V) :=
  Subgroup.closure {k | ∃ τ g, GlobalTheory.CuspGK.InK M τ g ∧ k = atTau θ V τ g}

theorem kGrp_le : kGrp θ M ≤ GinfC V :=
  (Subgroup.closure_le _).2 fun _ ⟨τ, g, _, e⟩ => e ▸ GlobalTheory.FinTranslate.atTau_mem θ V τ g

theorem rTr_mul (x y : GA D V) (f : GA D V → ℂ) : rTr V (x * y) f = rTr V x (rTr V y f) := by
  funext g
  simp only [rTr, mul_assoc]

theorem rTr_inv_rTr (x : GA D V) (f : GA D V → ℂ) : rTr V x⁻¹ (rTr V x f) = f := by
  funext g
  simp only [rTr, inv_mul_cancel_right]

theorem rTr_mem_of_kStable {W : Submodule ℂ (GA D V → ℂ)} (hW : FiniteDimensional ℂ W)
    (hK : GlobalTheory.KTypeProj.KStable θ M W) {k : GA D V} (hk : k ∈ kGrp θ M) : ∀ f ∈ W, rTr V k f ∈ W := by
  refine Subgroup.closure_induction (p := fun k _ => ∀ f ∈ W, rTr V k f ∈ W) (fun x hx => ?_) ?_
    (fun x y _ _ hx hy => ?_) (fun x _ hx => ?_) hk
  · obtain ⟨τ, g, hg, rfl⟩ := hx
    exact hK τ g hg
  · intro f hf
    have e : rTr V 1 f = f := funext fun g => by simp [rTr]
    rw [e]
    exact hf
  · intro f hf
    rw [rTr_mul]
    exact hx _ (hy f hf)
  · let T : W →ₗ[ℂ] W := ((GlobalTheory.KTypeProj.rTrL x).restrict (p := W) (q := W) fun f hf => hx f hf)
    have hinj : Function.Injective T := by
      intro a b hab
      apply Subtype.ext
      have h1 : rTr V x a.1 = rTr V x b.1 := congrArg Subtype.val hab
      have h2 := congrArg (rTr V x⁻¹) h1
      rwa [rTr_inv_rTr, rTr_inv_rTr] at h2
    have hsurj := LinearMap.injective_iff_surjective.1 hinj
    intro f hf
    obtain ⟨h, hh⟩ := hsurj ⟨f, hf⟩
    have e : rTr V x h.1 = f := congrArg Subtype.val hh
    rw [← e, rTr_inv_rTr]
    exact h.2

theorem isKFinite_smul {Φ : GA D V → ℂ} {K : Subgroup (GA D V)} (h : GlobalTheory.Doubling.IsKFinite K Φ) (c : ℂ) :
    GlobalTheory.Doubling.IsKFinite K (c • Φ) := by
  obtain ⟨W, hW, hm⟩ := GlobalTheory.Doubling.isKFinite_iff.1 h
  exact GlobalTheory.Doubling.isKFinite_iff.2 ⟨W, hW, fun k hk => by
    exact W.smul_mem c (hm k hk)⟩

def kfinSm (hθ : IsInfFam θ) : Submodule ℂ (GA D V → ℂ) where
  carrier := {x | IsAutFunSm θ V x ∧ GlobalTheory.Doubling.IsKFinite (kGrp θ M) x}
  zero_mem' := ⟨GlobalTheory.Mem.AutSpace.isAutFunSm_zero θ V, .of_invariant fun _ _ _ => rfl⟩
  add_mem' := fun h h' => ⟨GlobalTheory.Mem.AutSpace.isAutFunSm_add h.1 h'.1, h.2.add h'.2⟩
  smul_mem' := fun c _ h => ⟨GlobalTheory.Mem.AutSpace.isAutFunSm_smul c h.1, isKFinite_smul h.2 c⟩

theorem exists_kStable {x : GA D V → ℂ} (h : GlobalTheory.Doubling.IsKFinite (kGrp θ M) x) :
    ∃ Y : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ Y ∧ x ∈ Y ∧ GlobalTheory.KTypeProj.KStable θ M Y := by
  refine ⟨GlobalTheory.Doubling.kSpan (kGrp θ M) x, h, Submodule.subset_span ⟨1, one_mem _, funext fun g => by simp⟩, ?_⟩
  intro τ g hg f hf
  have ha : atTau θ V τ g ∈ kGrp θ M := Subgroup.subset_closure ⟨τ, g, hg, rfl⟩
  have hle : GlobalTheory.Doubling.kSpan (kGrp θ M) x ≤
      (GlobalTheory.Doubling.kSpan (kGrp θ M) x).comap (GlobalTheory.KTypeProj.rTrL (atTau θ V τ g)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    refine Submodule.subset_span ⟨atTau θ V τ g * k, mul_mem ha hk, ?_⟩
    funext y
    simp only [GlobalTheory.KTypeProj.rTrL_apply, rTr, mul_assoc]
  exact hle hf

theorem isGKSub_kfinSm (hθ : IsInfFam θ) : GlobalTheory.CuspGK.IsGKSub θ M (kfinSm θ M hθ) where
  k τ g hg f hf := ⟨GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau D θ hθ V f hf.1 τ g hg.1,
    hf.2.translate (Subgroup.subset_closure ⟨τ, g, hg, rfl⟩)⟩
  lie τ X hX f hf := ⟨GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX hf.1,
    GlobalTheory.CuspLie.isKFinite_Rder hθ hX (kGrp_le θ M) hf.1.smooth hf.2⟩

theorem kFinite_of_mem_gkGen : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ → ∀ ψ : GA D V → ℂ,
    IsAutFunSm θ V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ GlobalTheory.KTypeProj.KStable θ M W) →
    ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∃ Y : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ Y ∧ x ∈ Y ∧
      GlobalTheory.KTypeProj.KStable θ M Y := by
  intro D θ V S M hθ ψ hψ ⟨W, hW, hψW, hK⟩ x hx
  have hm : ψ ∈ kfinSm θ M hθ :=
    ⟨hψ, GlobalTheory.Doubling.isKFinite_iff.2 ⟨W, hW, fun k hk => rTr_mem_of_kStable θ M hW hK hk ψ hψW⟩⟩
  exact exists_kStable θ M (GlobalTheory.CuspGK.gkGen_le θ M hm (isGKSub_kfinSm θ M hθ) hx).2

end GlobalTheory.GKGenKFin

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kFinite_of_mem_gKModuleGeneratedBy : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ → ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ GlobalTheory.KTypeProj.KStable θ M W) →
    ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∃ Y : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ Y ∧ x ∈ Y ∧
      GlobalTheory.KTypeProj.KStable θ M Y := by
  atlas_forward_decl GlobalTheory.GKGenKFin.kFinite_of_mem_gkGen
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.KTypeProj

theorem ktype_proj : GlobalTheory.FunPr.Hypotheses₂ → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ f ∈ W, rTr V (atTau θ V τ g) f ∈ W) →
    ∀ b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ,
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, x ≠ 0 → 0 < (b x x).re) →
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ, star (b x y) = b y x) →
      (∀ τ g, GlobalTheory.CuspGK.InK M τ g → ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (rTr V (atTau θ V τ g) y) = b (rTr V (atTau θ V τ g⁻¹) x) y) →
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (Rder θ V τ X y) = -b (Rder θ V τ X x) y) →
    ∃ e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ), e ψ = ψ ∧
      (∀ A : Submodule ℂ (GA D V → ℂ), A ≤ GlobalTheory.CuspGK.gkGen θ M ψ → GlobalTheory.CuspGK.IsGKSub θ M A → ∀ x ∈ A, e x ∈ A) ∧
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, e (e x) = e x) ∧
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ, b (e x) y = b x (e y)) ∧
      FiniteDimensional ℂ ((GlobalTheory.CuspGK.gkGen θ M ψ).map e) := by
  intro hP D θ V S M hθ ψ hψ hcusp hWex b hpos hherm hKadj hLie
  obtain ⟨W, hWfd, hψW, hWK⟩ := hWex
  have hWK' : KStable θ M W := fun τ g hg f hf => hWK τ g hg.1 hg.2 f hf
  set G := GlobalTheory.CuspGK.gkGen θ M ψ with hGdef
  set F := typeSpan (rhoK θ M) (W ⊓ G) G with hFdef
  haveI hFfd : FiniteDimensional ℂ F := GlobalTheory.T.finite_dim_K_stable_sesquilinear hP θ V S M hθ ψ hψ hcusp W hWfd hψW hWK' b hpos hherm hKadj hLie
  have hFG : F ≤ G := typeSpan_le _ _ _
  have hprojG : ∀ F' : Submodule ℂ (GA D V → ℂ), F' ≤ G → FiniteDimensional ℂ F' →
      ∃ π : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ), (∀ x, π x ∈ F') ∧ ∀ x, ∀ f ∈ F', b (π x) f = b x f :=
    fun F' hF' hfd => GlobalTheory.T.exists_orthogonalProjection_posDef_sesquilinear_finiteDim b F' hfd (fun x hx => hpos x (hF' hx)) (fun x hx y hy => hherm x (hF' hx) y (hF' hy))
  obtain ⟨e, heF, hechar⟩ := hprojG F hFG hFfd
  have hfix : ∀ f ∈ F, e f = f := by
    intro f hf
    by_contra hne
    have hd : e f - f ∈ F := F.sub_mem (heF f) hf
    have h0 : b (e f - f) (e f - f) = 0 := by
      rw [show b (e f - f) = b (e f) - b f from map_sub b _ _, LinearMap.sub_apply, hechar f _ hd, sub_self]
    have := hpos _ (hFG hd) (sub_ne_zero.2 hne)
    rw [h0] at this
    simp at this
  have hψF : ψ ∈ F := le_typeSpan _ inf_le_right ⟨hψW, GlobalTheory.CuspGK.mem_gkGen θ M ψ⟩
  have hinvK : ∀ i : KIdx M, GlobalTheory.CuspGK.InK M i.1.1 i.1.2⁻¹ ∧ i.1.2⁻¹⁻¹ = i.1.2 := fun i => GlobalTheory.T.inMaxCompactOfModelFrame_inv M i.1.1 i.1.2 i.2
  let inv : KIdx M → KIdx M := fun i => ⟨(i.1.1, i.1.2⁻¹), (hinvK i).1⟩
  have hρG : ∀ i, ∀ x ∈ G, rhoK θ M i x ∈ G := (kStable_iff θ M G).1 (kStable_gkGen θ M ψ)
  have hadj : ∀ i, ∀ x ∈ G, ∀ y ∈ G, b (rhoK θ M i x) y = b x (rhoK θ M (inv i) y) := by
    intro i x hx y hy
    have h := hKadj i.1.1 i.1.2⁻¹ (hinvK i).1 x hx y hy
    rw [(hinvK i).2] at h
    exact h.symm
  refine ⟨e, hfix ψ hψF, ?_, fun x _ => hfix _ (heF x), ?_, ?_⟩
  · intro A hAG hA x hx
    obtain ⟨Y, hYfd, hxY, hYK⟩ := GlobalTheory.T.kFinite_of_mem_gKModuleGeneratedBy θ M hθ ψ hψ ⟨W, hWfd, hψW, hWK'⟩ x (hAG hx)
    haveI := hYfd
    have hst := (kStable_iff θ M (Y ⊓ A)).1 (kStable_inf θ M hYK (kStable_of_isGKSub θ M hA))
    have := GlobalTheory.T.typeSpanProjection_preserves_finiteDim_invariant_subspace b G (rhoK θ M) inv hpos hherm hρG hadj hprojG (W ⊓ G) e heF hechar (Y ⊓ A)
      inferInstance (inf_le_right.trans hAG) hst x ⟨hxY, hx⟩
    exact this.2
  · intro x hx y hy
    have h1 : b (e x) (y - e y) = 0 := by
      rw [← hherm _ (G.sub_mem hy (hFG (heF y))) _ (hFG (heF x)), map_sub, LinearMap.sub_apply,
        hechar y _ (heF x), sub_self, star_zero]
    have h2 : b (e x) y = b (e x) (e y) := by
      rw [map_sub] at h1
      exact sub_eq_zero.1 h1
    rw [h2, hechar x _ (heF y)]
  · refine Submodule.finiteDimensional_of_le (S₂ := F) ?_
    rintro _ ⟨x, -, rfl⟩
    exact heF x

end GlobalTheory.KTypeProj

end
end
