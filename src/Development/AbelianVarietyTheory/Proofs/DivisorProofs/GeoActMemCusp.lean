import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActLevOfLiftsOfEqOne
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionMemCuspForms
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevActMemMlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformFamilyComponentIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedSectionReadingEqMovedFrameReadingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelGroupLiftExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelLiftFiniteCongruence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateCharacterOnLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformFamilyUnfoldingCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchingDeterminantRootOfUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTraceFormLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLinearApproxTower
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingComponentUniqueFrameUniqueArithmeticGroup

section
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moveMatch_of_markRel_of_isLevMove : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ), Formalism.L2.PjFree.GoodEmb c σ → 1 ≤ Dw.p + Dw.q → l.A = 1 → Pinned U e F ik φ → ∀ (k k' : U.Comp) (δ : GL (Fin r) E) (h : IsMatch (U.X k) (U.X k') δ) (γ : Dw.La →ₗ[𝓞 E] Dw.La) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), MarkRel l (φ k) (φ k') (F.t (ik k)) (F.t (ik k')) γ δ → IsLevMove ρ ν γ LinearMap.id → MoveMatch U U k k' h ρ ν := by
  first | exact @GlobalTheory.GeoLevel.moveMatch_of_markRel | exact GlobalTheory.GeoLevel.moveMatch_of_markRel | (intros; apply GlobalTheory.GeoLevel.moveMatch_of_markRel <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoLevel

section General

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix

theorem exists_endo_approx_of_keeps_hat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} (L Λ : Submodule (𝓞 E) (Fin n → E)) (g : GL (Fin n) (RA F E)) (h1 : L.FG)
    (h2 : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (hΛ : (Λ : Set (Fin n → E)) = latOf F (g : Matrix (Fin n) (Fin n) (RA F E)) L)
    (hg : ∀ z ∈ hat F (L : Set (Fin n → E)), (g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ z ∈ hat F (L : Set (Fin n → E)))
    {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (ι : La →ₗ[𝓞 E] (Fin n → E)) (hi : Function.Injective ι)
    (hr : LinearMap.range ι = L) (N : ℕ) (hN : 0 < N) :
    ∃ γ₀ : La →ₗ[𝓞 E] La, ∀ a, ∃ w ∈ hat F (L : Set (Fin n → E)),
      (g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ (fv F (ι a)) - fv F (ι (γ₀ a)) = N • w := by
  subst hr
  obtain ⟨f, hf, -, -⟩ := exists_linear_approx_tower F E n _ g Λ h1 h2 hΛ
  have hle : Λ ≤ LinearMap.range ι := by
    intro v hv
    have hv' : v ∈ (Λ : Set (Fin n → E)) := hv
    rw [hΛ] at hv'
    obtain ⟨z, hz, hzv⟩ := hv'
    refine ((hat_rational_points_and_approx F E n _ h1 h2).1 v).1 ?_
    rw [← hzv]
    exact hg z hz
  let e : La ≃ₗ[𝓞 E] LinearMap.range ι := LinearEquiv.ofInjective ι hi
  have he : ∀ x : LinearMap.range ι, ι (e.symm x) = x := fun x => by
    have : ((e (e.symm x) : LinearMap.range ι) : Fin n → E) = x := by rw [e.apply_symm_apply]
    exact this
  refine ⟨e.symm.toLinearMap ∘ₗ Submodule.inclusion hle ∘ₗ f N ∘ₗ e.toLinearMap, fun a => ?_⟩
  obtain ⟨w, hw, hfw⟩ := hf N hN (e a)
  refine ⟨-((g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ w), neg_mem (hg w hw), ?_⟩
  have h3 : ι ((e.symm.toLinearMap ∘ₗ Submodule.inclusion hle ∘ₗ f N ∘ₗ e.toLinearMap) a) =
      (f N (e a) : Fin n → E) := he _
  have h4 : ((e a : LinearMap.range ι) : Fin n → E) = ι a := rfl
  rw [h3, hfw, h4, Matrix.mulVec_add, GlobalTheory.AdLat.Tower.mulVec_nsmul, smul_neg]
  abel

end General

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong IotaOK)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem exists_endo_approx : ∀ (D : D7) (V : HSp D) (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), LatEmb V ι → ∀ (N : ℕ), 0 < N → ∀ κ : GA D V, FinCong V 1 κ → ∃ γ₀ : La →ₗ[𝓞 D.host.E] La, ∀ a, ∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (ι a)) - finVec V (ι (γ₀ a)) = N • w := by
  intro D V La _ _ ι hι N hN κ hκ
  obtain ⟨h1, h2, -, -, h5, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V 1
  obtain ⟨-, -, h3, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V κ
  have hk := (GlobalTheory.Member.AALev.congruences_agree D V κ).1.2 hκ
  rw [h5] at hk ⊢
  exact exists_endo_approx_of_keeps_hat (F := D.host.F) (latG V 1) (latG V κ) (finHom V κ) h1 h2 h3 hk ι hι.1 hι.2 N hN

end GlobalTheory.GeoLevel
end
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong IotaOK)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_congruence_endomorphism : ∀ (D : D7) (V : HSp D) (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), LatEmb V ι → ∀ (N : ℕ), 0 < N → ∀ κ : GA D V, FinCong V 1 κ → ∃ γ₀ : La →ₗ[𝓞 D.host.E] La, ∀ a, ∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (ι a)) - finVec V (ι (γ₀ a)) = N • w := by
  first | exact @GlobalTheory.GeoLevel.exists_endo_approx | exact GlobalTheory.GeoLevel.exists_endo_approx | (intros; apply GlobalTheory.GeoLevel.exists_endo_approx <;> assumption)
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong IotaOK)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoLevel

theorem isLift_inv_mul {D : D7} {V : HSp D} {r : ℕ} {hr : V.rank = r} {β : GL (Fin r) (EAf D)}
    {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)} {g : Formalism.L2.DIV.G0 Pg r} {κ₀ κ : GA D V}
    (h₀ : IsLift V hr β Pg g κ₀) (h : IsLift V hr β Pg g κ) : IsLift V hr β Pg 1 (κ₀⁻¹ * κ) := by
  obtain ⟨a₀, b₀, c₀⟩ := h₀
  obtain ⟨a, b, c⟩ := h
  have e : finR V hr (κ₀⁻¹ * κ) = (finR V hr κ₀)⁻¹ * finR V hr κ := by rw [map_mul, map_inv]
  have hb : finR V hr (κ₀⁻¹ * κ) ∈ Formalism.L2.DIV.St β := by
    rw [e]; exact mul_mem (inv_mem b₀) b
  refine ⟨mul_mem (inv_mem a₀) a, hb, fun w => ?_⟩
  have e2 : (⟨finR V hr (κ₀⁻¹ * κ), hb⟩ : Formalism.L2.DIV.St β) = (⟨finR V hr κ₀, b₀⟩ : Formalism.L2.DIV.St β)⁻¹ * ⟨finR V hr κ, b⟩ :=
    Subtype.ext e
  rw [e2, map_mul, map_inv, c₀, c, inv_mul_cancel]
  rfl

theorem cong_latG_of_finCong {D : D7} {V : HSp D} {M : ℕ} {k : GA D V} (hk : FinCong V M k)
    {a : Fin V.rank → D.host.E} (ha : a ∈ latG V 1) :
    ∃ w ∈ latGHat V 1, (finHom V k).1 *ᵥ finVec V a - finVec V a = M • w := by
  refine ((GlobalTheory.Member.AALev.congruences_agree D V k).2 M ⊤).1 (fun b _ z hz => hk _ ?_) a (by rwa [Submodule.top_smul])
  rw [GlobalTheory.Member.AALev.latHat_eq] at hz ⊢
  exact GlobalTheory.Member.AALev.hat_smul_int _ b hz

theorem exists_induces : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H) (V : HSp D) (r : ℕ) (hr : V.rank = r) (β : GL (Fin r) (EAf D)) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)), IsLatBasis V hr β → (∀ w, w ∈ Pg ↔ l.Mb ≤ w.asIdeal) → l.Mb.IsRadical → ∀ (Dw : Datum H) (ι₀ : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)), LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀) → ∀ g : Formalism.L2.DIV.G0 Pg r, ∃ γ₀, Induces Dw l V hr ι₀ β Pg g γ₀ := by
  intro D H l V r hr β Pg hβ hPg hrad Dw ι₀ hι g
  obtain ⟨κ₀, h₀⟩ := GlobalTheory.T.level_group_lift_exists D H l V r hr β Pg hβ hPg g
  obtain ⟨c1, c2⟩ := GlobalTheory.T.level_lift_finite_congruence D H l V r hr β Pg hβ hPg
  have hk₀ := c1 g κ₀ h₀
  obtain ⟨γ₀, hγ⟩ := GlobalTheory.T.lattice_congruence_endomorphism D V Dw.La _ hι l.M (lt_of_lt_of_le (by norm_num) l.three_le) κ₀ hk₀
  refine ⟨γ₀, fun κ hκ a _ => ?_⟩
  obtain ⟨w', hw', e'⟩ := hγ a
  obtain ⟨w, hw, e⟩ := cong_latG_of_finCong (c2 hrad _ (isLift_inv_mul h₀ hκ))
    (hι.2 ▸ LinearMap.mem_range_self _ a :
      (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀) a ∈ latG V 1)
  refine ⟨(finHom V κ₀).1 *ᵥ w + w', add_mem ((GlobalTheory.Member.AALev.congruences_agree D V κ₀).1.2 hk₀ w hw) hw', ?_⟩
  change (finHom V κ).1 *ᵥ finVec V ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀) a) -
    finVec V ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀) (γ₀ a)) = _
  have e1 : (finHom V κ).1 = (finHom V κ₀).1 * (finHom V (κ₀⁻¹ * κ)).1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel_left]
  have e3 : (finHom V κ₀).1 *ᵥ (l.M • w) = l.M • (finHom V κ₀).1 *ᵥ w := map_nsmul (finHom V κ₀).1.mulVecLin l.M w
  rw [nsmul_add, ← e', ← e3, ← e, Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← e1, sub_add_sub_cancel]

end GlobalTheory.GeoLevel
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong IotaOK)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoLevel.ModHalf

theorem mem_of_coprime {R A : Type} [CommRing R] [AddCommGroup A] [Module R A] {I J : Ideal R} (h : I ⊔ J = ⊤)
    (f : A →ₗ[R] A) (hf : ∀ a ∈ J • (⊤ : Submodule R A), f a ∈ I • (⊤ : Submodule R A)) (a : A) :
    f a ∈ I • (⊤ : Submodule R A) := by
  have h1 : (1 : R) ∈ I ⊔ J := by rw [h]; trivial
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 h1
  have : a = x • a + y • a := by rw [← add_smul, hxy, one_smul]
  rw [this, map_add, map_smul]
  exact add_mem (Submodule.smul_mem_smul hx trivial) (hf _ (Submodule.smul_mem_smul hy trivial))

theorem map_mem_smul_top {R A : Type} [CommRing R] [AddCommGroup A] [Module R A] {J : Ideal R}
    (f : A →ₗ[R] A) {a : A} (ha : a ∈ J • (⊤ : Submodule R A)) : f a ∈ J • (⊤ : Submodule R A) := by
  refine Submodule.smul_induction_on ha (fun r hr x _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smul]; exact Submodule.smul_mem_smul hr trivial
  · rw [map_add]; exact add_mem hx hy

theorem mem_of_range {R A B : Type} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    {I J : Ideal R} {N : ℕ} (h : I * J = Ideal.span {(N : R)}) (ι : A →ₗ[R] B) (hι : Function.Injective ι)
    {x y : A} {u : B} (hu : u ∈ LinearMap.range ι) (e : ι x - ι y = N • u) : x - y ∈ I • (⊤ : Submodule R A) := by
  obtain ⟨v, rfl⟩ := hu
  rw [← map_nsmul, ← map_sub] at e
  have e' : x - y = (N : R) • v := by rw [Nat.cast_smul_eq_nsmul]; exact hι e
  rw [e']
  refine Submodule.smul_mem_smul ?_ trivial
  have : (N : R) ∈ I * J := by
    rw [h]; exact Ideal.mem_span_singleton_self _
  exact (Ideal.mul_le_inf this).1

set_option maxHeartbeats 1600000 in

theorem mem_of_finVec {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (l : Level H) (V : HSp D)
    {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (hι : LatEmb V ι) (x y : La) (w : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) (hw : w ∈ latGHat V 1)
    (h : finVec V (ι x) - finVec V (ι y) = l.M • w) : x - y ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) La) := by
  obtain ⟨u, hu, e⟩ := GlobalTheory.MarkUniq.exists_of_finVec_eq_nsmul V 1 l.M (by have := l.three_le; omega)
    (ι x - ι y) w hw ((GlobalTheory.MarkUniq.finVec_sub V (ι x) (ι y)).trans h)
  exact mem_of_range l.prod ι hι.1 (hι.2.ge hu) e

theorem isLift_mul {D : D7} {V : HSp D} {r : ℕ} {hr : V.rank = r} {β : GL (Fin r) (EAf D)}
    {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)} {g h : Formalism.L2.DIV.G0 Pg r} {κ κ' : GA D V}
    (h1 : IsLift V hr β Pg g κ) (h2 : IsLift V hr β Pg h κ') : IsLift V hr β Pg (g * h) (κ * κ') := by
  obtain ⟨a1, b1, c1⟩ := h1
  obtain ⟨a2, b2, c2⟩ := h2
  refine ⟨mul_mem a1 a2, by rw [map_mul]; exact mul_mem b1 b2, fun w => ?_⟩
  have : (⟨finR V hr (κ * κ'), by rw [map_mul]; exact mul_mem b1 b2⟩ : Formalism.L2.DIV.St β) =
      ⟨finR V hr κ, b1⟩ * ⟨finR V hr κ', b2⟩ := Subtype.ext (map_mul _ _ _)
  rw [this, map_mul, c1, c2]; rfl

theorem flip_sub {M : Type} [AddCommGroup M] (N : ℕ) {p q w : M} (e : p - q = N • w) : q - p = N • (-w) := by
  rw [smul_neg, ← e, neg_sub]

theorem cocycle {M : Type} [AddCommGroup M] (k : M →+ M) (N : ℕ) {p q s t w₁ w₂ w₃ : M}
    (e1 : p - q = N • w₁) (e2 : k q - s = N • w₂) (e3 : k p - t = N • w₃) :
    t - s = N • (k w₁ + w₂ - w₃) := by
  rw [smul_sub, smul_add, ← map_nsmul, ← e1, ← e2, ← e3, map_sub]; abel

set_option maxHeartbeats 1600000 in

theorem action_mod_half : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H) (V : HSp D) (r : ℕ) (hr : V.rank = r) (β : GL (Fin r) (EAf D)) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)), IsLatBasis V hr β → (∀ w, w ∈ Pg ↔ l.Mb ≤ w.asIdeal) → ∀ (Dw : Datum H) (ι₀ : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)), LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀) → ∀ γ : Formalism.L2.DIV.G0 Pg r → Dw.La →ₗ[𝓞 D.host.E] Dw.La, (∀ g, Induces Dw l V hr ι₀ β Pg g (γ g)) → (∀ a, γ 1 a - a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) ∧ ∀ g h a, γ (g * h) a - γ g (γ h a) ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La) := by
  intro D H l V r hr β Pg hβ hPg Dw ι₀ hι γ hγ
  refine ⟨fun a => ?_, fun g h a => ?_⟩
  · refine mem_of_coprime l.coprime (γ 1 - LinearMap.id) (fun a ha => ?_) a
    obtain ⟨w, hw, e⟩ := hγ 1 1 (isLift_one V hr β Pg) a ha
    rw [map_one, Units.val_one, Matrix.one_mulVec] at e
    exact mem_of_finVec l V _ hι (γ 1 a) a (-w) (neg_mem hw) (flip_sub l.M e)
  · refine mem_of_coprime l.coprime (γ (g * h) - γ g ∘ₗ γ h) (fun a ha => ?_) a
    obtain ⟨κ, hκ⟩ := GlobalTheory.T.level_group_lift_exists D H l V r hr β Pg hβ hPg g
    obtain ⟨κ', hκ'⟩ := GlobalTheory.T.level_group_lift_exists D H l V r hr β Pg hβ hPg h
    obtain ⟨w₁, hw₁, e₁⟩ := hγ h κ' hκ' a ha
    obtain ⟨w₂, hw₂, e₂⟩ := hγ g κ hκ (γ h a) (map_mem_smul_top (γ h) ha)
    obtain ⟨w₃, hw₃, e₃⟩ := hγ (g * h) (κ * κ') (isLift_mul hκ hκ') a ha
    rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec] at e₃
    have hk := (GlobalTheory.Member.AALev.congruences_agree D V κ).1.2
      ((GlobalTheory.T.level_lift_finite_congruence D H l V r hr β Pg hβ hPg).1 g κ hκ) w₁ hw₁
    exact mem_of_finVec l V _ hι (γ (g * h) a) (γ g (γ h a)) _ (sub_mem (add_mem hk hw₂) hw₃)
      (cocycle (Matrix.mulVecLin (finHom V κ).1).toAddMonoidHom l.M e₁ e₂ e₃)

end GlobalTheory.GeoLevel.ModHalf
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoLevel

section Free

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem isMatch_div {X X' : Data E r} {a b : GL (Fin r) E} (ha : IsMatch X X' a) (hb : IsMatch X X' b) :
    IsMatch X' X' (b * a⁻¹) := by
  have hri : ∀ v, (a : Matrix (Fin r) (Fin r) E) *ᵥ (((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  refine ⟨rfl, rfl, rfl, fun u v => ?_, fun v => ?_⟩
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hb.iso, ← ha.iso, hri, hri]
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← hb.lat, ha.lat, hri]

omit [NumberField E] [IsCMField E] in
theorem lact_div {Ψ : Finset (E →+* ℂ)} (a b : GL (Fin r) E) (z : Frame Ψ r) :
    lact (b * a⁻¹) (castFr rfl (lact a z)) = lact b z := by
  funext τ
  change ((b * a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
    ((a : Matrix (Fin r) (Fin r) E).map τ.1 * mat z τ) = (b : Matrix (Fin r) (Fin r) E).map τ.1 * mat z τ
  rw [← Matrix.mul_assoc, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel_right]

variable {U : Formalism.L2.PjFree.Unf Xo c σ r} {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)}
  {ik : U.Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ}

theorem comp_unique (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (hpq : 1 ≤ Dw.p + Dw.q)
    (hA : l.A = 1) (hP : Pinned U e F ik φ) {k k₁ k₂ : U.Comp} {δ₁ δ₂ : GL (Fin r) E}
    (h₁ : IsMatch (U.X k) (U.X k₁) δ₁) (h₂ : IsMatch (U.X k) (U.X k₂) δ₂) {γ : Dw.La →ₗ[𝓞 E] Dw.La}
    {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ} (hm : IsLevMove ρ ν γ LinearMap.id)
    (m₁ : MarkRel l (φ k) (φ k₁) (F.t (ik k)) (F.t (ik k₁)) γ δ₁)
    (m₂ : MarkRel l (φ k) (φ k₂) (F.t (ik k)) (F.t (ik k₂)) γ δ₂) (x : (U.X k).dom) : k₁ = k₂ := by
  obtain ⟨y', hy⟩ := (GlobalTheory.exists_unique_frMove E H Dw l Xo c ρ ν hm.1 _ (U.un k x)).1
  obtain ⟨a₁, b₁⟩ := GlobalTheory.T.moveMatch_of_markRel_of_isLevMove E H Dw l Xo c σ r U g e F ik φ hσ hpq hA hP k k₁ δ₁ h₁ γ ρ ν m₁ hm x y' hy
  obtain ⟨a₂, b₂⟩ := GlobalTheory.T.moveMatch_of_markRel_of_isLevMove E H Dw l Xo c σ r U g e F ik φ hσ hpq hA hP k k₂ δ₂ h₂ γ ρ ν m₂ hm x y' hy
  obtain ⟨t₀, ht⟩ := exists_frBor_gen _ _ (a₂.symm.trans a₁) (b₂.symm.trans b₁)
  obtain ⟨_, -, _, -, he⟩ := (hU.2.2.2.1 k₁ k₂ _ _).1 ⟨_, ht⟩
  exact (congrArg Sigma.fst he).symm

theorem exists_const (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (hpq : 1 ≤ Dw.p + Dw.q)
    (hA : l.A = 1) (hP : Pinned U e F ik φ)
    (hex : ∀ (k : U.Comp) (δ : GL (Fin r) E) (h : IsMatch (U.X k) (U.X k) δ) (ρ : Xo.X ⟶ Xo.X)
      (ν : SABMap Xo.univ.t Xo.univ.t ρ), ρ ≫ Xo.s = Xo.s → MoveMatch U U k k h ρ ν → ∀ w n, Dom w n →
      ∀ f ∈ sec Xo c w n, ∀ f' ∈ sec Xo c w n,
      (∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') → ∀ x ∈ (U.X k).dom,
      Formalism.L2.PjFree.rdU U f' k x = Formalism.L2.PjFree.rdU U f k (lact δ (castFr h.psi x)))
    {k k' : U.Comp} {δ₀ : GL (Fin r) E} (h₀ : IsMatch (U.X k) (U.X k') δ₀) {γ : Dw.La →ₗ[𝓞 E] Dw.La}
    {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ} (hm : IsLevMove ρ ν γ LinearMap.id)
    (m₀ : MarkRel l (φ k) (φ k') (F.t (ik k)) (F.t (ik k')) γ δ₀) (n : ℕ) :
    ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ w, Dom w n → ∀ f ∈ sec Xo c w n, ∀ f' ∈ sec Xo c w n,
      (∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') →
      ∀ (k₁ k₁' : U.Comp) (δ : GL (Fin r) E) (h : IsMatch (U.X k₁) (U.X k₁') δ), k₁ = k →
      MarkRel l (φ k₁) (φ k₁') (F.t (ik k₁)) (F.t (ik k₁')) γ δ → ∀ x ∈ (U.X k₁).dom,
      Formalism.L2.PjFree.rdU U f' k₁ x = ε * Formalism.L2.PjFree.rdU U f k₁' (lact δ (castFr h.psi x)) := by
  obtain ⟨ε, hε, hc⟩ := GlobalTheory.T.exists_const_mul_reading_of_moved_section_at_frame E H Dw l Xo c σ r U U hσ hU hU k k' δ₀ h₀ ρ ν hm.1
    (GlobalTheory.T.moveMatch_of_markRel_of_isLevMove E H Dw l Xo c σ r U g e F ik φ hσ hpq hA hP k k' δ₀ h₀ γ ρ ν m₀ hm)
    (fun x y' t hx hy ht => GlobalTheory.LevelCusp.cabs_gen_eq_one_of_move E H Dw l Xo c σ r U hσ hU ρ ν k k' x _ y' t hy ht hx
      (fun τ i => by rw [h₀.dmin_eq]; exact hx _ i)) n
  refine ⟨ε, hε, fun w hw f hf f' hf' hv k₁ k₁' δ h hk m x hx => ?_⟩
  subst hk
  obtain rfl : k₁' = k' := comp_unique hσ hU hpq hA hP h h₀ hm m m₀ ⟨x, hx⟩
  obtain ⟨ν₀, hν₀, hy₀⟩ := (GlobalTheory.MoveCalc.frMove_calculus E H Dw l Xo c).1
  have hm₀ : IsLevMove (𝟙 Xo.X) ν₀ LinearMap.id LinearMap.id :=
    ⟨Category.id_comp _, fun a => by rw [hν₀]; exact (Category.comp_id _).trans (Category.id_comp _).symm,
      fun a => by rw [hν₀]; exact (Category.comp_id _).trans (Category.id_comp _).symm⟩
  have := hex k₁' _ (isMatch_div h₀ h) _ ν₀ hm₀.1
    (GlobalTheory.T.moveMatch_of_markRel_of_isLevMove E H Dw l Xo c σ r U g e F ik φ hσ hpq hA hP _ _ _ _ _ _ _ (m₀.div m) hm₀) w n hw f hf f hf
    (fun y y' hy => by
      rw [(GlobalTheory.exists_unique_frMove E H Dw l Xo c _ ν₀ hm₀.1 _ y).2 y y' ν₀ rfl (hy₀ _ y) hy]) _ (h₀.mem_dom hx)
  rw [hc w hw f hf f' hf' hv x hx, this, lact_div]

end Free

section Record

open NumberField IsDedekindDomain CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH
  Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts
open GlobalTheory.Member (FinCong)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def liftGrp (V : HSp D) {r : ℕ} (hr : V.rank = r) (β : GL (Fin r) (EAf D)) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) :
    Subgroup (Formalism.L2.DIV.G0 Pg r × GA D V) where
  carrier := {p | IsLift V hr β Pg p.1 p.2}
  one_mem' := isLift_one V hr β Pg
  mul_mem' := by
    rintro ⟨g, κ⟩ ⟨g', κ'⟩ ⟨a, h, b⟩ ⟨a', h', b'⟩
    refine ⟨mul_mem a a', by rw [Prod.snd_mul, map_mul]; exact mul_mem h h', fun w => ?_⟩
    have := map_mul (Formalism.L2.DIV.redAt β w.1) ⟨_, h⟩ ⟨_, h'⟩
    rw [b, b'] at this
    refine Eq.trans (congrArg _ (Subtype.ext ?_)) this
    exact map_mul (finR V hr) κ κ'
  inv_mem' := by
    rintro ⟨g, κ⟩ ⟨a, h, b⟩
    refine ⟨inv_mem a, by rw [Prod.snd_inv, map_inv]; exact inv_mem h, fun w => ?_⟩
    have := map_inv (Formalism.L2.DIV.redAt β w.1) ⟨_, h⟩
    rw [b] at this
    refine Eq.trans (congrArg _ (Subtype.ext ?_)) this
    exact map_inv (finR V hr) κ

variable {G : Type} [Group G]

end Record

end GlobalTheory.GeoLevel
end
end
