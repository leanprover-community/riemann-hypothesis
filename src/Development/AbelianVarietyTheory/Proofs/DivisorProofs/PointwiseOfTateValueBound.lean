import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelPAdicComparison
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPointPairingCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelPAdicComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BLieLieComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointOnModelPullbackCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackTangentCombination

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem htAt_dualFam_frame : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint → TateSt → ValueSt →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (τ : Psi H) (p : ℕ) [Fact p.Prime]
    [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ n : ℕ,
    ∀ (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → l'.A = p ^ n →
    ∀ (N : ℕ) (a : Fin N → Dw.La) (T S : Ind Dw τ.1 → Fin N → c'.V W), LatData Dw (embV c' W (conjEmb τ.1)) a T S →
    ∀ [Algebra c.F ℂ_[p]] (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
      (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (y : FrPt Xo c ℂ_[p]), HTAt Y r ν yb yy P π ψ y →
      ∀ (β : c'.V W →+* 𝓞_ℂ_[p]), yb ≫ Y.s = spMap β →
      ∃ (ta : Fin N → P.T) (w₁ : Fin (Dw.mult τ.1) → P.V) (w₂ : Fin (Dw.mult (conjEmb τ.1)) → P.V)
        (σ : Equiv.Perm (Ind Dw τ.1)),
        (∀ m, ((ta m).lev n).left ≫ ψ = yy ≫ (Y.oF.etaA (a m)).left) ∧
        (∀ k, w₁ k ∈ htLat c P τ.1 ∧ w₁ k ∈ Submodule.span ℂ_[p] (Set.range P.bLie) ∧
          w₁ k ∈ P.eigV (embInt c P.integers τ.1)) ∧
        (∀ k, w₂ k ∈ htLat c P (conjEmb τ.1) ∧ w₂ k ∈ Submodule.span ℂ_[p] (Set.range P.bLie) ∧
          w₂ k ∈ P.eigV (embInt c P.integers (conjEmb τ.1))) ∧
        ‖(Matrix.of fun k k' => P.pairV (w₁ k) (∑ m, (β (T (σ (Sum.inl k')) m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m)).det‖ = 1 ∧
        ‖(Matrix.of fun k k' => P.pairV (w₂ k) (∑ m, (β (S (σ (Sum.inr k')) m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m)).det‖ = 1 := by
  intro hK hTate hVal E _ _ _ H Dw τ p _ _ hs n l l' Xo Xo' c c' W Y r ν hle hOv hA N a T S hLat _ yb yy P π ψ y hHT β hβ
  obtain ⟨ta, u, hlev, hDF⟩ := hTate E H Dw l' Xo' c' W Y p n hs hA yb yy P π ψ hHT.1 β (conjEmb τ.1) (Ind Dw τ.1)
    N a T S hLat
  rw [htAt_embV_eq E H Dw l l' Xo Xo' c c' W Y r ν hle hOv p yb yy P π ψ y hHT β hβ (conjEmb τ.1)] at hDF
  obtain ⟨hPt, -, -, z, g, a0, x, -, -, -, hTie, hLB⟩ := hHT
  obtain ⟨-, -, hπ, hψpb, hgen, -⟩ := hPt
  have hact : ∀ b, (P.oA.act b).left ≫ ψ = ψ ≫ (Y.oF.t.act.act b).left := fun b =>
    Y.m.cart.1.hom_ext
      (by rw [Category.assoc, Category.assoc, Y.m.act, hgen, ← Category.assoc ψ, hgen, ← Category.assoc, P.gen_act,
        Category.assoc, hπ, Category.assoc])
      (by rw [Category.assoc, Category.assoc, Over.w, hψpb.1.w, Over.w_assoc])
  have hact2 : ∀ b, (P.oA.act b).left ≫ (ψ ≫ ν.φ) = (ψ ≫ ν.φ) ≫ (Xo.univ.t.act.act b).left := fun b => by
    rw [← Category.assoc, hact, Category.assoc, ν.act, Category.assoc]
  have hpb2 := hψpb.comp ν.cart
  have heig : ∀ σ j, AvDefs.IsEig P.Gt P.oGt (embInt c P.integers σ) (x σ j) := fun σ j b =>
    ((hTie σ j).act b (hact2 b)).unique hpb2.1
      (by rw [z.eig σ j b, ← algebraMap_embInt P.integers]; exact (hTie σ j).scale _)
  have hK' := (hK p ℂ_[p] Valued.v 𝓞_ℂ_[p] (𝓞 E) P).2.2.2
  have hspan : ∀ σ i, (∑ j, g σ i j • P.bLie (x σ j)) ∈ Submodule.span ℂ_[p] (Set.range P.bLie) := fun σ i =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have heigV : ∀ σ i, (∑ j, g σ i j • P.bLie (x σ j)) ∈ P.eigV (embInt c P.integers σ) := fun σ i =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (bLie_mem_eigV (heig σ j))
  have hmem : ∀ σ i, (∑ j, g σ i j • P.bLie (x σ j)) ∈ htLat c P σ := fun σ i =>
    ((hLB σ).2.le (Submodule.subset_span ⟨i, rfl⟩)).1
  have horth : ∀ k k', P.pairV (∑ j, g τ.1 k j • P.bLie (x τ.1 j))
      (∑ j, g (conjEmb τ.1) k' j • P.bLie (x (conjEmb τ.1) j)) = 0 := fun k k' => by
    have h1 : (∑ j, g τ.1 k j • P.bLie (x τ.1 j)) ∈ P.W := hK'.2.2.2.2.2.2 ▸ hspan _ _
    exact (hK'.2.2.2.2.1 _).1 h1 _ (hK'.2.2.2.2.2.2 ▸ hspan _ _)
  obtain ⟨lam, hlam, hsgn, σ, hσ⟩ := hVal E H Dw l c p hs P τ _ _ u hDF _ _ (fun k => heigV _ k) (fun k => heigV _ k)
    horth (hLB τ.1) (hLB (conjEmb τ.1))
  refine ⟨ta, _, _, σ, hlev, fun k => ⟨hmem _ k, hspan _ k, heigV _ k⟩, fun k => ⟨hmem _ k, hspan _ k, heigV _ k⟩,
    hσ, ?_⟩
  have e := congrArg norm (hsgn σ)
  have hs1 : ‖((Equiv.Perm.sign σ : ℤ) : ℂ_[p])‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [norm_mul, norm_mul, hlam, hσ, hs1, _root_.one_mul, _root_.one_mul] at e
  exact e.symm

end GlobalTheory.FlatModel
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_level_p_power_frame : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint → TateSt → ValueSt →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (τ : Psi H) (p : ℕ) [Fact p.Prime]
    [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ n : ℕ,
    ∀ (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → l'.A = p ^ n →
    ∀ (N : ℕ) (a : Fin N → Dw.La) (T S : Ind Dw τ.1 → Fin N → c'.V W), LatData Dw (embV c' W (conjEmb τ.1)) a T S →
    ∀ [Algebra c.F ℂ_[p]] (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
      (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (y : FrPt Xo c ℂ_[p]), HTAt Y r ν yb yy P π ψ y →
      ∀ (β : c'.V W →+* 𝓞_ℂ_[p]), yb ≫ Y.s = spMap β →
      ∃ (ta : Fin N → P.T) (w₁ : Fin (Dw.mult τ.1) → P.V) (w₂ : Fin (Dw.mult (conjEmb τ.1)) → P.V)
        (σ : Equiv.Perm (Ind Dw τ.1)),
        (∀ m, ((ta m).lev n).left ≫ ψ = yy ≫ (Y.oF.etaA (a m)).left) ∧
        (∀ k, w₁ k ∈ htLat c P τ.1 ∧ w₁ k ∈ Submodule.span ℂ_[p] (Set.range P.bLie) ∧
          w₁ k ∈ P.eigV (embInt c P.integers τ.1)) ∧
        (∀ k, w₂ k ∈ htLat c P (conjEmb τ.1) ∧ w₂ k ∈ Submodule.span ℂ_[p] (Set.range P.bLie) ∧
          w₂ k ∈ P.eigV (embInt c P.integers (conjEmb τ.1))) ∧
        ‖(Matrix.of fun k k' => P.pairV (w₁ k) (∑ m, (β (T (σ (Sum.inl k')) m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m)).det‖ = 1 ∧
        ‖(Matrix.of fun k k' => P.pairV (w₂ k) (∑ m, (β (S (σ (Sum.inr k')) m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m)).det‖ = 1 := by
  atlas_forward_decl GlobalTheory.FlatModel.htAt_dualFam_frame
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_point_pairing_compatible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime]
    [StarRing (𝓞 E)] (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
    (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left), PtOn Y yb yy P π ψ →
    (∀ u : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left, IsTanAtG Y.t yb u → ∃! x : LieG P.Gt, ITie P π x u) ∧
    (∀ x : LieG P.Gt, ∃ u, IsTanAtG Y.t yb u ∧ ITie P π x u) ∧
    (∀ (m : ℕ) (v : Fin m → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left)) (xs : Fin m → LieG P.Gt) (cf : Fin m → 𝓞_ℂ_[p])
      (u : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left) (x : LieG P.Gt), (∀ i, IsTanAtG Y.t yb (v i)) →
      (∀ i, ITie P π (xs i) (v i)) → IsCombAtG Y.t yb v cf u → ITie P π x u →
      P.bLie x = ∑ i, (cf i : ℂ_[p]) • P.bLie (xs i)) ∧
    ∀ (σ : 𝓞 E →+* 𝓞_ℂ_[p]) (x : LieG P.Gt) (u : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left), IsTanAtG Y.t yb u →
      ITie P π x u → (IsEigG Y.t σ u ↔ AvDefs.IsEig P.Gt P.oGt σ x) := by
  first | exact @GlobalTheory.FlatModel.tanTie | exact GlobalTheory.FlatModel.tanTie | (intros; apply GlobalTheory.FlatModel.tanTie <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem htAt_discr_smul_eigen_mem_span_rows : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime]
    [StarRing (𝓞 E)] (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle →
    ∀ [Algebra c.F ℂ_[p]] (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
      (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (y : FrPt Xo c ℂ_[p]), HTAt Y r ν yb yy P π ψ y →
      ∀ (β : c'.V W →+* 𝓞_ℂ_[p]), yb ≫ Y.s = spMap β →
      ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left)), IsTanBasis Y.t yb e →
      ∃ x : Fin g → LieG P.Gt, (∀ b, ITie P π (x b) (e b)) ∧
        ∀ (σ : E →+* ℂ) (U : Fin g → Fin g → 𝓞_ℂ_[p]), EigAt Y.t yb (β.comp (embV c' W σ)) e U →
        ∀ x' : LieG P.Gt, AvDefs.IsEig P.Gt P.oGt (embInt c P.integers σ) x' →
        ∃ M : Fin g → 𝓞_ℂ_[p], ((discr E : ℤ) : ℂ_[p]) • P.bLie x' =
          ∑ k, (M k : ℂ_[p]) • ∑ b, (U k b : ℂ_[p]) • P.bLie (x b) := by
  intro E _ _ _ H Dw p _ _ l l' Xo Xo' c c' W Y r ν hle hOI _ yb yy P π ψ y hHT β hβ g e hB
  have hPt : PtOn Y yb yy P π ψ := hHT.1
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.p_adic_point_pairing_compatible E H Dw p l' Xo' c' W Y yb yy P π ψ hPt
  choose x hx using fun b => (h1 (e b) (hB.1 b)).exists
  refine ⟨x, hx, ?_⟩
  intro σ U hEig x' hx'
  obtain ⟨u', hu'T, hu'X⟩ := h2 x'
  have hemb := GlobalTheory.FlatModel.htAt_embV_eq E H Dw l l' Xo Xo' c c' W Y r ν hle hOI p yb yy P π ψ y hHT β hβ σ
  have hEG : IsEigG Y.t (β.comp (embV c' W σ)) u' := by
    rw [hemb]
    exact (h4 _ x' u' hu'T hu'X).2 hx'
  have hid : spMap (RingHom.id 𝓞_ℂ_[p]) ≫ yb = yb := by
    rw [show spMap (RingHom.id 𝓞_ℂ_[p]) = 𝟙 _ from Spec.map_id _, Category.id_comp]
  have hdual : (fun i => spMap (dualMap (RingHom.id 𝓞_ℂ_[p])) ≫ e i) = e := by
    have : dualMap (RingHom.id 𝓞_ℂ_[p]) = RingHom.id _ := by
      ext s <;> simp [dualMap]
    funext i
    rw [this, show spMap (RingHom.id (DualNumber 𝓞_ℂ_[p])) = 𝟙 _ from Spec.map_id _, Category.id_comp]
  obtain ⟨w, hw, -⟩ := hB.2 𝓞_ℂ_[p] (RingHom.id _) u' (by rw [hid]; exact hu'T)
  rw [hid, hdual] at hw
  have hL := h3 g e x w u' x' hB.1 hx hw hu'X
  have hmem := hEig.2 w u' hw hEG
  obtain ⟨M, hM⟩ := (Submodule.mem_span_range_iff_exists_fun 𝓞_ℂ_[p]).1 hmem
  refine ⟨M, ?_⟩
  have hcoord : ∀ b, ((discr E : ℤ) : 𝓞_ℂ_[p]) * w b = ∑ k, M k * U k b := by
    intro b
    have := congrFun hM b
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this.symm
  rw [hL, Finset.smul_sum]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  have := congrArg (fun z : 𝓞_ℂ_[p] => (z : ℂ_[p])) (hcoord b)
  exact_mod_cast this

end GlobalTheory.FlatModel
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_map_over_inclusion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime]
    [StarRing (𝓞 E)] (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle →
    ∀ [Algebra c.F ℂ_[p]] (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
      (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (y : FrPt Xo c ℂ_[p]), HTAt Y r ν yb yy P π ψ y →
      ∀ (β : c'.V W →+* 𝓞_ℂ_[p]), yb ≫ Y.s = spMap β →
      ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left)), IsTanBasis Y.t yb e →
      ∃ x : Fin g → LieG P.Gt, (∀ b, ITie P π (x b) (e b)) ∧
        ∀ (σ : E →+* ℂ) (U : Fin g → Fin g → 𝓞_ℂ_[p]), EigAt Y.t yb (β.comp (embV c' W σ)) e U →
        ∀ x' : LieG P.Gt, AvDefs.IsEig P.Gt P.oGt (embInt c P.integers σ) x' →
        ∃ M : Fin g → 𝓞_ℂ_[p], ((discr E : ℤ) : ℂ_[p]) • P.bLie x' =
          ∑ k, (M k : ℂ_[p]) • ∑ b, (U k b : ℂ_[p]) • P.bLie (x b) := by
  atlas_forward_decl GlobalTheory.FlatModel.htAt_discr_smul_eigen_mem_span_rows
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option autoImplicit false

namespace GlobalTheory.FlatModel.HTCong

theorem norm_natp (p : ℕ) [Fact p.Prime] : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  have e : (p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := (map_natCast _ p).symm
  rw [e, norm_algebraMap', Padic.norm_p]

theorem norm_le_of_mem_span (p : ℕ) [Fact p.Prime] (n : ℕ) (z : 𝓞_ℂ_[p])
    (hz : z ∈ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}) : ‖(z : ℂ_[p])‖ ≤ (p : ℝ)⁻¹ ^ n := by
  obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  have hw : ‖(w : ℂ_[p])‖ ≤ 1 := (GlobalTheory.PadicComplexHost.mem_iff_norm p _).1 w.2
  push_cast
  rw [norm_mul, norm_pow, norm_natp]
  exact mul_le_of_le_one_left (by positivity) hw

end GlobalTheory.FlatModel.HTCong

namespace GlobalTheory.FlatModel.HTCong

theorem pair_comb_congr : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (n N g : ℕ) {J : Type}
    (ta : Fin N → P.T) (x : Fin g → LieG P.Gt) (h : Fin N → Fin g → 𝓞_ℂ_[p]) (Tc : J → Fin N → 𝓞_ℂ_[p])
    (U : Fin g → 𝓞_ℂ_[p]), (∀ m b, h m b - (P.al₀ (ta m)).1 (x b) ∈ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}) → ∀ i : J,
    ‖(((∑ b, (∑ a, Tc i a * h a b) * U b : 𝓞_ℂ_[p]) : ℂ_[p]) -
      P.pairV (∑ b, (U b : ℂ_[p]) • P.bLie (x b)) (∑ m, (Tc i m : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m))‖ ≤ (p : ℝ)⁻¹ ^ n := by
  intro E _ _ p _ _ P n N g J ta x h Tc U hh i
  have key : P.pairV (∑ b, (U b : ℂ_[p]) • P.bLie (x b)) (∑ m, (Tc i m : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m) =
      ((∑ b, (∑ a, Tc i a * (P.al₀ (ta a)).1 (x b)) * U b : 𝓞_ℂ_[p]) : ℂ_[p]) := by
    have e1 : ∀ m, (Tc i m : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m = (Tc i m : ℂ_[p]) • ((1 : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m) := by
      intro m; rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    simp only [e1, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, P.pairV_bLie, smul_eq_mul]
    push_cast
    simp only [Finset.sum_mul, Finset.mul_sum]
    have ha : ∀ z : 𝓞_ℂ_[p], algebraMap 𝓞_ℂ_[p] ℂ_[p] z = (z : ℂ_[p]) := fun _ => rfl
    simp only [ha]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [key, ← AddSubgroupClass.coe_sub]
  refine norm_le_of_mem_span p n _ ?_
  have e2 : (∑ b, (∑ a, Tc i a * h a b) * U b) - (∑ b, (∑ a, Tc i a * (P.al₀ (ta a)).1 (x b)) * U b) =
      ∑ b, ∑ a, (Tc i a * U b) * (h a b - (P.al₀ (ta a)).1 (x b)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← sub_mul, ← Finset.sum_sub_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [e2]
  exact Ideal.sum_mem _ fun b _ => Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (hh a b)

end GlobalTheory.FlatModel.HTCong
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_pairing_approximation : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (n N g : ℕ) {J : Type}
    (ta : Fin N → P.T) (x : Fin g → LieG P.Gt) (h : Fin N → Fin g → 𝓞_ℂ_[p]) (Tc : J → Fin N → 𝓞_ℂ_[p])
    (U : Fin g → 𝓞_ℂ_[p]), (∀ m b, h m b - (P.al₀ (ta m)).1 (x b) ∈ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}) → ∀ i : J,
    ‖(((∑ b, (∑ a, Tc i a * h a b) * U b : 𝓞_ℂ_[p]) : ℂ_[p]) -
      P.pairV (∑ b, (U b : ℂ_[p]) • P.bLie (x b)) (∑ m, (Tc i m : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m))‖ ≤ (p : ℝ)⁻¹ ^ n := by
  atlas_forward_decl GlobalTheory.FlatModel.HTCong.pair_comb_congr
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

namespace GlobalTheory.MinorBound

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem norm_det_le_one {m : ℕ} (B : Matrix (Fin m) (Fin m) K) (hB : ∀ i j, ‖B i j‖ ≤ 1) :
    ‖B.det‖ ≤ 1 := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp only [h, one_smul, Units.neg_smul, norm_neg] <;>
  · rw [norm_prod]; exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => hB _ _

theorem norm_prod_sub_prod_le {Idx : Type*} (s : Finset Idx) (x y : Idx → K) {ε : ℝ} (hε : 0 ≤ ε)
    (hx : ∀ i, ‖x i‖ ≤ 1) (hy : ∀ i, ‖y i‖ ≤ 1) (hxy : ∀ i, ‖x i - y i‖ ≤ ε) :
    ‖∏ i ∈ s, x i - ∏ i ∈ s, y i‖ ≤ ε := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hε
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have : x a * ∏ i ∈ s, x i - y a * ∏ i ∈ s, y i
        = x a * (∏ i ∈ s, x i - ∏ i ∈ s, y i) + (x a - y a) * ∏ i ∈ s, y i := by ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]; nlinarith [hx a, ih, norm_nonneg (x a), norm_nonneg (∏ i ∈ s, x i - ∏ i ∈ s, y i)]
    · rw [norm_mul, norm_prod]
      have h1 : ∏ i ∈ s, ‖y i‖ ≤ 1 := Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => hy i
      nlinarith [hxy a, norm_nonneg (x a - y a), Finset.prod_nonneg fun i (_ : i ∈ s) => norm_nonneg (y i)]

theorem norm_det_sub_det_le {m : ℕ} (B C : Matrix (Fin m) (Fin m) K) {ε : ℝ} (hε : 0 ≤ ε)
    (hB : ∀ i j, ‖B i j‖ ≤ 1) (hC : ∀ i j, ‖C i j‖ ≤ 1) (hBC : ∀ i j, ‖B i j - C i j‖ ≤ ε) :
    ‖B.det - C.det‖ ≤ ε := by
  rw [Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hε fun σ _ => ?_
  rw [← smul_sub]
  have := norm_prod_sub_prod_le Finset.univ (fun i => B (σ i) i) (fun i => C (σ i) i) hε
    (fun i => hB _ _) (fun i => hC _ _) (fun i => hBC _ _)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp only [h, one_smul, Units.neg_smul, norm_neg] <;>
    exact this

theorem det_mul_expand {m g : ℕ} (M : Matrix (Fin m) (Fin g) K) (A : Matrix (Fin g) (Fin m) K) :
    (M * A).det = ∑ κ : Fin m → Fin g, (∏ i, M i (κ i)) * (Matrix.of fun k j => A (κ k) j).det := by
  classical
  have h1 : (M * A) = fun i => ∑ k, M i k • A k := by
    ext i j; simp [Matrix.mul_apply, Finset.sum_apply]
  have h2 := (Matrix.detRowAlternating : (Fin m → K) [⋀^Fin m]→ₗ[K] K).toMultilinearMap.map_sum
    (fun i k => M i k • A k)
  simp only [AlternatingMap.coe_multilinearMap] at h2
  rw [Matrix.det, h1, h2]
  refine Finset.sum_congr rfl fun f _ => ?_
  have h3 := (Matrix.detRowAlternating : (Fin m → K) [⋀^Fin m]→ₗ[K] K).toMultilinearMap.map_smul_univ
    (fun i => M i (f i)) (fun i => A (f i))
  simp only [AlternatingMap.coe_multilinearMap] at h3
  rw [h3, smul_eq_mul]
  rfl

theorem exists_minor_ge (p : ℕ) [hp : Fact p.Prime] (n m g : ℕ) (d : ℂ_[p]) (A Cc : Fin g → Fin m → ℂ_[p])
    (G : Matrix (Fin m) (Fin m) ℂ_[p]) (M : Fin m → Fin g → ℂ_[p]) (hd : d ≠ 0)
    (hCc : ∀ k j, ‖Cc k j‖ ≤ 1) (hCA : ∀ k j, ‖Cc k j - A k j‖ ≤ (p : ℝ)⁻¹ ^ n)
    (hM : ∀ i k, ‖M i k‖ ≤ 1) (hG : ‖G.det‖ = 1) (hrel : ∀ i j, d * G i j = ∑ k, M i k * A k j) :
    ∃ K : Fin m → Fin g, ‖d‖ ^ m ≤ ‖(Matrix.of fun k j => A (K k) j).det‖ ∧
      ‖(Matrix.of fun k j => A (K k) j).det‖ ≤ 1 ∧
      ‖(Matrix.of fun k j => Cc (K k) j).det - (Matrix.of fun k j => A (K k) j).det‖ ≤ (p : ℝ)⁻¹ ^ n := by
  have hε : 0 ≤ (p : ℝ)⁻¹ ^ n := by positivity
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hε1 : (p : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hp1)
  have hA : ∀ k j, ‖A k j‖ ≤ 1 := fun k j => by
    have h : A k j = Cc k j + -(Cc k j - A k j) := by ring
    rw [h]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hCc k j) ?_)
    rw [norm_neg]; exact (hCA k j).trans hε1
  have hdet : d ^ m * G.det = (Matrix.of M * Matrix.of A).det := by
    have h : d • G = Matrix.of M * Matrix.of A := by
      ext i j; simp [Matrix.mul_apply, hrel]
    rw [← h, Matrix.det_smul, Fintype.card_fin]
  rw [det_mul_expand] at hdet
  have hGne : G.det ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hG; exact zero_ne_one hG
  by_cases hne : Nonempty (Fin m → Fin g)
  · obtain ⟨K0, hK0⟩ := Finite.exists_max (fun κ : Fin m → Fin g => ‖(Matrix.of fun k j => A (κ k) j).det‖)
    refine ⟨K0, ?_, norm_det_le_one _ fun i j => hA _ _,
      norm_det_sub_det_le _ _ hε (fun i j => hCc _ _) (fun i j => hA _ _) (fun i j => hCA _ _)⟩
    have h1 : ‖d‖ ^ m = ‖d ^ m * G.det‖ := by rw [norm_mul, norm_pow, hG, _root_.mul_one]
    rw [h1, hdet]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun κ _ => ?_
    rw [norm_mul, norm_prod]
    have hP : ∏ i, ‖Matrix.of M i (κ i)‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => hM _ _
    calc (∏ i, ‖Matrix.of M i (κ i)‖) * ‖(Matrix.of fun k j => Matrix.of A (κ k) j).det‖
        ≤ 1 * ‖(Matrix.of fun k j => A (κ k) j).det‖ :=
          mul_le_mul_of_nonneg_right hP (norm_nonneg _)
      _ ≤ _ := by rw [_root_.one_mul]; exact hK0 κ
  · exfalso
    haveI : IsEmpty (Fin m → Fin g) := not_nonempty_iff.mp hne
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hdet
    exact mul_ne_zero (pow_ne_zero _ hd) hGne hdet

end GlobalTheory.MinorBound
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_minor_norm_det_bounds_and_det_sub_le : ∀ (p : ℕ) [Fact p.Prime] (n m g : ℕ) (d : ℂ_[p]) (A Cc : Fin g → Fin m → ℂ_[p]) (G : Matrix (Fin m) (Fin m) ℂ_[p])
    (M : Fin m → Fin g → ℂ_[p]), d ≠ 0 → (∀ k j, ‖Cc k j‖ ≤ 1) → (∀ k j, ‖Cc k j - A k j‖ ≤ (p : ℝ)⁻¹ ^ n) →
    (∀ i k, ‖M i k‖ ≤ 1) → ‖G.det‖ = 1 → (∀ i j, d * G i j = ∑ k, M i k * A k j) →
    ∃ K : Fin m → Fin g, ‖d‖ ^ m ≤ ‖(Matrix.of fun k j => A (K k) j).det‖ ∧
      ‖(Matrix.of fun k j => A (K k) j).det‖ ≤ 1 ∧
      ‖(Matrix.of fun k j => Cc (K k) j).det - (Matrix.of fun k j => A (K k) j).det‖ ≤ (p : ℝ)⁻¹ ^ n := by
  atlas_forward_decl GlobalTheory.MinorBound.exists_minor_ge
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatModel

theorem lt_norm_mul_of_close {K : Type} [NormedField K] [IsUltrametricDist K] {a₁ a₂ c₁ c₂ : K} {ε : ℝ}
    (h₂ : ‖a₂‖ ≤ 1) (hc₁ : ‖c₁ - a₁‖ ≤ ε) (hc₂ : ‖c₂ - a₂‖ ≤ ε) (hε1 : ε ≤ 1) (h₁ : ‖a₁‖ ≤ 1)
    (hε : ε < ‖a₁ * a₂‖) : ε < ‖c₁ * c₂‖ := by
  have hc2 : ‖c₂‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (c₂ - a₂) a₂
    rw [sub_add_cancel] at this
    exact this.trans (max_le (hc₂.trans hε1) h₂)
  have e : c₁ * c₂ - a₁ * a₂ = (c₁ - a₁) * c₂ + a₁ * (c₂ - a₂) := by ring
  have hd : ‖c₁ * c₂ - a₁ * a₂‖ ≤ ε := by
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_mul hc₁ hc2 (norm_nonneg _) ((norm_nonneg _).trans hc₁)).trans_eq (mul_one ε)
    · rw [norm_mul]
      exact (mul_le_mul h₁ hc₂ (norm_nonneg _) zero_le_one).trans_eq (one_mul ε)
  have := IsUltrametricDist.norm_add_le_max (a₁ * a₂ - c₁ * c₂) (c₁ * c₂)
  rw [sub_add_cancel, norm_sub_rev] at this
  rcases le_max_iff.1 this with h | h
  · exact absurd (hε.trans_le h) (not_lt.2 hd)
  · exact hε.trans_le h

theorem exists_large_minors : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint → TateSt → ValueSt → BoundSt →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (τ : Psi H) (p : ℕ) [Fact p.Prime]
    [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ n : ℕ,
    ∀ (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → l'.A = p ^ n →
    ∀ (N : ℕ) (a : Fin N → Dw.La) (T S : Ind Dw τ.1 → Fin N → c'.V W), LatData Dw (embV c' W (conjEmb τ.1)) a T S →
    ∀ [Algebra c.F ℂ_[p]] (f : Rul Xo c) (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
      (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (y : FrPt Xo c ℂ_[p]), HTAt Y r ν yb yy P π ψ y →
      (p : ℝ)⁻¹ ^ n < ‖((((discr E : ℤ) : ℂ_[p]) ^ 2 * (p : ℂ_[p]) ^ 2) ^ (Dw.mult τ.1 + Dw.mult (conjEmb τ.1)))‖ →
      ∀ (β : c'.V W →+* 𝓞_ℂ_[p]), yb ≫ Y.s = spMap β →
      ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left)) (U₁ U₂ : Fin g → Fin g → 𝓞_ℂ_[p])
        (h : Fin N → Fin g → 𝓞_ℂ_[p]), IsTanBasis Y.t yb e → EigAt Y.t yb (β.comp (embV c' W τ.1)) e U₁ →
        EigAt Y.t yb (β.comp (embV c' W (conjEmb τ.1))) e U₂ → HTApprox Y n yy P π ψ a e h →
        ∃ (σ : Equiv.Perm (Ind Dw τ.1)) (K₁ : Fin (Dw.mult τ.1) → Fin g) (K₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g),
          ((p : ℝ)⁻¹ ^ n < ‖((pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) *
        pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) : ℂ_[p])‖) := by
  intro hKer hTate hVal hBound E _ _ _ H Dw τ p _ _ hs n l l' Xo Xo' c c' W Y r ν hle hov hA N a T S hLat _ f yb yy P π ψ y
    hHT hn β hβ g e U₁ U₂ h hTan hE₁ hE₂ hApp
  obtain ⟨ta, w₁, w₂, σ, hta, hw₁, hw₂, hG₁, hG₂⟩ :=
    GlobalTheory.T.integral_model_level_p_power_frame hKer hTate hVal E H Dw τ p hs n l l' Xo Xo' c c' W Y r ν hle hov hA N a T S hLat yb yy P π ψ y
      hHT β hβ
  obtain ⟨x, hx, hM⟩ := GlobalTheory.T.integral_model_map_over_inclusion E H Dw p l l' Xo Xo' c c' W Y r ν hle hov yb yy P π ψ y hHT β hβ g e hTan
  have hCB : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.CokernelBound P := (hKer p ℂ_[p] _ 𝓞_ℂ_[p] (𝓞 E) P).2.2.1
  set d : ℂ_[p] := ((discr E : ℤ) : ℂ_[p]) with hd
  have hnorm : ∀ z : 𝓞_ℂ_[p], ‖(z : ℂ_[p])‖ ≤ 1 := fun z => (GlobalTheory.PadicComplexHost.mem_iff_norm p _).1 z.2
  have hd0 : d ^ 2 * (p : ℂ_[p]) ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero _ (Int.cast_ne_zero.2 (NumberField.discr_ne_zero E)))
    (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))
  have hε1 : (p : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by positivity)
    (inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le))

  have key : ∀ (σ' : E →+* ℂ) (U : Fin g → Fin g → 𝓞_ℂ_[p]), EigAt Y.t yb (β.comp (embV c' W σ')) e U →
      ∀ w : P.V, w ∈ htLat c P σ' → w ∈ Submodule.span ℂ_[p] (Set.range P.bLie) →
        w ∈ P.eigV (embInt c P.integers σ') → ∃ M : Fin g → 𝓞_ℂ_[p],
          (d ^ 2 * (p : ℂ_[p]) ^ 2) • w = ∑ k, (M k : ℂ_[p]) • ∑ b, (U k b : ℂ_[p]) • P.bLie (x b) := by
    intro σ' U hU w h1 h2 h3
    obtain ⟨x', hx'e, hx'⟩ := hBound E H l c p P hCB σ' w h1 h2 h3
    obtain ⟨M, hM'⟩ := hM σ' U hU x' hx'e
    refine ⟨M, ?_⟩
    rw [← hM', hx', smul_smul]
    congr 1
    ring
  choose M₁ hM₁ using fun i => key τ.1 U₁ hE₁ (w₁ i) (hw₁ i).1 (hw₁ i).2.1 (hw₁ i).2.2
  choose M₂ hM₂ using fun i => key (conjEmb τ.1) U₂ hE₂ (w₂ i) (hw₂ i).1 (hw₂ i).2.1 (hw₂ i).2.2
  have hcong : ∀ (U : Fin g → 𝓞_ℂ_[p]) (Tc : Ind Dw τ.1 → Fin N → 𝓞_ℂ_[p]) (i : Ind Dw τ.1),
      ‖(((∑ b, (∑ a, Tc i a * h a b) * U b : 𝓞_ℂ_[p]) : ℂ_[p]) -
        P.pairV (∑ b, (U b : ℂ_[p]) • P.bLie (x b)) (∑ m, (Tc i m : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m))‖ ≤ (p : ℝ)⁻¹ ^ n :=
    fun U Tc i => GlobalTheory.T.p_adic_pairing_approximation E p P n N g ta x h Tc U (fun m b => hApp m (ta m) (hta m) b (x b) (hx b)) i
  have hpair : ∀ (M : Fin g → 𝓞_ℂ_[p]) (X : Fin g → P.V) (t : P.V),
      P.pairV (∑ k, (M k : ℂ_[p]) • X k) t = ∑ k, (M k : ℂ_[p]) * P.pairV (X k) t := by
    intro M X t
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  obtain ⟨K₁, hK₁, hK₁', hK₁''⟩ := GlobalTheory.T.exists_minor_norm_det_bounds_and_det_sub_le p n (Dw.mult τ.1) g (d ^ 2 * (p : ℂ_[p]) ^ 2)
    (fun k j => P.pairV (∑ b, (U₁ k b : ℂ_[p]) • P.bLie (x b))
      (∑ m, ((β (T (σ (Sum.inl j)) m) : 𝓞_ℂ_[p]) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m))
    (fun k j => ((∑ b, covec β T h (σ ∘ Sum.inl) j b * U₁ k b : 𝓞_ℂ_[p]) : ℂ_[p]))
    (Matrix.of fun k k' => P.pairV (w₁ k) (∑ m, (β (T (σ (Sum.inl k')) m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m))
    (fun i k => (M₁ i k : ℂ_[p])) hd0 (fun k j => hnorm _)
    (fun k j => hcong (U₁ k) (fun i a => β (T i a)) (σ (Sum.inl j))) (fun i k => hnorm _) hG₁
    (fun i j => by
      rw [Matrix.of_apply, ← smul_eq_mul, ← LinearMap.smul_apply, ← map_smul, hM₁ i, hpair])
  obtain ⟨K₂, hK₂, hK₂', hK₂''⟩ := GlobalTheory.T.exists_minor_norm_det_bounds_and_det_sub_le p n (Dw.mult (conjEmb τ.1)) g (d ^ 2 * (p : ℂ_[p]) ^ 2)
    (fun k j => P.pairV (∑ b, (U₂ k b : ℂ_[p]) • P.bLie (x b))
      (∑ m, ((β (S (σ (Sum.inr j)) m) : 𝓞_ℂ_[p]) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m))
    (fun k j => ((∑ b, covec β S h (σ ∘ Sum.inr) j b * U₂ k b : 𝓞_ℂ_[p]) : ℂ_[p]))
    (Matrix.of fun k k' => P.pairV (w₂ k) (∑ m, (β (S (σ (Sum.inr k')) m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m))
    (fun i k => (M₂ i k : ℂ_[p])) hd0 (fun k j => hnorm _)
    (fun k j => hcong (U₂ k) (fun i a => β (S i a)) (σ (Sum.inr j))) (fun i k => hnorm _) hG₂
    (fun i j => by
      rw [Matrix.of_apply, ← smul_eq_mul, ← LinearMap.smul_apply, ← map_smul, hM₂ i, hpair])
  refine ⟨σ, K₁, K₂, ?_⟩
  have e₁ : ((pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) : 𝓞_ℂ_[p]) : ℂ_[p]) =
      (Matrix.of fun k j => ((∑ b, covec β T h (σ ∘ Sum.inl) j b * U₁ (K₁ k) b : 𝓞_ℂ_[p]) : ℂ_[p])).det := by
    change algebraMap 𝓞_ℂ_[p] ℂ_[p] (Matrix.det _) = _
    rw [RingHom.map_det]
    rfl
  have e₂ : ((pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) : ℂ_[p]) =
      (Matrix.of fun k j => ((∑ b, covec β S h (σ ∘ Sum.inr) j b * U₂ (K₂ k) b : 𝓞_ℂ_[p]) : ℂ_[p])).det := by
    change algebraMap 𝓞_ℂ_[p] ℂ_[p] (Matrix.det _) = _
    rw [RingHom.map_det]
    rfl
  change (p : ℝ)⁻¹ ^ n < ‖((pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) : 𝓞_ℂ_[p]) : ℂ_[p]) *
    ((pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) : ℂ_[p])‖
  rw [e₁, e₂]
  refine lt_norm_mul_of_close hK₂' hK₁'' hK₂'' hε1 hK₁' (hn.trans_le ?_)
  rw [pow_add, norm_mul, norm_pow, norm_pow]
  exact (mul_le_mul hK₁ hK₂ (by positivity) (norm_nonneg _)).trans_eq (norm_mul _ _).symm

end GlobalTheory.FlatModel
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_level_p_power : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint → TateSt → ValueSt → BoundSt →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (τ : Psi H) (p : ℕ) [Fact p.Prime]
    [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ n : ℕ,
    ∀ (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → l'.A = p ^ n →
    ∀ (N : ℕ) (a : Fin N → Dw.La) (T S : Ind Dw τ.1 → Fin N → c'.V W), LatData Dw (embV c' W (conjEmb τ.1)) a T S →
    ∀ [Algebra c.F ℂ_[p]] (f : Rul Xo c) (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
      (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (y : FrPt Xo c ℂ_[p]), HTAt Y r ν yb yy P π ψ y →
      (p : ℝ)⁻¹ ^ n < ‖((((discr E : ℤ) : ℂ_[p]) ^ 2 * (p : ℂ_[p]) ^ 2) ^ (Dw.mult τ.1 + Dw.mult (conjEmb τ.1)))‖ →
      ∀ (β : c'.V W →+* 𝓞_ℂ_[p]), yb ≫ Y.s = spMap β →
      ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left)) (U₁ U₂ : Fin g → Fin g → 𝓞_ℂ_[p])
        (h : Fin N → Fin g → 𝓞_ℂ_[p]), IsTanBasis Y.t yb e → EigAt Y.t yb (β.comp (embV c' W τ.1)) e U₁ →
        EigAt Y.t yb (β.comp (embV c' W (conjEmb τ.1))) e U₂ → HTApprox Y n yy P π ψ a e h →
        ∃ (σ : Equiv.Perm (Ind Dw τ.1)) (K₁ : Fin (Dw.mult τ.1) → Fin g) (K₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g),
          ((p : ℝ)⁻¹ ^ n < ‖((pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) *
        pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) : ℂ_[p])‖) := by
  atlas_forward_decl GlobalTheory.FlatModel.exists_large_minors
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

open RetractionModules in

theorem exists_iTie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype)
    (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
    (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left), PtOn Y yb yy P π ψ →
    ∀ u : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left, IsTanAtG Y.t yb u → ∃ x : LieG P.Gt, ITie P π x u := by
  intro E _ _ _ H Dw l' Xo' c' W Y p _ _ yb yy P π ψ hP u hu
  obtain ⟨xG, hxG⟩ := tan_lift hP.2.1 hu
  obtain ⟨x, hx⟩ := exists_corr_left xG
  exact ⟨x, xG, hx, hxG⟩

end GlobalTheory.FlatModel
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_point_frame_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype)
    (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
    (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left), PtOn Y yb yy P π ψ →
    ∀ u : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left, IsTanAtG Y.t yb u → ∃ x : LieG P.Gt, ITie P π x u := by
  atlas_forward_decl GlobalTheory.FlatModel.exists_iTie
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatModel

theorem pt_isEig_of_lieTie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _))
    (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] [Algebra c.F ℂ_[p]] (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c')
    (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left), PtOn Y yb yy P π ψ →
    ∀ (σ : E →+* ℂ) (x : LieG P.Gt) (u : Sp (DualNumber ℂ_[p]) ⟶ Xo.univ.t.G.left),
      LieTie P (ψ ≫ ν.φ) x u → IsEigAt c σ u → AvDefs.IsEig P.Gt P.oGt (embInt c P.integers σ) x := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν p _ _ _ yb yy P π ψ hP σ x u h hu
  obtain ⟨-, -, h2, h3, h4, -⟩ := hP
  have hpb : IsGrpPullback P.A.A Xo.univ.t.G (yy ≫ r ≫ pullback.fst _ _) (ψ ≫ ν.φ) := h3.comp ν.cart
  have hact : ∀ a, (P.oA.act a).left ≫ (ψ ≫ ν.φ) = (ψ ≫ ν.φ) ≫ (Xo.univ.t.act.act a).left := fun a => by
    have e : (P.oA.act a).left ≫ ψ = ψ ≫ (Y.oF.t.act.act a).left := Y.m.cart.1.hom_ext
      (by rw [Category.assoc, Category.assoc, Y.m.act, h4, ← Category.assoc ψ, h4, ← Category.assoc, P.gen_act,
        Category.assoc, h2, Category.assoc])
      (by rw [Category.assoc, Category.assoc, Over.w, h3.1.w, Over.w_assoc])
    rw [← Category.assoc, e, Category.assoc, Category.assoc, ν.act]
  intro a
  exact (h.act a (hact a)).unique hpb.1 (by rw [hu a, ← algebraMap_embInt P.integers]; exact h.scale _)

end GlobalTheory.FlatModel

end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_point_complete_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _))
    (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] [Algebra c.F ℂ_[p]] (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c')
    (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left), PtOn Y yb yy P π ψ →
    ∀ (σ : E →+* ℂ) (x : LieG P.Gt) (u : Sp (DualNumber ℂ_[p]) ⟶ Xo.univ.t.G.left),
      LieTie P (ψ ≫ ν.φ) x u → IsEigAt c σ u → AvDefs.IsEig P.Gt P.oGt (embInt c P.integers σ) x := by
  atlas_forward_decl GlobalTheory.FlatModel.pt_isEig_of_lieTie
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option autoImplicit false

namespace GlobalTheory.FlatModel.TieComb

open GlobalTheory.HTLat.OmegaRank

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {p : ℕ} [Fact p.Prime] [StarRing (𝓞 E)] {P : PtP E p}

theorem corr_lieComb : ∀ {g : ℕ} (U : Fin g → 𝓞_ℂ_[p]) (xb : Fin g → LieG P.Gt) (xG : Fin g → LieG P.G),
    (∀ b, Corr P (xb b).1 (xG b).1) → Corr P (lieComb P.Gt U xb).1 (lieComb P.G U xG).1
  | 0, _, _, _, _ => Corr.one
  | g + 1, U, xb, xG, h => by
    rw [lieComb_succ, lieComb_succ]
    exact Corr.mul (Corr.comp (dualScale (U 0)) (h 0))
      (corr_lieComb (Fin.tail U) (Fin.tail xb) (Fin.tail xG) fun b => h b.succ)

variable {yb : Sp 𝓞_ℂ_[p] ⟶ X} {π : P.G.left ⟶ t.G.left}

theorem prod_push (hP : IsGrpPullback P.G t.G yb π) :
    ∀ {g : ℕ} (U : Fin g → 𝓞_ℂ_[p]) (xG : Fin g → LieG P.G),
    (List.ofFn fun i => pushPt hP.1.w (AvDefs.lieScale P.G (U i) (xG i)).1).prod.left =
      (lieComb P.G U xG).1.left ≫ π
  | 0, U, xG => by
    rw [List.ofFn_zero, List.prod_nil, lieComb_zero]
    exact grpPull_one hP _
  | g + 1, U, xG => by
    rw [List.ofFn_succ, List.prod_cons, lieComb_succ]
    exact hP.2 _ _ _ _ _ rfl (prod_push hP (Fin.tail U) (Fin.tail xG))

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0})
    (t : SAB H X) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (yb : Sp 𝓞_ℂ_[p] ⟶ X) (π : P.G.left ⟶ t.G.left),
    IsGrpPullback P.G t.G yb π → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ t.G.left)) (xb : Fin g → LieG P.Gt),
    (∀ b, ITie P π (xb b) (e b)) → ∀ U : Fin g → 𝓞_ℂ_[p],
    ∃ u0 : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ t.G.left, IsCombAtG t yb e U u0 ∧ ITie P π (lieComb P.Gt U xb) u0 := by
  intro E _ _ _ H X t p _ _ P yb π hP g e xb hT U
  choose xG hc he using hT
  refine ⟨(lieComb P.G U xG).1.left ≫ π, ⟨fun i => pushPt hP.1.w (AvDefs.lieScale P.G (U i) (xG i)).1, fun i => ?_,
    prod_push hP U xG⟩, lieComb P.G U xG, corr_lieComb U xb xG hc, rfl⟩
  rw [← he i]
  rfl

end GlobalTheory.FlatModel.TieComb
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_combination_lie_group_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0})
    (t : SAB H X) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (yb : Sp 𝓞_ℂ_[p] ⟶ X) (π : P.G.left ⟶ t.G.left),
    IsGrpPullback P.G t.G yb π → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ t.G.left)) (xb : Fin g → LieG P.Gt),
    (∀ b, ITie P π (xb b) (e b)) → ∀ U : Fin g → 𝓞_ℂ_[p],
    ∃ u0 : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ t.G.left, IsCombAtG t yb e U u0 ∧ ITie P π (lieComb P.Gt U xb) u0 := by
  atlas_forward_decl GlobalTheory.FlatModel.TieComb.main
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatModel.BaseChangeComb

theorem comp_listProd' {B : Scheme.{0}} {G : Over B} [GrpObj G] {T T' : Over B} (f : T' ⟶ T) (L : List (T ⟶ G)) :
    f ≫ L.prod = (L.map (f ≫ ·)).prod := by
  induction L with
  | nil => exact MonObj.comp_one f
  | cons a L ih => rw [List.prod_cons, MonObj.comp_mul, ih, List.map_cons, List.prod_cons]

theorem dualMap_comp_epsMul' {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (a : R) :
    (dualMap φ).comp (epsMul a) = (epsMul (φ a)).comp (dualMap φ) := by
  apply RingHom.ext
  intro r
  ext <;> simp [dualMap, epsMul, _root_.mul_comm]

theorem bc_comb_eig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0})
    (t : SAB H X) (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (x : Sp R ⟶ X) (g : ℕ)
    (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) (U : Fin g → R) (σ : 𝓞 E →+* R) (u : Sp (DualNumber R) ⟶ t.G.left),
    (IsCombAtG t x e U u → IsCombAtG t (spMap φ ≫ x) (bcV t φ e) (fun b => φ (U b)) (spMap (dualMap φ) ≫ u)) ∧
    (IsEigG t σ u → IsEigG t (φ.comp σ) (spMap (dualMap φ) ≫ u)) := by
  intro E _ _ _ H X t R S _ _ φ x g e U σ u
  refine ⟨fun h => ?_, fun h a => ?_⟩
  · obtain ⟨w, hw, hp⟩ := h
    have he : spMap (dualMap φ) ≫ (tEpsG x).hom = (tEpsG (spMap φ ≫ x)).hom := by
      show spMap (dualMap φ) ≫ spMap (algebraMap R (DualNumber R)) ≫ x =
        spMap (algebraMap S (DualNumber S)) ≫ spMap φ ≫ x
      rw [← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]
      congr 2
      apply RingHom.ext
      intro r
      ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    let bc : tEpsG (spMap φ ≫ x) ⟶ tEpsG x := Over.homMk (spMap (dualMap φ)) he
    refine ⟨fun i => bc ≫ w i, fun i => ?_, ?_⟩
    · show spMap (dualMap φ) ≫ (w i).left = spMap (epsMul (φ (U i))) ≫ spMap (dualMap φ) ≫ e i
      rw [hw i, ← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp, dualMap_comp_epsMul']
    · have hl : (List.ofFn fun i => bc ≫ w i) = (List.ofFn w).map (bc ≫ ·) := by
        rw [List.map_ofFn]
        rfl
      rw [hl, ← comp_listProd', Over.comp_left, hp]
      rfl
  · show (spMap (dualMap φ) ≫ u) ≫ (t.act.act a).left = spMap (epsMul (φ (σ a))) ≫ spMap (dualMap φ) ≫ u
    rw [Category.assoc, h a, ← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp, dualMap_comp_epsMul']

end GlobalTheory.FlatModel.BaseChangeComb

end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCombAtG_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0})
    (t : SAB H X) (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (x : Sp R ⟶ X) (g : ℕ)
    (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) (U : Fin g → R) (σ : 𝓞 E →+* R) (u : Sp (DualNumber R) ⟶ t.G.left),
    (IsCombAtG t x e U u → IsCombAtG t (spMap φ ≫ x) (bcV t φ e) (fun b => φ (U b)) (spMap (dualMap φ) ≫ u)) ∧
    (IsEigG t σ u → IsEigG t (φ.comp σ) (spMap (dualMap φ) ≫ u)) := by
  atlas_forward_decl GlobalTheory.FlatModel.BaseChangeComb.bc_comb_eig
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.point_on_model_pullback_compatible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype)
    (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
    (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left), PtOn Y yb yy P π ψ →
    ∀ (X : LieG P.Gt) (u0 : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left), ITie P π X u0 →
    ∃ w : Sp (DualNumber ℂ_[p]) ⟶ Y.oF.t.G.left,
      w ≫ Y.m.φ = spMap (dualMap (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ u0 ∧
      w ≫ Y.oF.t.G.hom = spMap (algebraMap ℂ_[p] (DualNumber ℂ_[p])) ≫ yy ∧
      spMap (TrivSqZeroExt.fstHom ℂ_[p] ℂ_[p] ℂ_[p]).toRingHom ≫ w = (1 : Over.mk yy ⟶ Y.oF.t.G).left ∧
      LieTie P ψ X w := by
  first | exact @GlobalTheory.FlatModel.LiftW.liftW | exact GlobalTheory.FlatModel.LiftW.liftW | (intros; apply GlobalTheory.FlatModel.LiftW.liftW <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem spMap_epsMul_algebraMap {R : Type} [CommRing R] (s : R) :
    spMap (epsMul s) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R (DualNumber R)) := by
  rw [spMap, spMap, ← Spec.map_comp]
  congr 1
  ext x
  · simp [epsMul]
  · simp [epsMul, TrivSqZeroExt.map]

theorem tanEig_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]]
    (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (y : FrPt Xo c ℂ_[p]), GlobalTheory.AllWt.ptF y = yy ≫ r →
    ∀ w : Sp (DualNumber ℂ_[p]) ⟶ Y.oF.t.G.left, w ≫ Y.oF.t.G.hom = spMap (algebraMap ℂ_[p] (DualNumber ℂ_[p])) ≫ yy →
    spMap (TrivSqZeroExt.fstHom ℂ_[p] ℂ_[p] ℂ_[p]).toRingHom ≫ w = (1 : Over.mk yy ⟶ Y.oF.t.G).left →
    ∀ σ : E →+* ℂ, (∀ a : 𝓞 E, (w ≫ Y.m.φ) ≫ (Y.t.act.act a).left =
      spMap (epsMul (algebraMap c.F ℂ_[p] (embK c σ a))) ≫ w ≫ Y.m.φ) →
    IsTanAt y.x (w ≫ ν.φ) ∧ IsEigAt c σ (w ≫ ν.φ) := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν p _ _ yy y hy w hw h1 σ he
  have hx : yy ≫ r ≫ pullback.fst _ _ = y.x := by
    have h0 : GlobalTheory.AllWt.ptF y ≫ pullback.fst _ _ = y.x := pullback.lift_fst _ _ _
    rw [hy, Category.assoc] at h0
    exact h0
  have hsq : ν.φ ≫ Xo.univ.t.G.hom = Y.oF.t.G.hom ≫ r ≫ pullback.fst _ _ := ν.cart.1.w
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, hsq, ← Category.assoc, hw, Category.assoc, hx]
  · let T : Over (Xo'.XF c') := Over.mk yy
    have hu : ((1 : T ⟶ Y.oF.t.G).left ≫ ν.φ) ≫ Xo.univ.t.G.hom = T.hom ≫ (r ≫ pullback.fst _ _) := by
      rw [Category.assoc, hsq, ← Category.assoc, Over.w]
    let x₀ : Over.mk (T.hom ≫ (r ≫ pullback.fst _ _)) ⟶ Xo.univ.t.G := Over.homMk ((1 : T ⟶ Y.oF.t.G).left ≫ ν.φ) hu
    have hm := ν.cart.2 T 1 1 x₀ x₀ rfl rfl
    have hxx : x₀ * x₀ = x₀ * 1 := by
      rw [_root_.mul_one]
      ext1
      rw [hm, _root_.mul_one]
      rfl
    have h11 : x₀ = 1 := mul_left_cancel hxx
    have key : ∀ (m m' : Sp ℂ_[p] ⟶ Xo.X), m = m' →
        (1 : Over.mk m ⟶ Xo.univ.t.G).left = (1 : Over.mk m' ⟶ Xo.univ.t.G).left := by
      rintro _ _ rfl; rfl
    rw [← Category.assoc, h1]
    have : x₀.left = (1 : Over.mk (T.hom ≫ (r ≫ pullback.fst _ _)) ⟶ Xo.univ.t.G).left := by rw [h11]
    exact this.trans (key _ _ hx)
  · intro a
    have hA : w ≫ (Y.oF.t.act.act a).left =
        spMap (epsMul (algebraMap c.F ℂ_[p] (embK c σ a))) ≫ w := by
      apply Y.m.cart.1.hom_ext
      · rw [Category.assoc, Y.m.act a, ← Category.assoc, he a, Category.assoc]
      · rw [Category.assoc, Over.w, hw, Category.assoc, hw, ← Category.assoc, spMap_epsMul_algebraMap]
    rw [Category.assoc, ← ν.act a, ← Category.assoc, hA, Category.assoc]

end GlobalTheory.FlatModel
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_point_model_abelian_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]]
    (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (y : FrPt Xo c ℂ_[p]), GlobalTheory.AllWt.ptF y = yy ≫ r →
    ∀ w : Sp (DualNumber ℂ_[p]) ⟶ Y.oF.t.G.left, w ≫ Y.oF.t.G.hom = spMap (algebraMap ℂ_[p] (DualNumber ℂ_[p])) ≫ yy →
    spMap (TrivSqZeroExt.fstHom ℂ_[p] ℂ_[p] ℂ_[p]).toRingHom ≫ w = (1 : Over.mk yy ⟶ Y.oF.t.G).left →
    ∀ σ : E →+* ℂ, (∀ a : 𝓞 E, (w ≫ Y.m.φ) ≫ (Y.t.act.act a).left =
      spMap (epsMul (algebraMap c.F ℂ_[p] (embK c σ a))) ≫ w ≫ Y.m.φ) →
    IsTanAt y.x (w ≫ ν.φ) ∧ IsEigAt c σ (w ≫ ν.φ) := by
  atlas_forward_decl GlobalTheory.FlatModel.tanEig_of_model
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGrpPullback_tangent_combination : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (S0 : Scheme.{0})
    (t : SAB H S0) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (x0 : Sp ℂ_[p] ⟶ S0)
    (ψ' : P.A.A.left ⟶ t.G.left), IsGrpPullback P.A.A t.G x0 ψ' →
    ∀ (m : ℕ) (xs : Fin m → LieG P.Gt) (us : Fin m → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)) (a : Fin m → 𝓞_ℂ_[p])
      (u : Sp (DualNumber ℂ_[p]) ⟶ t.G.left), (∀ i, LieTie P ψ' (xs i) (us i)) →
      IsCombAtG t x0 us (fun i => algebraMap 𝓞_ℂ_[p] ℂ_[p] (a i)) u → LieTie P ψ' (lieComb P.Gt a xs) u := by
  first | exact @GlobalTheory.FlatModel.lieTie_lieComb | exact GlobalTheory.FlatModel.lieTie_lieComb | (intros; apply GlobalTheory.FlatModel.lieTie_lieComb <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatModel

theorem exists_denom (p : ℕ) [Fact p.Prime] : ∀ (m : ℕ) (d : Fin m → ℂ_[p]), ∃ δ : 𝓞_ℂ_[p],
    (δ : ℂ_[p]) ≠ 0 ∧ ∀ l, (δ : ℂ_[p]) * d l ∈ 𝓞_ℂ_[p] := by
  intro m
  induction m with
  | zero => exact fun d => ⟨1, by simp, fun l => l.elim0⟩
  | succ m ih =>
    intro d
    obtain ⟨δ, hδ, hl⟩ := ih (Fin.tail d)
    by_cases ha : (δ : ℂ_[p]) * d 0 ∈ 𝓞_ℂ_[p]
    · refine ⟨δ, hδ, fun l => ?_⟩
      refine Fin.cases ha (fun l => ?_) l
      exact hl l
    · have hne : (δ : ℂ_[p]) * d 0 ≠ 0 := fun h => ha (h ▸ (𝓞_ℂ_[p]).zero_mem)
      have hinv : ((δ : ℂ_[p]) * d 0)⁻¹ ∈ 𝓞_ℂ_[p] := ((𝓞_ℂ_[p]).mem_or_inv_mem _).resolve_left ha
      refine ⟨δ * ⟨_, hinv⟩, ?_, fun l => ?_⟩
      · change (δ : ℂ_[p]) * ((δ : ℂ_[p]) * d 0)⁻¹ ≠ 0
        exact mul_ne_zero hδ (inv_ne_zero hne)
      · change (δ : ℂ_[p]) * ((δ : ℂ_[p]) * d 0)⁻¹ * d l ∈ 𝓞_ℂ_[p]
        refine Fin.cases ?_ (fun l => ?_) l
        · rw [show (δ : ℂ_[p]) * ((δ : ℂ_[p]) * d 0)⁻¹ * d 0 = 1 by
            rw [_root_.mul_comm (δ : ℂ_[p]), _root_.mul_assoc]; exact inv_mul_cancel₀ hne]
          exact (𝓞_ℂ_[p]).one_mem
        · rw [show (δ : ℂ_[p]) * ((δ : ℂ_[p]) * d 0)⁻¹ * d l.succ = ((δ : ℂ_[p]) * d 0)⁻¹ * ((δ : ℂ_[p]) * Fin.tail d l) by
            simp only [Fin.tail]; ring]
          exact (𝓞_ℂ_[p]).mul_mem _ _ hinv (hl l)

theorem exists_denom_alg : ∀ (p : ℕ) [Fact p.Prime] (m : ℕ) (d : Fin m → ℂ_[p]), ∃ δ : 𝓞_ℂ_[p],
    algebraMap 𝓞_ℂ_[p] ℂ_[p] δ ≠ 0 ∧ ∀ l, ∃ e : 𝓞_ℂ_[p], algebraMap 𝓞_ℂ_[p] ℂ_[p] e = algebraMap 𝓞_ℂ_[p] ℂ_[p] δ * d l := by
  intro p _ m d
  obtain ⟨δ, hδ, hl⟩ := exists_denom p m d
  exact ⟨δ, hδ, fun l => ⟨⟨_, hl l⟩, rfl⟩⟩

set_option maxHeartbeats 1000000 in

theorem htComb_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle →
    ∀ (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] [Algebra c.F ℂ_[p]] (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c')
      (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (y : FrPt Xo c ℂ_[p]),
      HTAt Y r ν yb yy P π ψ y →
    ∀ (z : FrPt Xo c ℂ_[p]) (gm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ_[p]) (am : ℂ_[p])
      (x : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → LieG P.Gt), GlobalTheory.Frames.FrChg gm am z y →
      (∀ τ j, LieTie P (ψ ≫ ν.φ) (x τ j) (z.u τ j)) →
    ∀ (β : c'.V W →+* 𝓞_ℂ_[p]), yb ≫ Y.s = spMap β →
    ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left)), IsTanBasis Y.t yb e →
    ∀ (xb : Fin g → LieG P.Gt), (∀ b, ITie P π (xb b) (e b)) →
    ∀ (σ : E →+* ℂ) (U : Fin g → 𝓞_ℂ_[p]), (∀ u, IsCombAtG Y.t yb e U u → IsEigG Y.t (β.comp (embV c' W σ)) u) →
    ∃ (w : Sp (DualNumber ℂ_[p]) ⟶ Y.oF.t.G.left) (cf : Fin (Dw.mult σ) → ℂ_[p]),
      IsCombAtG Y.t (yy ≫ Y.j) (bcV Y.t (algebraMap 𝓞_ℂ_[p] ℂ_[p]) e) (fun b => (U b : ℂ_[p])) (w ≫ Y.m.φ) ∧
      IsCombAt y.x (y.u σ) cf (w ≫ ν.φ) ∧
      ∑ b, (U b : ℂ_[p]) • P.bLie (xb b) = ∑ j, cf j • ∑ l, gm σ j l • P.bLie (x σ l) := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle hOI p _ _ _ yb yy P π ψ y hHT z gm am x hchg hx β hβ g e _ xb hxb σ U hU
  obtain ⟨hPt, hTs, hptF, hHC⟩ := hHT
  obtain ⟨u0, hu0c, hu0t⟩ := GlobalTheory.T.exists_combination_lie_group_pullback E H Y.X Y.t p P yb π hPt.2.1 g e xb hxb U
  have hu0e := hU u0 hu0c
  obtain ⟨w, hw1, hw2, hw3, hwt⟩ := GlobalTheory.T.point_on_model_pullback_compatible E H Dw l' Xo' c' W Y p yb yy P π ψ hPt _ u0 hu0t
  have hbc := GlobalTheory.T.isCombAtG_base_change E H Y.X Y.t 𝓞_ℂ_[p] ℂ_[p] (algebraMap 𝓞_ℂ_[p] ℂ_[p]) yb g e U (β.comp (embV c' W σ)) u0
  have hA : IsCombAtG Y.t (yy ≫ Y.j) (bcV Y.t (algebraMap 𝓞_ℂ_[p] ℂ_[p]) e) (fun b => (U b : ℂ_[p])) (w ≫ Y.m.φ) := by
    rw [hw1, ← hPt.1]
    exact hbc.1 hu0c
  have hemb := GlobalTheory.T.integral_model_p_adic_comparison E H Dw l l' Xo Xo' c c' W Y r ν hle hOI p yb yy P π ψ y ⟨hPt, hTs, hptF, hHC⟩ β hβ σ
  have hE : ∀ a : 𝓞 E, (w ≫ Y.m.φ) ≫ (Y.t.act.act a).left =
      spMap (epsMul (algebraMap c.F ℂ_[p] (embK c σ a))) ≫ w ≫ Y.m.φ := by
    intro a
    have h := hbc.2 hu0e a
    have hs : algebraMap 𝓞_ℂ_[p] ℂ_[p] (β (embV c' W σ a)) = algebraMap c.F ℂ_[p] (embK c σ a) := by
      rw [← algebraMap_embInt P.integers σ a, ← hemb]; rfl
    rw [hw1, h, RingHom.comp_apply, RingHom.comp_apply, hs]
  obtain ⟨hT, hEig⟩ := GlobalTheory.T.padic_point_model_abelian_map E H Dw l l' Xo Xo' c c' W Y r ν p yy y hptF w hw2 hw3 σ hE
  obtain ⟨cf, hcf, -⟩ := y.basis σ (w ≫ ν.φ) hT hEig
  refine ⟨w, cf, hA, hcf, ?_⟩
  have hyx : y.x = yy ≫ r ≫ pullback.fst _ _ := by
    rw [← Category.assoc, ← hptF]
    exact (pullback.lift_fst _ _ _).symm
  have hzx : y.x = z.x := hchg.1
  have hψ' : IsGrpPullback P.A.A Xo.univ.t.G z.x (ψ ≫ ν.φ) := by
    rw [← hzx, hyx]
    exact hPt.2.2.2.1.comp ν.cart
  have hXt : LieTie P (ψ ≫ ν.φ) (lieComb P.Gt U xb) (w ≫ ν.φ) := by
    obtain ⟨xG, u', h1, h2, h3⟩ := hwt
    exact ⟨xG, u', h1, by rw [← h2, Category.assoc], h3⟩
  have hdc : IsCombAtG Xo.univ.t z.x (z.u σ) ((Matrix.of fun l j => gm σ j l).mulVec cf) (w ≫ ν.φ) :=
    tanLinG (z.u σ) (fun j => z.tan σ j) (y.u σ) (Matrix.of fun l j => gm σ j l) cf (w ≫ ν.φ)
      (fun j => hchg.2.1 σ j) (hzx ▸ hcf)
  obtain ⟨δ, hδ0, hδ⟩ := exists_denom_alg p _ ((Matrix.of fun l j => gm σ j l).mulVec cf)
  choose ee hee using hδ
  have hsc : IsCombAtG Xo.univ.t z.x (z.u σ) (fun l => algebraMap 𝓞_ℂ_[p] ℂ_[p] (ee l))
      (spMap (epsMul (algebraMap 𝓞_ℂ_[p] ℂ_[p] δ)) ≫ (w ≫ ν.φ)) := by
    have h := (isCombAtG_iff Xo.univ.t z.x (fun j => ovT (z.tan σ j)) _ (w ≫ ν.φ)).1 hdc
    refine (isCombAtG_iff Xo.univ.t z.x (fun j => ovT (z.tan σ j)) _ _).2 ?_
    rw [show (fun l => algebraMap 𝓞_ℂ_[p] ℂ_[p] (ee l)) =
      fun l => algebraMap 𝓞_ℂ_[p] ℂ_[p] δ * (Matrix.of fun l j => gm σ j l).mulVec cf l from funext hee,
      ← smT_combT, smT_left, h]
  have hL1 := hXt.scale δ
  have hL2 := GlobalTheory.T.isGrpPullback_tangent_combination E H Xo.X Xo.univ.t p P z.x (ψ ≫ ν.φ) hψ' _ (x σ) (z.u σ) ee _ (hx σ) hsc
  have heq := hL1.unique hψ'.1 hL2
  have hb := congrArg P.bLie heq
  rw [P.bLie_scale, bLie_lieComb, bLie_lieComb] at hb
  have hb' : algebraMap 𝓞_ℂ_[p] ℂ_[p] δ • ∑ b, (U b : ℂ_[p]) • P.bLie (xb b) =
      algebraMap 𝓞_ℂ_[p] ℂ_[p] δ • ∑ l, (Matrix.of fun l j => gm σ j l).mulVec cf l • P.bLie (x σ l) := by
    have e1 : algebraMap 𝓞_ℂ_[p] ℂ_[p] δ • ∑ b, (U b : ℂ_[p]) • P.bLie (xb b) = δ • ∑ b, U b • P.bLie (xb b) := by
      rw [algebraMap_smul]
      congr 1
    have e2 : ∑ l, ee l • P.bLie (x σ l) =
        algebraMap 𝓞_ℂ_[p] ℂ_[p] δ • ∑ l, (Matrix.of fun l j => gm σ j l).mulVec cf l • P.bLie (x σ l) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_smul, ← hee, algebraMap_smul]
    rw [e1, hb, e2]
  have h2 := smul_right_injective P.V hδ0 hb'
  rw [h2]
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm]

end GlobalTheory.FlatModel

end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_p_adic_over_inclusion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle →
    ∀ (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] [Algebra c.F ℂ_[p]] (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c')
      (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (y : FrPt Xo c ℂ_[p]),
      HTAt Y r ν yb yy P π ψ y →
    ∀ (z : FrPt Xo c ℂ_[p]) (gm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ_[p]) (am : ℂ_[p])
      (x : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → LieG P.Gt), GlobalTheory.Frames.FrChg gm am z y →
      (∀ τ j, LieTie P (ψ ≫ ν.φ) (x τ j) (z.u τ j)) →
    ∀ (β : c'.V W →+* 𝓞_ℂ_[p]), yb ≫ Y.s = spMap β →
    ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left)), IsTanBasis Y.t yb e →
    ∀ (xb : Fin g → LieG P.Gt), (∀ b, ITie P π (xb b) (e b)) →
    ∀ (σ : E →+* ℂ) (U : Fin g → 𝓞_ℂ_[p]), (∀ u, IsCombAtG Y.t yb e U u → IsEigG Y.t (β.comp (embV c' W σ)) u) →
    ∃ (w : Sp (DualNumber ℂ_[p]) ⟶ Y.oF.t.G.left) (cf : Fin (Dw.mult σ) → ℂ_[p]),
      IsCombAtG Y.t (yy ≫ Y.j) (bcV Y.t (algebraMap 𝓞_ℂ_[p] ℂ_[p]) e) (fun b => (U b : ℂ_[p])) (w ≫ Y.m.φ) ∧
      IsCombAt y.x (y.u σ) cf (w ≫ ν.φ) ∧
      ∑ b, (U b : ℂ_[p]) • P.bLie (xb b) = ∑ j, cf j • ∑ l, gm σ j l • P.bLie (x σ l) := by
  atlas_forward_decl GlobalTheory.FlatModel.htComb_lift
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace GlobalTheory.FlatModel

theorem norm_int_le_one {p : ℕ} [Fact p.Prime] (x : 𝓞_ℂ_[p]) : ‖(x : ℂ_[p])‖ ≤ 1 := by
  rw [← coe_valued]
  exact_mod_cast (Valuation.mem_valuationSubring_iff _ _).1 x.2

theorem norm_eq_of_norm_sub_lt {p : ℕ} [Fact p.Prime] {X A : ℂ_[p]} (h : ‖X - A‖ < ‖X‖) : ‖A‖ = ‖X‖ := by
  have h1 : ‖A‖ ≤ max ‖X‖ ‖X - A‖ := by
    have := IsUltrametricDist.norm_add_le_max X (-(X - A))
    rwa [norm_neg, show X + -(X - A) = A by ring] at this
  have h2 : ‖X‖ ≤ max ‖A‖ ‖X - A‖ := by
    have := IsUltrametricDist.norm_add_le_max A (X - A)
    simpa using this
  rcases le_max_iff.1 h2 with h2 | h2
  · exact le_antisymm (h1.trans (max_le le_rfl h.le)) h2
  · exact absurd h (not_lt.2 h2)

theorem norm_quot_sub_lt {p : ℕ} [Fact p.Prime] (n : ℕ) (x y : 𝓞_ℂ_[p]) (A B κ q : ℂ_[p])
    (hbig : (p : ℝ)⁻¹ ^ n < ‖((x * y : 𝓞_ℂ_[p]) : ℂ_[p])‖)
    (hA : ‖(x : ℂ_[p]) - A‖ ≤ (p : ℝ)⁻¹ ^ n) (hB : ‖(y : ℂ_[p]) - B‖ ≤ (p : ℝ)⁻¹ ^ n)
    (hq : q * A = κ * B) (hκ : κ ≠ 0) :
    ‖q * (x : ℂ_[p]) / (y : ℂ_[p]) - κ‖ < ‖κ‖ := by
  have hX1 := norm_int_le_one x
  have hY1 := norm_int_le_one y
  have hbig' : (p : ℝ)⁻¹ ^ n < ‖(x : ℂ_[p])‖ * ‖(y : ℂ_[p])‖ := by
    rw [← norm_mul]; exact_mod_cast hbig
  have hXb : (p : ℝ)⁻¹ ^ n < ‖(x : ℂ_[p])‖ :=
    hbig'.trans_le (mul_le_of_le_one_right (norm_nonneg _) hY1)
  have hYb : (p : ℝ)⁻¹ ^ n < ‖(y : ℂ_[p])‖ :=
    hbig'.trans_le (mul_le_of_le_one_left (norm_nonneg _) hX1)
  have hXA : ‖(x : ℂ_[p]) - A‖ < ‖(x : ℂ_[p])‖ := hA.trans_lt hXb
  have hYB : ‖(y : ℂ_[p]) - B‖ < ‖(y : ℂ_[p])‖ := hB.trans_lt hYb
  have nA := norm_eq_of_norm_sub_lt hXA
  have nB := norm_eq_of_norm_sub_lt hYB
  have hpos : (0 : ℝ) < (p : ℝ)⁻¹ ^ n := by
    have : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    positivity
  have hA0 : A ≠ 0 := fun h0 => by rw [h0, norm_zero] at nA; linarith
  have hB0 : B ≠ 0 := fun h0 => by rw [h0, norm_zero] at nB; linarith
  have hY0 : (y : ℂ_[p]) ≠ 0 := fun h0 => by rw [h0, norm_zero] at hYb; linarith
  have hq' : q = κ * B / A := by rw [eq_div_iff hA0, hq]
  have key : q * (x : ℂ_[p]) / (y : ℂ_[p]) - κ =
      κ * ((((x : ℂ_[p]) - A) * B - A * ((y : ℂ_[p]) - B)) / (A * (y : ℂ_[p]))) := by
    rw [hq']; field_simp; ring
  rw [key, norm_mul]
  have hk : 0 < ‖κ‖ := norm_pos_iff.2 hκ
  refine mul_lt_of_lt_one_right hk ?_
  have hden : 0 < ‖A * (y : ℂ_[p])‖ := norm_pos_iff.2 (mul_ne_zero hA0 hY0)
  rw [norm_div, div_lt_one hden]
  have e1 : ‖((x : ℂ_[p]) - A) * B‖ < ‖A * (y : ℂ_[p])‖ := by
    rw [norm_mul, norm_mul, nA, nB]
    exact mul_lt_mul_of_pos_right hXA (by linarith)
  have e2 : ‖A * ((y : ℂ_[p]) - B)‖ < ‖A * (y : ℂ_[p])‖ := by
    rw [norm_mul, norm_mul]
    exact mul_lt_mul_of_pos_left hYB (by rw [nA]; linarith)
  calc ‖((x : ℂ_[p]) - A) * B - A * ((y : ℂ_[p]) - B)‖
      ≤ max ‖((x : ℂ_[p]) - A) * B‖ ‖A * ((y : ℂ_[p]) - B)‖ := by
        have := IsUltrametricDist.norm_add_le_max (((x : ℂ_[p]) - A) * B) (-(A * ((y : ℂ_[p]) - B)))
        rwa [norm_neg, ← sub_eq_add_neg] at this
    _ < ‖A * (y : ℂ_[p])‖ := max_lt e1 e2

end GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem norm_minor_sub_le {p : ℕ} [Fact p.Prime] {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : PtP E p)
    (n : ℕ) {V J : Type} [CommRing V] (β : V →+* 𝓞_ℂ_[p]) {N g m : ℕ} (T : J → Fin N → V)
    (h : Fin N → Fin g → 𝓞_ℂ_[p]) (ta : Fin N → P.T) (xb : Fin g → LieG P.Gt)
    (hh : ∀ a b, h a b - (P.al₀ (ta a)).1 (xb b) ∈ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n})
    (I : Fin m → J) (U : Fin m → Fin g → 𝓞_ℂ_[p]) :
    ‖((pairDet (covec β T h I) U : 𝓞_ℂ_[p]) : ℂ_[p]) -
      (Matrix.of fun k k' => P.pairV (∑ b, (U k b : ℂ_[p]) • P.bLie (xb b))
        (∑ a, (β (T (I k') a) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta a)).det‖ ≤ (p : ℝ)⁻¹ ^ n := by
  classical
  set Mex : Matrix (Fin m) (Fin m) 𝓞_ℂ_[p] :=
    Matrix.of fun k k' => ∑ b, (∑ a, β (T (I k') a) * (P.al₀ (ta a)).1 (xb b)) * U k b with hMex
  have h1 : pairDet (covec β T h I) U - Mex.det ∈ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n} := by
    rw [← Ideal.Quotient.eq, pairDet, RingHom.map_det, RingHom.map_det]
    congr 1
    ext k k'
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hMex, covec]
    rw [Ideal.Quotient.eq, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun b _ => ?_
    rw [← sub_mul, ← Finset.sum_sub_distrib]
    refine Ideal.mul_mem_right _ _ (Ideal.sum_mem _ fun a _ => ?_)
    rw [← mul_sub]
    exact Ideal.mul_mem_left _ _ (hh a b)
  have e : ∀ (x : LieG P.Gt) (c : ℂ_[p]) (t : P.T),
      P.pairV (P.bLie x) (c ⊗ₜ[ℤ_[p]] t) = c * algebraMap 𝓞_ℂ_[p] ℂ_[p] ((P.al₀ t).1 x) := fun x c t => by
    rw [show (c ⊗ₜ[ℤ_[p]] t : P.V) = c • ((1 : ℂ_[p]) ⊗ₜ[ℤ_[p]] t) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one], map_smul, P.pairV_bLie, smul_eq_mul]
  have h2 : ((Mex.det : 𝓞_ℂ_[p]) : ℂ_[p]) = (Matrix.of fun k k' => P.pairV (∑ b, (U k b : ℂ_[p]) • P.bLie (xb b))
        (∑ a, (β (T (I k') a) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta a)).det := by
    change algebraMap 𝓞_ℂ_[p] ℂ_[p] Mex.det = _
    rw [RingHom.map_det]
    congr 1
    ext k k'
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hMex, map_sum, map_mul, map_smul,
      LinearMap.sum_apply, LinearMap.smul_apply, e, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    change ((β (T (I k') a) : ℂ_[p]) * ((P.al₀ (ta a)).1 (xb b) : ℂ_[p])) * (U k b : ℂ_[p]) =
      (U k b : ℂ_[p]) * ((β (T (I k') a) : ℂ_[p]) * ((P.al₀ (ta a)).1 (xb b) : ℂ_[p]))
    ring
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
  rw [← h2]
  have h3 : ((pairDet (covec β T h I) U : 𝓞_ℂ_[p]) : ℂ_[p]) - ((Mex.det : 𝓞_ℂ_[p]) : ℂ_[p]) =
      (c : ℂ_[p]) * (p : ℂ_[p]) ^ n := by
    have := congrArg (algebraMap 𝓞_ℂ_[p] ℂ_[p]) hc
    rw [map_mul, map_pow, map_natCast, map_sub] at this
    exact this.symm
  rw [h3, norm_mul, norm_pow, GlobalTheory.PadicComplexHost.norm_p]
  exact mul_le_of_le_one_left (by positivity) (norm_int_le_one c)

end GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem kap_close : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint → TateSt → ValueSt → BoundSt →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (τ : Psi H) (p : ℕ) [Fact p.Prime]
    [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ n : ℕ,
    ∀ (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → l'.A = p ^ n →
    ∀ (N : ℕ) (a : Fin N → Dw.La) (T S : Ind Dw τ.1 → Fin N → c'.V W), LatData Dw (embV c' W (conjEmb τ.1)) a T S →
    ∀ [Algebra c.F ℂ_[p]] (f : Rul Xo c) (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
      (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (y : FrPt Xo c ℂ_[p]), HTAt Y r ν yb yy P π ψ y →
      evR Xo c f y ≠ 0 → ∃ κ : ℂ_[p], ‖κ‖ = ‖evR Xo c f y‖ ∧
      ∀ (β : c'.V W →+* 𝓞_ℂ_[p]), yb ≫ Y.s = spMap β →
      ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left)) (U₁ U₂ : Fin g → Fin g → 𝓞_ℂ_[p])
        (h : Fin N → Fin g → 𝓞_ℂ_[p]), IsTanBasis Y.t yb e → EigAt Y.t yb (β.comp (embV c' W τ.1)) e U₁ →
        EigAt Y.t yb (β.comp (embV c' W (conjEmb τ.1))) e U₂ → HTApprox Y n yy P π ψ a e h →
        ∀ (σ : Equiv.Perm (Ind Dw τ.1)) (K₁ : Fin (Dw.mult τ.1) → Fin g) (K₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g),
          ((p : ℝ)⁻¹ ^ n < ‖((pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) *
        pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) : ℂ_[p])‖) →
          ∀ fv : ℂ_[p], GVal Y r ν τ.1 f yy (bcV Y.t (algebraMap 𝓞_ℂ_[p] ℂ_[p]) e) (fun k b => (U₁ (K₁ k) b : ℂ_[p]))
            (fun k b => (U₂ (K₂ k) b : ℂ_[p])) fv →
          ‖fv * ((Equiv.Perm.sign σ : ℤ) : ℂ_[p]) * (pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) : 𝓞_ℂ_[p]) /
            (pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) - κ‖ < ‖κ‖ := by
  classical
  intro hK hT hV _ E _ _ _ H Dw τ p _ _ hs n l l' Xo Xo' c c' W Y r ν hle hov hA N a T S hLD _ f yb yy P π ψ y hHT hev
  have inj : ∀ {A B : Type} [CommRing A] [CommRing B] (f f' : A →+* B), spMap f = spMap f' → f = f' := by
    intro A B _ _ f f' h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : c'.V W →+* 𝓞_ℂ_[p], yb ≫ Y.s = spMap β₀ :=
    ⟨(Spec.preimage (yb ≫ Y.s)).hom, by simp [spMap]⟩
  have hHT' := hHT
  obtain ⟨hPt, hTe, hF, z, gm, am, x, hFC, -, -, htie, hlat⟩ := hHT'
  obtain ⟨ta, u0, hlev, hDF⟩ :=
    hT E H Dw l' Xo' c' W Y p n hs hA yb yy P π ψ hPt β₀ (conjEmb τ.1) (Ind Dw τ.1) N a T S hLD
  rw [GlobalTheory.T.integral_model_p_adic_comparison E H Dw l l' Xo Xo' c c' W Y r ν hle hov p yb yy P π ψ y hHT β₀ hβ₀] at hDF
  have heig : ∀ σ j, AvDefs.IsEig P.Gt P.oGt (embInt c P.integers σ) (x σ j) := fun σ j =>
    GlobalTheory.T.p_adic_point_complete_field E H Dw l l' Xo Xo' c c' W Y r ν p yb yy P π ψ hPt σ (x σ j) (z.u σ j) (htie σ j) (z.eig σ j)
  have hmemE : ∀ σ k, ∑ j, gm σ k j • P.bLie (x σ j) ∈ P.eigV (embInt c P.integers σ) := fun σ k =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (bLie_mem_eigV (heig σ j))
  have hKS := (hK p ℂ_[p] _ 𝓞_ℂ_[p] (𝓞 E) P).2.2.2
  have hmemW : ∀ σ k, ∑ j, gm σ k j • P.bLie (x σ j) ∈ P.W := fun σ k => by
    rw [hKS.2.2.2.2.2.2]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  set w₁ : Fin (Dw.mult τ.1) → P.V := fun k => ∑ j, gm τ.1 k j • P.bLie (x τ.1 j) with hw₁
  set w₂ : Fin (Dw.mult (conjEmb τ.1)) → P.V := fun k => ∑ j, gm (conjEmb τ.1) k j • P.bLie (x (conjEmb τ.1) j)
    with hw₂
  have horth : ∀ k k', P.pairV (w₁ k) (w₂ k') = 0 := fun k k' =>
    (hKS.2.2.2.2.1 _).1 (hmemW _ k) _ (hmemW _ k')
  obtain ⟨lam, hlam, hlamσ, -⟩ :=
    hV E H Dw l c p hs P τ _ _ u0 hDF w₁ w₂ (hmemE _) (hmemE _) horth (hlat _) (hlat _)
  refine ⟨lam * evR Xo c f y, by rw [norm_mul, hlam, _root_.one_mul], ?_⟩
  intro β hβ g e U₁ U₂ h htb hE1 hE2 happ σ K₁ K₂ hbig fv hGV
  have hββ : β = β₀ := inj _ _ (hβ.symm.trans hβ₀)
  subst hββ
  choose xb hxb using fun b => GlobalTheory.T.p_adic_point_frame_map E H Dw l' Xo' c' W Y p yb yy P π ψ hPt (e b) (htb.1 b)
  have hh : ∀ m b, h m b - (P.al₀ (ta m)).1 (xb b) ∈ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n} := fun m b =>
    happ m (ta m) (hlev m) b (xb b) (hxb b)
  have G1 := fun k => GlobalTheory.T.integral_model_p_adic_over_inclusion E H Dw l l' Xo Xo' c c' W Y r ν hle hov p yb yy P π ψ y hHT z gm am x hFC
    htie β hβ g e htb xb hxb τ.1 (U₁ (K₁ k)) (fun u hu => hE1.1 (K₁ k) u hu)
  have G2 := fun k => GlobalTheory.T.integral_model_p_adic_over_inclusion E H Dw l l' Xo Xo' c c' W Y r ν hle hov p yb yy P π ψ y hHT z gm am x hFC
    htie β hβ g e htb xb hxb (conjEmb τ.1) (U₂ (K₂ k)) (fun u hu => hE2.1 (K₂ k) u hu)
  choose v₁ cf₁ hv₁ hcf₁ hid₁ using G1
  choose v₂ cf₂ hv₂ hcf₂ hid₂ using G2
  have hfv := hGV y hTe hF v₁ v₂ (Matrix.of cf₁) (Matrix.of cf₂) hv₁ hv₂ hcf₁ hcf₂
  have fac : ∀ {m : ℕ} (cf : Fin m → Fin m → ℂ_[p]) (w : Fin m → P.V) (tt : Fin m → P.V)
      (L : Fin m → Fin g → 𝓞_ℂ_[p]), (∀ k, ∑ b, (L k b : ℂ_[p]) • P.bLie (xb b) = ∑ j, cf k j • w j) →
      (Matrix.of fun k k' => P.pairV (∑ b, (L k b : ℂ_[p]) • P.bLie (xb b)) (tt k')).det =
        (Matrix.of cf).det * (Matrix.of fun k k' => P.pairV (w k) (tt k')).det := by
    intro m cf w tt L hL
    rw [← Matrix.det_mul]
    congr 1
    ext k k'
    simp only [Matrix.of_apply, Matrix.mul_apply, hL, map_sum, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul]
  set M₁ := (Matrix.of fun k k' => P.pairV (w₁ k)
    ((fun i => ∑ m, (β (T i m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m) (σ (Sum.inl k')))).det with hM₁
  set M₂ := (Matrix.of fun k k' => P.pairV (w₂ k)
    ((fun i => ∑ m, (β (S i m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m) (σ (Sum.inr k')))).det with hM₂
  have hl : ((Equiv.Perm.sign σ : ℤ) : ℂ_[p]) * M₁ = lam * M₂ := hlamσ σ
  have hA₁ : ‖((pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) : 𝓞_ℂ_[p]) : ℂ_[p]) - (Matrix.of cf₁).det * M₁‖ ≤
      (p : ℝ)⁻¹ ^ n :=
    (congrArg (fun d => ‖((pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) : 𝓞_ℂ_[p]) : ℂ_[p]) - d‖)
      (fac cf₁ w₁ (fun k' => ∑ m, (β (T (σ (Sum.inl k')) m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m) (U₁ ∘ K₁) hid₁).symm).trans_le
      (norm_minor_sub_le P n β T h ta xb hh (σ ∘ Sum.inl) (U₁ ∘ K₁))
  have hB₁ : ‖((pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) : ℂ_[p]) - (Matrix.of cf₂).det * M₂‖ ≤
      (p : ℝ)⁻¹ ^ n :=
    (congrArg (fun d => ‖((pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) : ℂ_[p]) - d‖)
      (fac cf₂ w₂ (fun k' => ∑ m, (β (S (σ (Sum.inr k')) m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m) (U₂ ∘ K₂) hid₂).symm).trans_le
      (norm_minor_sub_le P n β S h ta xb hh (σ ∘ Sum.inr) (U₂ ∘ K₂))
  have hlam0 : lam ≠ 0 := fun h0 => by rw [h0, norm_zero] at hlam; exact zero_ne_one hlam
  refine norm_quot_sub_lt n _ _ _ _ _ _ hbig hA₁ hB₁ ?_ (mul_ne_zero hlam0 hev)
  linear_combination (((Equiv.Perm.sign σ : ℤ) : ℂ_[p]) * M₁) * hfv + ((Matrix.of cf₂).det * evR Xo c f y) * hl

end GlobalTheory.FlatModel
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_level_p_power_tangent : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint → TateSt → ValueSt → BoundSt →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (τ : Psi H) (p : ℕ) [Fact p.Prime]
    [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ n : ℕ,
    ∀ (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → l'.A = p ^ n →
    ∀ (N : ℕ) (a : Fin N → Dw.La) (T S : Ind Dw τ.1 → Fin N → c'.V W), LatData Dw (embV c' W (conjEmb τ.1)) a T S →
    ∀ [Algebra c.F ℂ_[p]] (f : Rul Xo c) (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
      (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (y : FrPt Xo c ℂ_[p]), HTAt Y r ν yb yy P π ψ y →
      evR Xo c f y ≠ 0 → ∃ κ : ℂ_[p], ‖κ‖ = ‖evR Xo c f y‖ ∧
      ∀ (β : c'.V W →+* 𝓞_ℂ_[p]), yb ≫ Y.s = spMap β →
      ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left)) (U₁ U₂ : Fin g → Fin g → 𝓞_ℂ_[p])
        (h : Fin N → Fin g → 𝓞_ℂ_[p]), IsTanBasis Y.t yb e → EigAt Y.t yb (β.comp (embV c' W τ.1)) e U₁ →
        EigAt Y.t yb (β.comp (embV c' W (conjEmb τ.1))) e U₂ → HTApprox Y n yy P π ψ a e h →
        ∀ (σ : Equiv.Perm (Ind Dw τ.1)) (K₁ : Fin (Dw.mult τ.1) → Fin g) (K₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g),
          ((p : ℝ)⁻¹ ^ n < ‖((pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) *
        pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) : ℂ_[p])‖) →
          ∀ fv : ℂ_[p], GVal Y r ν τ.1 f yy (bcV Y.t (algebraMap 𝓞_ℂ_[p] ℂ_[p]) e) (fun k b => (U₁ (K₁ k) b : ℂ_[p]))
            (fun k b => (U₂ (K₂ k) b : ℂ_[p])) fv →
          ‖fv * ((Equiv.Perm.sign σ : ℤ) : ℂ_[p]) * (pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) : 𝓞_ℂ_[p]) /
            (pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) - κ‖ < ‖κ‖ := by
  atlas_forward_decl GlobalTheory.FlatModel.kap_close
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem ptSt_of_steps : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint → TateSt → ValueSt → BoundSt → PtSt := by
  intro hK hT hV hB E _ _ _ H Dw τ p _ _ hs
  have hpos : (0 : ℝ) < ‖((((discr E : ℤ) : ℂ_[p]) ^ 2 * (p : ℂ_[p]) ^ 2) ^ (Dw.mult τ.1 + Dw.mult (conjEmb τ.1)))‖ := by
    refine norm_pos_iff.2 (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ ?_) (pow_ne_zero _ ?_)))
    · exact Int.cast_ne_zero.2 (NumberField.discr_ne_zero E)
    · exact Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos hp1
  refine ⟨n, ?_⟩
  intro l l' Xo Xo' c c' W Y r ν hle hOI hA N a T S hLat _ f yb yy P π ψ y hHT hf
  obtain ⟨κ, hκ, hcl⟩ := GlobalTheory.T.integral_model_level_p_power_tangent hK hT hV hB E H Dw τ p hs n l l' Xo Xo' c c' W Y r ν hle hOI hA N a T S hLat f
    yb yy P π ψ y hHT hf
  exact ⟨κ, hκ, fun β hβ g e U₁ U₂ h h1 h2 h3 h4 =>
    ⟨GlobalTheory.T.integral_model_level_p_power hK hT hV hB E H Dw τ p hs n l l' Xo Xo' c c' W Y r ν hle hOI hA N a T S hLat f yb yy P π ψ y hHT hn
      β hβ g e U₁ U₂ h h1 h2 h3 h4, hcl β hβ g e U₁ U₂ h h1 h2 h3 h4⟩⟩

end GlobalTheory.FlatModel
end
end

open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointwise_of_tate_value_bound : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint → TateSt → ValueSt → BoundSt → PtSt := by
  atlas_forward_decl GlobalTheory.FlatModel.ptSt_of_steps
end
