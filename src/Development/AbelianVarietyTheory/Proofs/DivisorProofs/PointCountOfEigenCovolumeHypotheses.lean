import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionFrameInvariance
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueStatementHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepLatZero

section
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.ShFam.Descent

namespace GlobalTheory.DetHT

theorem lieTie_frameOf_of_ptAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F))
    (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]] (P z : FrPt Xo c ℂ_[p]) (yb : Sp 𝓞_ℂ_[p] ⟶ Z.X),
    GlobalTheory.AllWt.ptF z = GlobalTheory.AllWt.ptF P →
    letI := H.starRing; ∀ (Q : PtP E p) (π : Q.G.left ⟶ Z.t.G.left) (ψ : Q.A.A.left ⟶ Z.oF.t.G.left),
      PtAt Z yb (GlobalTheory.AllWt.ptF P) Q π ψ → ∀ (σ : E →+* ℂ) (j : Fin (Dw.mult σ)) (xx : LieG Q.Gt),
      LieTie Q (ψ ≫ Z.m0.toSABMap.φ) xx (z.u σ j) → LieTie Q (Q.gen ≫ π) xx ((frameOf Z z).v σ j) := by
  intro E _ _ _ H Dw l Xo c Z p _ _ P z yb hz Q π ψ hP σ j xx h
  obtain ⟨xG, u', h1, h2, h3⟩ := h
  refine ⟨xG, u', h1, ?_, h3⟩
  obtain ⟨w, a1, a2, a3⟩ := (tie_frameOf Z z).2.2 σ j
  have hw := Over.w u'
  have hψ := hP.2.2.2.1.1.w
  have h5 := hP.2.2.2.2
  have hb : w ≫ Z.oF.t.G.hom = (Over.Hom.left u' ≫ ψ) ≫ Z.oF.t.G.hom := by
    rw [a1, Category.assoc, hψ, ← Category.assoc, hw, hz]
    rfl
  have hm : w ≫ Z.m0.φ = (Over.Hom.left u' ≫ ψ) ≫ Z.m0.φ := by
    rw [a2, Category.assoc, h2]
  have hwe := Z.m0.toSABMap.cart.1.hom_ext hm hb
  rw [← h5, ← Category.assoc, ← hwe, a3]

end GlobalTheory.DetHT
end

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.ShFam.Descent

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_frobenius_point_comparison : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F))
    (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]] (P z : FrPt Xo c ℂ_[p]) (yb : Sp 𝓞_ℂ_[p] ⟶ Z.X),
    GlobalTheory.AllWt.ptF z = GlobalTheory.AllWt.ptF P →
    letI := H.starRing; ∀ (Q : PtP E p) (π : Q.G.left ⟶ Z.t.G.left) (ψ : Q.A.A.left ⟶ Z.oF.t.G.left),
      PtAt Z yb (GlobalTheory.AllWt.ptF P) Q π ψ → ∀ (σ : E →+* ℂ) (j : Fin (Dw.mult σ)) (xx : LieG Q.Gt),
      LieTie Q (ψ ≫ Z.m0.toSABMap.φ) xx (z.u σ j) → LieTie Q (Q.gen ≫ π) xx ((frameOf Z z).v σ j) := by
  atlas_forward_decl GlobalTheory.DetHT.lieTie_frameOf_of_ptAt
end

section
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.ShFam.Descent

namespace GlobalTheory.DetHT

theorem ptAt_tangent_isEig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F))
    (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]] (z : FrPt Xo c ℂ_[p]) (yb : Sp 𝓞_ℂ_[p] ⟶ Z.X)
    (yy : Sp ℂ_[p] ⟶ Xo.XF c),
    letI := H.starRing; ∀ (Q : PtP E p) (π : Q.G.left ⟶ Z.t.G.left) (ψ : Q.A.A.left ⟶ Z.oF.t.G.left),
      PtAt Z yb yy Q π ψ → ∀ (σ : E →+* ℂ) (j : Fin (Dw.mult σ)) (xx : LieG Q.Gt),
      LieTie Q (ψ ≫ Z.m0.toSABMap.φ) xx (z.u σ j) → AvDefs.IsEig Q.Gt Q.oGt (embInt c Q.integers σ) xx := by
  intro E _ _ _ H Dw l Xo c Z p _ _ z yb yy
  letI := H.starRing
  intro Q π ψ hP σ j xx h
  obtain ⟨-, -, h3, h4, h5⟩ := hP
  have hpb : IsGrpPullback Q.A.A Xo.univ.t.G _ (ψ ≫ Z.m0.toSABMap.φ) := h4.comp Z.m0.toSABMap.cart
  have hact : ∀ a, (Q.oA.act a).left ≫ (ψ ≫ Z.m0.toSABMap.φ) =
      (ψ ≫ Z.m0.toSABMap.φ) ≫ (Xo.univ.t.act.act a).left := fun a => by
    have e : (Q.oA.act a).left ≫ ψ = ψ ≫ (Z.oF.t.act.act a).left := Z.m.cart.1.hom_ext
      (by rw [Category.assoc, Category.assoc, Z.m.act, h5, ← Category.assoc ψ, h5, ← Category.assoc, Q.gen_act,
        Category.assoc, h3, Category.assoc])
      (by rw [Category.assoc, Category.assoc, Over.w, h4.1.w, Over.w_assoc])
    rw [← Category.assoc, e, Category.assoc, Category.assoc, Z.m0.toSABMap.act]
  exact fun a =>
    (h.act a (hact a)).unique hpb.1 (by rw [z.eig σ j a, ← algebraMap_embInt Q.integers]; exact h.scale _)

end GlobalTheory.DetHT
end

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.ShFam.Descent

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_point_period_relation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F))
    (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]] (z : FrPt Xo c ℂ_[p]) (yb : Sp 𝓞_ℂ_[p] ⟶ Z.X)
    (yy : Sp ℂ_[p] ⟶ Xo.XF c),
    letI := H.starRing; ∀ (Q : PtP E p) (π : Q.G.left ⟶ Z.t.G.left) (ψ : Q.A.A.left ⟶ Z.oF.t.G.left),
      PtAt Z yb yy Q π ψ → ∀ (σ : E →+* ℂ) (j : Fin (Dw.mult σ)) (xx : LieG Q.Gt),
      LieTie Q (ψ ≫ Z.m0.toSABMap.φ) xx (z.u σ j) → AvDefs.IsEig Q.Gt Q.oGt (embInt c Q.integers σ) xx := by
  atlas_forward_decl GlobalTheory.DetHT.ptAt_tangent_isEig
end

section
set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.ShFam.Pad AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigLetters

section Tan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
  {S : Type} [CommRing S] {x0 : Sp S ⟶ X0}

def tvG {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x0 v) : TanM x0 t.G :=
  mkT (ovT hv) (smT_zero_ovT hv)

theorem tv_tvG {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x0 v) : tv (tvG hv) = ovT hv := rfl

theorem tvG_tv (n : TanM x0 t.G) : tvG (isTanAtG_of (t := t) (x0 := x0) (tv n) (tv_mem n)) = n :=
  tanM_ext (Over.OverMorphism.ext rfl)

theorem tv_sumG {κ : Type} (s : Finset κ) (f : κ → TanM x0 t.G) : tv (∑ i ∈ s, f i) = ∏ i ∈ s, tv (f i) := by
  simp only [tv, toMul_sum, Subgroup.val_finset_prod]

theorem combG_iff {m : ℕ} (u : Fin m → (Sp (DualNumber S) ⟶ t.G.left)) (hu : ∀ i, IsTanAtG t x0 (u i))
    (cf : Fin m → S) {w : Sp (DualNumber S) ⟶ t.G.left} (hw : IsTanAtG t x0 w) :
    IsCombAtG t x0 u cf w ↔ tvG hw = ∑ i, cf i • tvG (hu i) := by
  have e : IsCombAtG t x0 u cf w ↔ (combT x0 (fun i => ovT (hu i)) cf).left = w :=
    isCombAtG_iff t x0 (fun i => ovT (hu i)) cf w
  rw [e]
  constructor
  · intro h
    apply tanM_ext
    rw [tv_sumG, tv_tvG]
    apply Over.OverMorphism.ext
    exact h.symm
  · intro h
    have h3 : ovT hw = combT x0 (fun i => ovT (hu i)) cf := by
      rw [← tv_tvG hw, h, tv_sumG]
      rfl
    exact (congrArg (fun V => Over.Hom.left V) h3).symm

end Tan

section Letters

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H)


theorem mem_letters (x : Letter Dw) : x ∈ letters Dw := by
  obtain ⟨τ, i⟩ := x
  unfold letters
  refine List.mem_flatMap.2 ⟨Fintype.equivFin (E →+* ℂ) τ, List.mem_finRange _, ?_⟩
  generalize hσ : (Fintype.equivFin (E →+* ℂ)).symm (Fintype.equivFin (E →+* ℂ) τ) = σ
  obtain rfl : σ = τ := by rw [← hσ, Equiv.symm_apply_apply]
  exact List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩

end Letters

section Flag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {Ω : Type} [Field Ω] [Algebra c.F Ω] (y : FlagPt Z Ω) (hA : algebraMap c.F Ω = y.fK)

include hA in
theorem eig_iffG (τ : E →+* ℂ) {w : Sp (DualNumber Ω) ⟶ Z.t.G.left} (hw : IsTanAtG Z.t (y.y ≫ GlobalTheory.Toroidal.genι Z) w) :
    (∀ a : 𝓞 E, w ≫ (Z.t.act.act a).left = spMap (epsMul (y.fK (embF c τ (a : E)))) ≫ w) ↔
      IsEigV (actR (x0 := y.y ≫ GlobalTheory.Toroidal.genι Z) (S := Ω) Z.t.act) (embK c τ) (tvG hw) := by
  rw [← hA]
  refine forall_congr' fun a => ⟨fun h => tanM_ext ?_, fun h => ?_⟩
  · apply Over.OverMorphism.ext
    exact h
  · have := congrArg (fun V => (tv V).left) h
    exact this

include hA in
theorem eig_coordsG (τ : E →+* ℂ) (n : TanM (y.y ≫ GlobalTheory.Toroidal.genι Z) Z.t.G)
    (hn : IsEigV (actR (x0 := y.y ≫ GlobalTheory.Toroidal.genι Z) (S := Ω) Z.t.act) (embK c τ) n) :
    ∃! a : Fin (Dw.mult τ) → Ω, n = ∑ i, a i • tvG (y.tan τ i) := by
  have hw := isTanAtG_of (t := Z.t) (x0 := y.y ≫ GlobalTheory.Toroidal.genι Z) (tv n) (tv_mem n)
  have heig := (eig_iffG y hA τ hw).2 ((tvG_tv n).symm ▸ hn)
  obtain ⟨a, ha, hu⟩ := y.basis τ _ hw heig
  refine ⟨a, ?_, fun b hb => hu b ?_⟩
  · rw [← tvG_tv n]
    exact (combG_iff (y.u τ) (y.tan τ) a hw).1 ha
  · refine (combG_iff (y.u τ) (y.tan τ) b hw).2 ?_
    rw [tvG_tv n]
    exact hb

theorem eig_combG {x : Sp Ω ⟶ Z.X} (τ : E →+* ℂ) {m : ℕ} (v : Fin m → TanM x Z.t.G)
    (hv : ∀ i, IsEigV (actR (x0 := x) (S := Ω) Z.t.act) (embK c τ) (v i)) (a : Fin m → Ω) :
    IsEigV (actR (x0 := x) (S := Ω) Z.t.act) (embK c τ) (∑ i, a i • v i) := by
  intro b
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hv i b, smul_comm]

def fullG : Letter Dw → TanM (y.y ≫ GlobalTheory.Toroidal.genι Z) Z.t.G := fun k => tvG (y.tan k.1 k.2)

include hA in
theorem fullG_eig (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) :
    IsEigV (actR (x0 := y.y ≫ GlobalTheory.Toroidal.genι Z) (S := Ω) Z.t.act) (embK c τ) (fullG y ⟨τ, i⟩) :=
  (eig_iffG y hA τ (y.tan τ i)).1 (y.eig τ i)

include hA in
theorem fullG_basis (m : TanM (y.y ≫ GlobalTheory.Toroidal.genι Z) Z.t.G) :
    ∃! a : Letter Dw → Ω, m = ∑ k, a k • fullG y k := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  let ρ := actR (x0 := y.y ≫ GlobalTheory.Toroidal.genι Z) (S := Ω) Z.t.act
  have hsum : ∑ τ, proj ρ (embK c) α τ m = m := by
    have := congrArg (fun e : Module.End Ω (TanM (y.y ≫ GlobalTheory.Toroidal.genι Z) Z.t.G) => e m)
      (sum_proj ρ (embK c) α hinj)
    simpa [LinearMap.sum_apply] using this
  have hE : ∀ τ, IsEigV ρ (embK c τ) (proj ρ (embK c) α τ m) := fun τ =>
    eig_of_alpha ρ (embK c) α hN τ (proj_eig_alpha ρ (embK c) α hinj f hf hfs τ m)
  choose a ha hu using fun τ => eig_coordsG y hA τ (proj ρ (embK c) α τ m) (hE τ)
  refine ⟨fun k => a k.1 k.2, ?_, fun b hb => ?_⟩
  · show m = ∑ k : Letter Dw, a k.1 k.2 • fullG y k
    rw [Fintype.sum_sigma]
    conv_lhs => rw [← hsum]
    exact Finset.sum_congr rfl fun τ _ => ha τ
  · have hb' : m = ∑ k : Letter Dw, b k • fullG y k := hb
    rw [Fintype.sum_sigma] at hb'
    funext k
    obtain ⟨τ, i⟩ := k
    have hn := proj_sum_eig ρ (embK c) α hinj (fun τ => ∑ i, b ⟨τ, i⟩ • fullG y ⟨τ, i⟩)
      (fun τ => eig_combG τ _ (fun i => fullG_eig y hA τ i) _) τ
    rw [← hb'] at hn
    have := hu τ (fun i => b ⟨τ, i⟩) hn
    exact congrFun this i

end Flag


end GlobalTheory.EigLetters
end
end

section
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.ShFam.Descent

namespace GlobalTheory.FramedPointCoeffs

open ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj MonObj

theorem coeffs_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F)
    (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (S : Type) [Field S] [Algebra c.F S] (P : FrPt Xo c S) (σ : E →+* ℂ)
    (a a' : Fin (Dw.mult σ) → S) (w : Sp (DualNumber S) ⟶ Z.t.G.left),
    IsCombAtG Z.t (GlobalTheory.AllWt.ptF P ≫ Z.j) ((frameOf Z P).v σ) a w →
    IsCombAtG Z.t (GlobalTheory.AllWt.ptF P ≫ Z.j) ((frameOf Z P).v σ) a' w → a = a' := by
  intro E _ _ _ H Dw l Xo c O _ β Z S _ _ P σ a a' w ha ha'
  have hw : Formalism.L2.Pj.IsTanAtG Z.t (GlobalTheory.AllWt.ptF P ≫ Z.j) w :=
    GlobalTheory.ShFam.Pad.Guard.comb_tan ((frameOf Z P).tan σ) ha
  have hv : ∀ i, IsEigV (actR (x0 := GlobalTheory.AllWt.ptF P ≫ Z.j) (S := S) Z.t.act) (embK c σ)
      (GlobalTheory.EigLetters.tvG ((frameOf Z P).tan σ i)) := by
    intro i b
    apply tanM_ext
    apply Over.OverMorphism.ext
    exact (frameOf Z P).eig σ i b
  have h1 := (GlobalTheory.EigLetters.combG_iff ((frameOf Z P).v σ) ((frameOf Z P).tan σ) a hw).1 ha
  have h2 : IsEigV (actR (x0 := GlobalTheory.AllWt.ptF P ≫ Z.j) (S := S) Z.t.act) (embK c σ)
      (GlobalTheory.EigLetters.tvG hw) := by
    rw [h1]
    exact GlobalTheory.EigLetters.eig_combG σ _ hv a
  have he : ∀ b : 𝓞 E, w ≫ (Z.t.act.act b).left =
      spMap (epsMul (algebraMap c.F S (embK c σ b))) ≫ w := by
    intro b
    exact congrArg (fun V => (tv V).left) (h2 b)
  exact ((frameOf Z P).basis σ w hw he).unique ha ha'

end GlobalTheory.FramedPointCoeffs
end

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.ShFam.Descent

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.combinatorial_tangent_point_condition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F)
    (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (S : Type) [Field S] [Algebra c.F S] (P : FrPt Xo c S) (σ : E →+* ℂ)
    (a a' : Fin (Dw.mult σ) → S) (w : Sp (DualNumber S) ⟶ Z.t.G.left),
    IsCombAtG Z.t (GlobalTheory.AllWt.ptF P ≫ Z.j) ((frameOf Z P).v σ) a w →
    IsCombAtG Z.t (GlobalTheory.AllWt.ptF P ≫ Z.j) ((frameOf Z P).v σ) a' w → a = a' := by
  atlas_forward_decl GlobalTheory.FramedPointCoeffs.coeffs_unique
end

section
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.ShFam.Descent

namespace GlobalTheory.DetHT.BridgeBasis

theorem mem_latHT_iff_changeBasis : BridgeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F))
    (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]] (yy : Sp ℂ_[p] ⟶ Xo.XF c) (yb : Sp 𝓞_ℂ_[p] ⟶ Z.X),
    letI := H.starRing; ∀ (Q : PtP E p) (π : Q.G.left ⟶ Z.t.G.left) (ψ : Q.A.A.left ⟶ Z.oF.t.G.left),
      PtAt Z yb yy Q π ψ → ∀ (n : ℕ) (xx : Fin n → LieG Q.Gt) (u u' : Fin n → (Sp (DualNumber ℂ_[p]) ⟶ Z.t.G.left))
      (g : Matrix (Fin n) (Fin n) ℂ_[p]), (∀ j, IsTanAtG Z.t (yy ≫ Z.j) (u j)) →
      (∀ j, LieTie Q (Q.gen ≫ π) (xx j) (u j)) → (∀ i, IsCombAtG Z.t (yy ≫ Z.j) u (g i) (u' i)) →
      ∀ (a : Fin n → ℂ_[p]) (w : Sp (DualNumber ℂ_[p]) ⟶ Z.t.G.left), IsCombAtG Z.t (yy ≫ Z.j) u' a w →
        (w ∈ GlobalTheory.ShFam.Pad.latHT Z.t p (yy ≫ Z.j) ↔ ∑ i, a i • ∑ j, g i j • Q.bLie (xx j) ∈ Q.latT) := by
  intro hB E _ _ _ H Dw l Xo c Z p _ _ yy yb
  letI := H.starRing
  intro Q π ψ hP n xx u u' g hu hx hg a w hw
  haveI : IsProper Z.s := projProper _ _ _ Z.proj
  haveI : IsNoetherianRing (𝓞 c.F) := Algebra.FiniteType.isNoetherianRing ℤ (𝓞 c.F)
  haveI : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.s
  haveI : Z.X.IsSeparated := ⟨by rw [← terminal.comp_from Z.s]; infer_instance⟩
  have hc : IsCombAtG Z.t (yy ≫ Z.j) u (g.transpose.mulVec a) w :=
    GlobalTheory.TangentLinear.isCombAtG_mulVec u hu u' g.transpose a w (fun i => by simpa [Matrix.transpose_apply] using hg i) hw
  rw [← hP.1] at hc
  have key := hB E H Z.X Z.t p Q yb π hP.2.1 n xx u hx (g.transpose.mulVec a) w hc
  rw [hP.1] at key
  rw [key]
  have hs : ∑ j, (g.transpose.mulVec a) j • Q.bLie (xx j) = ∑ i, a i • ∑ j, g i j • Q.bLie (xx j) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [_root_.mul_comm]
  rw [hs]

end GlobalTheory.DetHT.BridgeBasis
end

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.ShFam.Descent

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_point_tangent_map_formula : BridgeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F))
    (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]] (yy : Sp ℂ_[p] ⟶ Xo.XF c) (yb : Sp 𝓞_ℂ_[p] ⟶ Z.X),
    letI := H.starRing; ∀ (Q : PtP E p) (π : Q.G.left ⟶ Z.t.G.left) (ψ : Q.A.A.left ⟶ Z.oF.t.G.left),
      PtAt Z yb yy Q π ψ → ∀ (n : ℕ) (xx : Fin n → LieG Q.Gt) (u u' : Fin n → (Sp (DualNumber ℂ_[p]) ⟶ Z.t.G.left))
      (g : Matrix (Fin n) (Fin n) ℂ_[p]), (∀ j, IsTanAtG Z.t (yy ≫ Z.j) (u j)) →
      (∀ j, LieTie Q (Q.gen ≫ π) (xx j) (u j)) → (∀ i, IsCombAtG Z.t (yy ≫ Z.j) u (g i) (u' i)) →
      ∀ (a : Fin n → ℂ_[p]) (w : Sp (DualNumber ℂ_[p]) ⟶ Z.t.G.left), IsCombAtG Z.t (yy ≫ Z.j) u' a w →
        (w ∈ GlobalTheory.ShFam.Pad.latHT Z.t p (yy ≫ Z.j) ↔ ∑ i, a i • ∑ j, g i j • Q.bLie (xx j) ∈ Q.latT) := by
  atlas_forward_decl GlobalTheory.DetHT.BridgeBasis.mem_latHT_iff_changeBasis
end

section
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.ShFam.Descent

theorem GlobalTheory.CompHt.eigtau_sum_mem_latT_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p : ℕ) [Fact p.Prime]
    (δ : ℂ_[p]), δ ≠ 0 → ∀ (l : Level H) (c : Coeff l) [Algebra c.F ℂ_[p]],
    letI := H.starRing; ∀ (Q : PtP E p) (τ : Psi H),
      (∀ w ∈ Q.eigV (embInt c Q.integers τ.1), (w ∈ htLat c Q τ.1 ↔ δ • w ∈ Q.latT)) →
      ∀ (n : ℕ) (xx : Fin n → LieG Q.Gt) (g : Matrix (Fin n) (Fin n) ℂ_[p]),
      (∀ j, AvDefs.IsEig Q.Gt Q.oGt (embInt c Q.integers τ.1) (xx j)) →
      IsLatBasis ℂ_[p] (htLat c Q τ.1) (fun i => ∑ j, g i j • Q.bLie (xx j)) → ∀ a : Fin n → ℂ_[p],
        (∑ i, a i • ∑ j, g i j • Q.bLie (xx j) ∈ Q.latT ↔ ∀ i, ‖δ⁻¹ * a i‖ ≤ 1) := by
  intro E _ _ _ H p _ δ hδ l c _ Q τ hyp n xx g hx hb a
  letI := H.starRing
  set s := ∑ i, a i • ∑ j, g i j • Q.bLie (xx j) with hs
  have hsV : s ∈ Q.eigV (embInt c Q.integers τ.1) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (bLie_mem_eigV (hx j)))
  have h1 := hyp (δ⁻¹ • s) (Submodule.smul_mem _ _ hsV)
  rw [smul_smul, mul_inv_cancel₀ hδ, one_smul] at h1
  rw [← h1, hs, Finset.smul_sum]
  simp_rw [smul_smul]
  rw [hb.sum_mem_iff]
  simp_rw [mem_range_iff_norm_le]
end

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.ShFam.Descent

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_eigenvector_height_matrix : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p : ℕ) [Fact p.Prime]
    (δ : ℂ_[p]), δ ≠ 0 → ∀ (l : Level H) (c : Coeff l) [Algebra c.F ℂ_[p]],
    letI := H.starRing; ∀ (Q : PtP E p) (τ : Psi H),
      (∀ w ∈ Q.eigV (embInt c Q.integers τ.1), (w ∈ htLat c Q τ.1 ↔ δ • w ∈ Q.latT)) →
      ∀ (n : ℕ) (xx : Fin n → LieG Q.Gt) (g : Matrix (Fin n) (Fin n) ℂ_[p]),
      (∀ j, AvDefs.IsEig Q.Gt Q.oGt (embInt c Q.integers τ.1) (xx j)) →
      IsLatBasis ℂ_[p] (htLat c Q τ.1) (fun i => ∑ j, g i j • Q.bLie (xx j)) → ∀ a : Fin n → ℂ_[p],
        (∑ i, a i • ∑ j, g i j • Q.bLie (xx j) ∈ Q.latT ↔ ∀ i, ‖δ⁻¹ * a i‖ ≤ 1) := by
  atlas_forward_decl GlobalTheory.CompHt.eigtau_sum_mem_latT_iff
end

section
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.ShFam.Descent

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem eigconj_sum_mem_latT_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p : ℕ) [Fact p.Prime]
    (l : Level H) (c : Coeff l) [Algebra c.F ℂ_[p]],
    letI := H.starRing; ∀ (Q : PtP E p) (τ : Psi H) (n : ℕ) (xx : Fin n → LieG Q.Gt) (g : Matrix (Fin n) (Fin n) ℂ_[p]),
      (∀ j, AvDefs.IsEig Q.Gt Q.oGt (embInt c Q.integers (conjEmb τ.1)) (xx j)) →
      IsLatBasis ℂ_[p] (htLat c Q (conjEmb τ.1)) (fun i => ∑ j, g i j • Q.bLie (xx j)) → ∀ a : Fin n → ℂ_[p],
        (∑ i, a i • ∑ j, g i j • Q.bLie (xx j) ∈ Q.latT ↔ ∀ i, ‖(1 : ℂ_[p]) * a i‖ ≤ 1) := by
  intro E _ _ _ H p _ l c _
  letI := H.starRing
  intro Q τ n xx g hx hb a
  have hs : (∑ i, a i • ∑ j, g i j • Q.bLie (xx j)) ∈ Q.eigV (embInt c Q.integers (conjEmb τ.1)) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (bLie_mem_eigV (hx j)))
  have h := hb.sum_mem_iff a
  rw [htLat_conj] at h
  simp only [_root_.one_mul, ← mem_range_iff_norm_le p]
  rw [← h]
  exact ⟨fun h1 => ⟨h1, hs⟩, fun h1 => h1.1⟩

end GlobalTheory
end
end

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.ShFam.Descent

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_lattice_basis_of_eigenvectors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p : ℕ) [Fact p.Prime]
    (l : Level H) (c : Coeff l) [Algebra c.F ℂ_[p]],
    letI := H.starRing; ∀ (Q : PtP E p) (τ : Psi H) (n : ℕ) (xx : Fin n → LieG Q.Gt) (g : Matrix (Fin n) (Fin n) ℂ_[p]),
      (∀ j, AvDefs.IsEig Q.Gt Q.oGt (embInt c Q.integers (conjEmb τ.1)) (xx j)) →
      IsLatBasis ℂ_[p] (htLat c Q (conjEmb τ.1)) (fun i => ∑ j, g i j • Q.bLie (xx j)) → ∀ a : Fin n → ℂ_[p],
        (∑ i, a i • ∑ j, g i j • Q.bLie (xx j) ∈ Q.latT ↔ ∀ i, ‖(1 : ℂ_[p]) * a i‖ ≤ 1) := by
  atlas_forward_decl GlobalTheory.eigconj_sum_mem_latT_iff
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.ShFam.Descent

namespace GlobalTheory.DetHT

theorem pointSt_of : BridgeSt → EigSt → CovolSt → PointSt := by
  intro hB hE hC E _ _ _ _ H Dw τ p _
  obtain ⟨δ, hδ, hEδ⟩ := hE E H p
  refine ⟨-(Dw.mult τ.1 : ℝ) * Real.log ‖δ‖, ?_⟩
  intro l Xo c Z _ f hf P y z yb hyP Q π ψ hPt hHT hfy
  letI := H.starRing
  obtain ⟨g, a, x, hchg, -, -, htie, hlat⟩ := hHT
  have hPy : P.x = y.x := by rw [← Descent.ptF_fst P, ← hyP, Descent.ptF_fst]
  have hzy : z.x = y.x := hchg.1.symm
  have hzP : ptF z = ptF P := by
    refine pullback.hom_ext ?_ ?_
    · rw [Descent.ptF_fst, Descent.ptF_fst, hzy, hPy]
    · rw [Descent.ptF_snd, Descent.ptF_snd]
  have LT := fun σ j => GlobalTheory.T.p_adic_frobenius_point_comparison E H Dw l Xo c Z p P z yb hzP Q π ψ hPt σ j (x σ j) (htie σ j)
  have LE := fun σ j => GlobalTheory.T.p_adic_point_period_relation E H Dw l Xo c Z p z yb (ptF P) Q π ψ hPt σ j (x σ j) (htie σ j)
  have uY := fun σ => GlobalTheory.T.combinatorial_tangent_point_condition E H Dw l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Z ℂ_[p] y σ
  set vY := (frameOf Z y).v with hvY
  set vZ := (frameOf Z z).v with hvZ
  have tY : ∀ σ k, IsTanAtG Z.t (ptF y ≫ Z.j) (vY σ k) := (frameOf Z y).tan
  have rY : ∀ σ k, TanRel Z (ptF y) (y.u σ k) (vY σ k) := (tie_frameOf Z y).2.2
  have tZ : ∀ σ k, IsTanAtG Z.t (ptF z ≫ Z.j) (vZ σ k) := (frameOf Z z).tan
  have rZ : ∀ σ k, TanRel Z (ptF z) (z.u σ k) (vZ σ k) := (tie_frameOf Z z).2.2
  clear_value vY vZ
  rw [hyP] at tY rY uY
  rw [hzP] at tZ rZ
  have Cz : ∀ σ i, IsCombAtG Z.t (ptF P ≫ Z.j) (vZ σ) (g σ i) (vY σ i) := fun σ i =>
    (TanRel.comb_iff ((Descent.ptF_fst P).trans (hPy.trans hzy.symm)) rfl (rZ σ) (rY σ i) _).1 (hchg.2.1 σ i)
  obtain ⟨G, b, hGu, hG⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c ℂ_[p] y P).1 hPy
  have Cy : ∀ σ i, IsCombAtG Z.t (ptF P ≫ Z.j) (vY σ) (G σ i) ((frameOf Z P).v σ i) := fun σ i =>
    (TanRel.comb_iff ((Descent.ptF_fst P).trans hPy) rfl (rY σ) ((tie_frameOf Z P).2.2 σ i) _).1 (hG.2.1 σ i)
  have hev := GlobalTheory.FlatGL.evR_flat_chg τ hf P y hPy (G τ.1) (G (conjEmb τ.1)) (hG.2.1 τ.1) (hG.2.1 _)
  have hL := fun σ => GlobalTheory.T.p_adic_point_tangent_map_formula hB E H Dw l Xo c Z p (ptF P) yb Q π ψ hPt (Dw.mult σ) (x σ) (vZ σ) (vY σ) (g σ)
    (tZ σ) (LT σ) (Cz σ)
  have h1 := hC E H Z.X Z.t ℂ_[p] (ptF P ≫ Z.j) (GlobalTheory.ShFam.Pad.latHT Z.t p (ptF P ≫ Z.j)) (Dw.mult τ.1)
    ((frameOf Z P).v τ.1) (vY τ.1) (G τ.1) δ⁻¹ (inv_ne_zero hδ) (tY τ.1) (uY τ.1)
    (fun a w hw => (hL τ.1 a w hw).trans (GlobalTheory.T.lattice_eigenvector_height_matrix E H p δ hδ l c Q τ (hEδ l c Q τ) _ (x τ.1) (g τ.1)
      (LE τ.1) (hlat τ.1) a)) (Cy τ.1) (hGu τ.1).ne_zero
  have h2 := hC E H Z.X Z.t ℂ_[p] (ptF P ≫ Z.j) (GlobalTheory.ShFam.Pad.latHT Z.t p (ptF P ≫ Z.j)) (Dw.mult (conjEmb τ.1))
    ((frameOf Z P).v (conjEmb τ.1)) (vY (conjEmb τ.1)) (G (conjEmb τ.1)) 1 one_ne_zero (tY _) (uY _)
    (fun a w hw => (hL _ a w hw).trans (GlobalTheory.T.height_lattice_basis_of_eigenvectors E H p l c Q τ _ (x (conjEmb τ.1)) (g (conjEmb τ.1))
      (LE _) (hlat _) a)) (Cy _) (hGu _).ne_zero
  have d1 := (hGu τ.1).ne_zero
  have d2 := (hGu (conjEmb τ.1)).ne_zero
  have hP0 : evR Xo c f P ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hev
    exact mul_ne_zero d2 hfy hev.symm
  refine ⟨hP0, ?_⟩
  have e := congrArg (fun t => Real.log ‖t‖) hev
  simp only [norm_mul] at e
  rw [Real.log_mul (norm_ne_zero_iff.2 hP0) (norm_ne_zero_iff.2 d1),
    Real.log_mul (norm_ne_zero_iff.2 d2) (norm_ne_zero_iff.2 hfy)] at e
  unfold lnDet
  rw [h1, h2, norm_inv, Real.log_inv, norm_one, Real.log_one]
  linarith

end GlobalTheory.DetHT
end
end

open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.point_count_of_eigen_covolume_hypotheses : BridgeSt → EigSt → CovolSt → PointSt := by
  atlas_forward_decl GlobalTheory.DetHT.pointSt_of
end
