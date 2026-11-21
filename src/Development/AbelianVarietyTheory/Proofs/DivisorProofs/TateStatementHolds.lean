import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateLatticeSpans
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeC

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FlatModel

theorem tateIso_transport_ptOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ) [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)], l'.A = p ^ n →
    ∀ (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left)
      (ψ : P.A.A.left ⟶ Y.oF.t.G.left), PtOn Y yb yy P π ψ →
    ∃ (ev : ℕ → Dw.La → (Over.mk (𝟙 (Sp ℂ_[p])) ⟶ P.A.A)) (ζ : ℕ → ℂ_[p]ˣ),
      (∀ k, 0 < k → IsPrimitiveRoot (ζ k) k) ∧ (∀ k m, 0 < k → 0 < m → ζ (k * m) ^ m = ζ k) ∧
      (∀ k a b, ev k (a + b) = ev k a * ev k b) ∧ (∀ k (o : 𝓞 E) a, ev k (o • a) = ev k a ≫ P.oA.act o) ∧
      (∀ k, 0 < k → ∀ x, x ^ k = 1 ↔ ∃ a, ev k a = x) ∧
      (∀ k m, 0 < k → 0 < m → ∀ a, ev (k * m) a ^ m = ev k a) ∧
      (∀ k, 0 < k → ∀ a b, weil P.A k (ev k a) (ev k b) = ζ k ^ Dw.EF a b) ∧
      ∀ a, (ev (p ^ n) a).left ≫ ψ = yy ≫ (Y.oF.etaA a).left := by
  intro E _ _ _ H Dw l' Xo' c' W Y p _ n _ hl yb yy P π ψ hP
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hP
  obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : KA l' →+* ℂ_[p], yy ≫ (pullback.fst _ _ ≫ Xo'.s) = spMap β₀ :=
    ⟨(Spec.preimage (yy ≫ (pullback.fst _ _ ≫ Xo'.s))).hom, by simp [spMap]⟩
  obtain ⟨-, I, -, hI, -⟩ := Y.oF.geom ℂ_[p] yy β₀ hβ₀
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv h4 (Over.mk (𝟙 _)) yy (Category.id_comp _).symm
  have hact : ∀ o : 𝓞 E, (P.oA.act o).left ≫ ψ = ψ ≫ (Y.oF.t.act.act o).left := by
    intro o
    apply Y.m.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, h5, Y.m.act o, ← Category.assoc ψ, h5, ← Category.assoc, P.gen_act o,
        Category.assoc, Category.assoc, h3 o]
    · rw [Category.assoc, Category.assoc, Over.w (Y.oF.t.act.act o), h4.1.w, ← Category.assoc, Over.w]
  have hlin : ∀ (x : Over.mk (𝟙 (Sp ℂ_[p])) ⟶ P.A.A) (o : 𝓞 E), e (x ≫ P.oA.act o) = e x ≫ Y.oF.t.act.act o := by
    intro x o
    apply Over.OverMorphism.ext
    rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, Category.assoc, hact]
  have hsymm : ∀ y : Over.mk yy ⟶ Y.oF.t.G, (e.symm y).left ≫ ψ = y.left := fun y => by
    rw [← he, MulEquiv.apply_symm_apply]
  have hweil : ∀ (g : Sp ℂ_[p] ⟶ Xo'.XF c'), 𝟙 _ ≫ yy = g → ∀ (k : ℤ) (x y : Over.mk (𝟙 (Sp ℂ_[p])) ⟶ P.A.A)
      (x₀ y₀ : Over.mk g ⟶ Y.oF.t.G) (c : (Γ(Sp ℂ_[p], ⊤))ˣ), x₀.left = x.left ≫ ψ → y₀.left = y.left ≫ ψ →
      (Out.WeilIs P.A.A P.A.L k x y c ↔ Out.WeilIs Y.oF.t.G Y.oF.t.PP.L k x₀ y₀ c) := by
    rintro g rfl k x y x₀ y₀ c hx hy
    exact GlobalTheory.weilIs_grpPullback_of_comm _ _ Y.oF.t.G P.A.A yy ψ Y.oF.t.PP.L P.A.L Y.oF.t.PP.isLB P.A.isLB h4 h6
      (Over.mk (𝟙 _)) k x y x₀ y₀ c hx hy
  have onto : ∀ k, 0 < k → ∀ x : Over.mk (𝟙 (Sp ℂ_[p])) ⟶ P.A.A, x ^ k = 1 ↔ ∃ a, e.symm (I.ev k a) = x := by
    intro k hk x
    rw [← e.injective.eq_iff, map_pow, map_one, I.onto k hk]
    simp only [MulEquiv.symm_apply_eq]
  refine ⟨fun k a => e.symm (I.ev k a), I.ζ, I.ζ_prim, I.ζ_pow, ?_, ?_, onto, ?_, ?_, ?_⟩
  · intro k a b
    simp only [I.add, map_mul]
  · intro k o a
    apply e.injective
    rw [hlin, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact I.lin k o a
  · intro k m hk hm a
    simp only [← map_pow, I.tower k m hk hm a]
  · intro k hk a b
    have hza : (e.symm (I.ev k a)) ^ k = 1 := (onto k hk _).2 ⟨a, rfl⟩
    have hzb : (e.symm (I.ev k b)) ^ k = 1 := (onto k hk _).2 ⟨b, rfl⟩
    refine ((GlobalTheory.HTLat.weilIs_iff (A := P.A) (Nat.one_le_iff_ne_zero.2 hk.ne') hza hzb _).1 ?_).symm
    rw [hweil yy (Category.id_comp yy) _ _ _ (I.ev k a) (I.ev k b) _ (hsymm _).symm (hsymm _).symm]
    exact I.isom k hk a b
  · intro a
    rw [hsymm, ← hl, ← hI a, Over.comp_left]
    congr 1

end GlobalTheory.FlatModel
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_point_level_power : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ) [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)], l'.A = p ^ n →
    ∀ (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left)
      (ψ : P.A.A.left ⟶ Y.oF.t.G.left), PtOn Y yb yy P π ψ →
    ∃ (ev : ℕ → Dw.La → (Over.mk (𝟙 (Sp ℂ_[p])) ⟶ P.A.A)) (ζ : ℕ → ℂ_[p]ˣ),
      (∀ k, 0 < k → IsPrimitiveRoot (ζ k) k) ∧ (∀ k m, 0 < k → 0 < m → ζ (k * m) ^ m = ζ k) ∧
      (∀ k a b, ev k (a + b) = ev k a * ev k b) ∧ (∀ k (o : 𝓞 E) a, ev k (o • a) = ev k a ≫ P.oA.act o) ∧
      (∀ k, 0 < k → ∀ x, x ^ k = 1 ↔ ∃ a, ev k a = x) ∧
      (∀ k m, 0 < k → 0 < m → ∀ a, ev (k * m) a ^ m = ev k a) ∧
      (∀ k, 0 < k → ∀ a b, weil P.A k (ev k a) (ev k b) = ζ k ^ Dw.EF a b) ∧
      ∀ a, (ev (p ^ n) a).left ≫ ψ = yy ≫ (Y.oF.etaA a).left := by
  atlas_forward_decl GlobalTheory.FlatModel.tateIso_transport_ptOn
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem tateLift_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p)
    (ev : ℕ → Dw.La → (Over.mk (𝟙 (Sp ℂ_[p])) ⟶ P.A.A)), (∀ k a b, ev k (a + b) = ev k a * ev k b) →
    (∀ k (o : 𝓞 E) a, ev k (o • a) = ev k a ≫ P.oA.act o) →
    (∀ k m, 0 < k → 0 < m → ∀ a, ev (k * m) a ^ m = ev k a) → (∀ a, ev 1 a = 1) →
    ∃ tι : Dw.La →+ P.T, (∀ a k, (tι a).lev k = ev (p ^ k) a) ∧ ∀ (o : 𝓞 E) a, tι (o • a) = P.actT o (tι a) := by
  intro E _ _ _ H Dw p _ _ P ev hadd hact htow hone
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have h1 : ∀ a k, ev (p ^ k) a ^ p ^ k = 1 := fun a k => by
    have := htow 1 (p ^ k) one_pos (pow_pos hp k) a
    rwa [Nat.one_mul, hone] at this
  have h2 : ∀ a k, ev (p ^ (k + 1)) a ^ p = ev (p ^ k) a := fun a k => by
    rw [pow_succ]
    exact htow (p ^ k) p (pow_pos hp k) hp a
  let f : Dw.La → P.T := fun a => Tate.mk (fun k => ev (p ^ k) a) fun k => ⟨h1 a k, h2 a k⟩
  refine ⟨{ toFun := f, map_zero' := ?_, map_add' := ?_ }, fun a k => rfl, ?_⟩
  · refine Tate.ext fun n => ?_
    have := hadd (p ^ n) 0 0
    rw [add_zero] at this
    change ev (p ^ n) 0 = 1
    exact left_eq_mul.1 this
  · intro a b
    exact Tate.ext fun n => hadd (p ^ n) a b
  · intro o a
    exact Tate.ext fun n => hact (p ^ n) o a

end GlobalTheory.FlatModel
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tate_module_of_evaluations : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p)
    (ev : ℕ → Dw.La → (Over.mk (𝟙 (Sp ℂ_[p])) ⟶ P.A.A)), (∀ k a b, ev k (a + b) = ev k a * ev k b) →
    (∀ k (o : 𝓞 E) a, ev k (o • a) = ev k a ≫ P.oA.act o) →
    (∀ k m, 0 < k → 0 < m → ∀ a, ev (k * m) a ^ m = ev k a) → (∀ a, ev 1 a = 1) →
    ∃ tι : Dw.La →+ P.T, (∀ a k, (tι a).lev k = ev (p ^ k) a) ∧ ∀ (o : 𝓞 E) a, tι (o • a) = P.actT o (tι a) := by
  atlas_forward_decl GlobalTheory.FlatModel.tateLift_exists
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_lattice_spans : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (tι : Dw.La →+ P.T),
    (∀ x : (Over.mk (𝟙 (Sp ℂ_[p])) ⟶ P.A.A), x ^ p = 1 → ∃ a, (tι a).lev 1 = x) →
    Submodule.span ℤ_[p] (Set.range tι) = ⊤ := by
  first | exact @GlobalTheory.TateSpan.span_range_eq_top | exact GlobalTheory.TateSpan.span_range_eq_top | (intros; apply GlobalTheory.TateSpan.span_range_eq_top <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.TateUnitPair

theorem lev_zsmul {p : ℕ} {M : Type} [CommGroup M] (t : Tate p M) (n : ℤ) (k : ℕ) :
    (n • t).lev k = t.lev k ^ n := by
  rfl

theorem lev_nsmul {p : ℕ} {M : Type} [CommGroup M] (t : Tate p M) (n : ℕ) (k : ℕ) :
    (n • t).lev k = t.lev k ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, Tate.lev_add, ih, pow_succ]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (tι : Dw.La →+ P.T) (ζ : ℕ → ℂ_[p]ˣ),
    (∀ k, 0 < k → IsPrimitiveRoot (ζ k) k) → (∀ k m, 0 < k → 0 < m → ζ (k * m) ^ m = ζ k) →
    (∀ (k : ℕ) a b, weil P.A (p ^ k) ((tι a).lev k) ((tι b).lev k) = ζ (p ^ k) ^ Dw.EF a b) →
    ∃ u : ℤ_[p], IsUnit u ∧ ∀ a b, pairT P.A P.eps (tι a) (tι b) = u * (Dw.EF a b : ℤ_[p]) := by
  intro E _ _ _ H Dw p _ _ P tι ζ hprim hcomp hweil
  have hp : p.Prime := Fact.out
  have hpk : ∀ k : ℕ, 0 < p ^ k := fun k => pow_pos hp.pos k
  let z : Tate p ℂ_[p]ˣ := Tate.mk (fun k => ζ (p ^ k)) fun k =>
    ⟨(hprim (p ^ k) (hpk k)).pow_eq_one, by
      rw [pow_succ]; exact hcomp (p ^ k) p (hpk k) hp.pos⟩
  refine ⟨P.eps.equiv.symm z, ?_, fun a b => ?_⟩
  · by_contra hu
    have hlt : ‖P.eps.equiv.symm z‖ < 1 := PadicInt.mem_nonunits.1 hu
    obtain ⟨c, hc⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 hlt
    have h1 : z = P.eps.equiv (P.eps.equiv.symm z) := (P.eps.equiv.apply_symm_apply z).symm
    rw [hc, ← smul_eq_mul, map_smul] at h1
    have h2 : z.lev 1 = 1 := by
      rw [h1]
      change ((p : ℤ_[p]) • P.eps.equiv c).lev 1 = 1
      rw [Nat.cast_smul_eq_nsmul, lev_nsmul]
      simpa using (P.eps.equiv c).lev_pow 1
    have h3 : IsPrimitiveRoot (ζ p) p := by simpa using hprim p hp.pos
    exact h3.ne_one hp.one_lt (by simpa [z] using h2)
  · have hw : weilT P.A p (tι a) (tι b) = (Dw.EF a b : ℤ) • z := Tate.ext fun k => by
      rw [lev_weilT, lev_zsmul, hweil]
      rfl
    change P.eps.equiv.symm (weilT P.A p (tι a) (tι b)) = _
    rw [hw, map_zsmul, zsmul_eq_mul, mul_comm]

end GlobalTheory.TateUnitPair
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_pairing_unit_scalar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (tι : Dw.La →+ P.T) (ζ : ℕ → ℂ_[p]ˣ),
    (∀ k, 0 < k → IsPrimitiveRoot (ζ k) k) → (∀ k m, 0 < k → 0 < m → ζ (k * m) ^ m = ζ k) →
    (∀ (k : ℕ) a b, weil P.A (p ^ k) ((tι a).lev k) ((tι b).lev k) = ζ (p ^ k) ^ Dw.EF a b) →
    ∃ u : ℤ_[p], IsUnit u ∧ ∀ a b, pairT P.A P.eps (tι a) (tι b) = u * (Dw.EF a b : ℤ_[p]) := by
  atlas_forward_decl GlobalTheory.TateUnitPair.main
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory

open Polynomial

theorem intCasimir_exists : ∀ (E : Type) [Field E] [NumberField E], ∃ (d : ℕ) (c θ : Fin d → 𝓞 E),
    (∀ o : 𝓞 E, ∑ j, c j ⊗ₜ[ℤ] (o * θ j) = ∑ j, (o * c j) ⊗ₜ[ℤ] θ j) ∧ ∑ j, c j * θ j ≠ 0 := by
  intro E _ _
  classical
  obtain ⟨α, -, -, hN⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_sepElt (E := E) (F := ℂ) (RingHom.id ℂ)
    (fun τ => τ.comp (algebraMap (𝓞 E) E)) (fun _ _ => rfl)
  let g : ℤ[X] := minpoly ℤ α
  have hgα : aeval α g = 0 := minpoly.aeval ℤ α
  have hroot : (g.map (algebraMap ℤ (𝓞 E))).IsRoot α := by
    rw [IsRoot, Polynomial.eval_map, ← aeval_def, hgα]
  let q := (g.map (algebraMap ℤ (𝓞 E))) /ₘ (X - C α)
  have hq : (X - C α) * q = g.map (algebraMap ℤ (𝓞 E)) := mul_divByMonic_eq_iff_isRoot.2 hroot
  let iL : 𝓞 E →+* 𝓞 E ⊗[ℤ] 𝓞 E := Algebra.TensorProduct.includeLeftRingHom
  let iR : 𝓞 E →+* 𝓞 E ⊗[ℤ] 𝓞 E := (Algebra.TensorProduct.includeRight : 𝓞 E →ₐ[ℤ] _).toRingHom
  have hiL : ∀ x, iL x = x ⊗ₜ[ℤ] 1 := fun _ => rfl
  have hiR : ∀ x, iR x = 1 ⊗ₜ[ℤ] x := fun _ => rfl
  let T : 𝓞 E ⊗[ℤ] 𝓞 E := q.eval₂ iL (iR α)
  have hT : T = ∑ j : Fin (q.natDegree + 1), q.coeff j ⊗ₜ[ℤ] (α ^ (j : ℕ)) := by
    show q.eval₂ iL (iR α) = _
    rw [eval₂_eq_sum_range, ← Fin.sum_univ_eq_sum_range (fun n => iL (q.coeff n) * (iR α) ^ n)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hiL, hiR, Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul,
      _root_.mul_one, _root_.one_mul]
  have hαT : iR α * T = iL α * T := by
    have h1 : ((X - C α) * q).eval₂ iL (iR α) = 0 := by
      rw [hq, eval₂_map]
      have : iL.comp (algebraMap ℤ (𝓞 E)) = iR.comp (algebraMap ℤ (𝓞 E)) := RingHom.ext_int _ _
      rw [this, ← hom_eval₂, ← aeval_def, hgα, map_zero]
    rw [eval₂_mul, eval₂_sub, eval₂_X, eval₂_C] at h1
    exact sub_eq_zero.1 (by rw [← sub_mul]; exact h1)
  let I : Ideal (𝓞 E ⊗[ℤ] 𝓞 E) := (Submodule.span (𝓞 E ⊗[ℤ] 𝓞 E) {T}).annihilator
  have hmemI : ∀ r, r ∈ I ↔ r * T = 0 := fun r => by
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
  let π := Ideal.Quotient.mk I
  have hπα : (π.comp iR).toIntAlgHom α = (π.comp iL).toIntAlgHom α := by
    show π (iR α) = π (iL α)
    rw [Ideal.Quotient.eq, hmemI, sub_mul, hαT, sub_self]
  have key : ∀ p : ℤ[X], π (iR (aeval α p)) = π (iL (aeval α p)) := fun p => by
    have h1 := aeval_algHom_apply (π.comp iR).toIntAlgHom α p
    have h2 := aeval_algHom_apply (π.comp iL).toIntAlgHom α p
    rw [hπα] at h1
    exact h1.symm.trans h2
  haveI : Module.Free ℤ (𝓞 E) := inferInstance
  haveI : Module.Free ℤ (𝓞 E ⊗[ℤ] 𝓞 E) := Module.Free.of_basis
    ((Module.Free.chooseBasis ℤ (𝓞 E)).tensorProduct (Module.Free.chooseBasis ℤ (𝓞 E)))
  haveI : Module.IsTorsionFree ℤ (𝓞 E ⊗[ℤ] 𝓞 E) := inferInstance
  have hall : ∀ o : 𝓞 E, iR o * T = iL o * T := by
    intro o
    obtain ⟨N, p, hN0, hNp⟩ := hN o
    have h := key p
    rw [← hNp, Ideal.Quotient.eq, hmemI, map_mul, map_mul, map_intCast, map_intCast, ← mul_sub,
      _root_.mul_assoc, ← zsmul_eq_mul] at h
    rw [← sub_eq_zero, ← sub_mul]
    exact (smul_eq_zero.1 h).resolve_left hN0
  refine ⟨q.natDegree + 1, fun j => q.coeff j, fun j => α ^ (j : ℕ), fun o => ?_, ?_⟩
  · have h := hall o
    rw [hT, Finset.mul_sum, Finset.mul_sum] at h
    convert h using 2 with j
    · rw [hiR, Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul]
    · rw [hiL, Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul]
  · have hsum : ∑ j : Fin (q.natDegree + 1), q.coeff j * α ^ (j : ℕ) = q.eval α := by
      rw [eval_eq_sum_range, ← Fin.sum_univ_eq_sum_range (fun n => q.coeff n * α ^ n)]
    rw [hsum]
    have hd := congrArg derivative hq
    rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, _root_.one_mul,
      derivative_map] at hd
    have he := congrArg (eval α) hd
    rw [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero, Polynomial.eval_map,
      ← aeval_def] at he
    rw [he]
    intro h0
    have hE : aeval (α : E) (derivative g) = 0 := by
      rw [Polynomial.aeval_algebraMap_apply, h0, map_zero]
    have hint : IsIntegral ℤ (α : E) := RingOfIntegers.isIntegral_coe α
    have hmin : minpoly ℚ (α : E) = g.map (algebraMap ℤ ℚ) := by
      rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint, NumberField.RingOfIntegers.minpoly_coe]
    have hsep := (Algebra.IsSeparable.isSeparable ℚ (α : E)).aeval_derivative_ne_zero
      (minpoly.aeval ℚ (α : E))
    rw [hmin, derivative_map, aeval_map_algebraMap] at hsep
    exact hsep hE

end GlobalTheory
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_trace_element : ∀ (E : Type) [Field E] [NumberField E], ∃ (d : ℕ) (c θ : Fin d → 𝓞 E),
    (∀ o : 𝓞 E, ∑ j, c j ⊗ₜ[ℤ] (o * θ j) = ∑ j, (o * c j) ⊗ₜ[ℤ] θ j) ∧ ∑ j, c j * θ j ≠ 0 := by
  atlas_forward_decl GlobalTheory.intCasimir_exists
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory

theorem ringHom_integers_injective_of_charZero :
    ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K]
    (χ : 𝓞 E →+* K), Function.Injective χ := by
  intro E _ _ K _ _ χ
  rw [injective_iff_map_eq_zero]
  intro o ho
  by_contra hne
  have hdvd := Algebra.dvd_algebraMap_intNorm_self ℤ (𝓞 E) o
  have hn : Algebra.intNorm ℤ (𝓞 E) o ≠ 0 := Algebra.intNorm_ne_zero.mpr hne
  have h2 := map_dvd χ hdvd
  rw [ho, zero_dvd_iff] at h2
  have h3 : χ (algebraMap ℤ (𝓞 E) (Algebra.intNorm ℤ (𝓞 E) o)) = ((Algebra.intNorm ℤ (𝓞 E) o : ℤ) : K) := by
    simp
  rw [h3] at h2
  exact hn (by exact_mod_cast h2)

end GlobalTheory
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
namespace GlobalTheory.FlatModel.EigSpan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {p : ℕ} [Fact p.Prime] [StarRing (𝓞 E)] {P : PtP E p} {V : Type} [CommRing V]

noncomputable def phi (β : V →+* 𝓞_ℂ_[p]) (tι : Dw.La →+ P.T) : V ⊗[ℤ] Dw.La →ₗ[ℤ] P.V :=
  TensorProduct.lift (LinearMap.mk₂ ℤ (fun (v : V) (b : Dw.La) => ((β v : 𝓞_ℂ_[p]) : ℂ_[p]) ⊗ₜ[ℤ_[p]] tι b)
    (fun v v' b => by simp [TensorProduct.add_tmul])
    (fun n v b => by simp [TensorProduct.smul_tmul'])
    (fun v b b' => by simp [TensorProduct.tmul_add])
    (fun n v b => by simp [TensorProduct.tmul_smul]))

theorem phi_tmul (β : V →+* 𝓞_ℂ_[p]) (tι : Dw.La →+ P.T) (v : V) (b : Dw.La) :
    phi β tι (v ⊗ₜ b) = ((β v : 𝓞_ℂ_[p]) : ℂ_[p]) ⊗ₜ[ℤ_[p]] tι b := by
  unfold phi
  erw [TensorProduct.lift.tmul]; rfl

theorem phi_smul (β : V →+* 𝓞_ℂ_[p]) (tι : Dw.La →+ P.T) (v : V) (y : V ⊗[ℤ] Dw.La) :
    phi β tι (v • y) = ((β v : 𝓞_ℂ_[p]) : ℂ_[p]) • phi β tι y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b =>
    rw [TensorProduct.smul_tmul', phi_tmul, phi_tmul, TensorProduct.smul_tmul']
    simp
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem le_span_of_casimir (β : V →+* 𝓞_ℂ_[p]) (σ : 𝓞 E →+* V) {J : Type} [DecidableEq J] {N : ℕ}
    (a : Fin N → Dw.La) (T S : J → Fin N → V) (tι : Dw.La →+ P.T) (hL : LatData Dw σ a T S)
    (hι : ∀ (o : 𝓞 E) b, tι (o • b) = P.actT o (tι b))
    (hsp : Submodule.span ℤ_[p] (Set.range tι) = ⊤)
    {d : ℕ} (c θ : Fin d → 𝓞 E) (hc : ∀ o : 𝓞 E, ∑ j, c j ⊗ₜ[ℤ] (o * θ j) = ∑ j, (o * c j) ⊗ₜ[ℤ] θ j)
    (hne : ((β (σ (∑ j, c j * θ j)) : 𝓞_ℂ_[p]) : ℂ_[p]) ≠ 0) :
    P.eigV (β.comp σ) ≤
      Submodule.span ℂ_[p] (Set.range fun i => ∑ m, (β (T i m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] tι (a m)) := by
  set Sp := Submodule.span ℂ_[p] (Set.range fun i => ∑ m, (β (T i m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] tι (a m)) with hSp
  let χ : 𝓞 E → ℂ_[p] := fun o => ((β (σ o) : 𝓞_ℂ_[p]) : ℂ_[p])
  let Q : P.V →ₗ[ℂ_[p]] P.V := ∑ j, χ (c j) • P.actV (θ j)
  have hΦ : ∀ y ∈ Submodule.span V (Set.range fun i => ∑ m, T i m ⊗ₜ[ℤ] a m), phi β tι y ∈ Sp := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [map_sum]
      simp only [phi_tmul]
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Sp.add_mem hx hy
    | smul v x _ hx => rw [phi_smul]; exact Sp.smul_mem _ hx
  have hb : ∀ b : Dw.La, Q (1 ⊗ₜ tι b) ∈ Sp := by
    intro b
    let g : 𝓞 E →ₗ[ℤ] Dw.La := (LinearMap.toSpanSingleton (𝓞 E) Dw.La b).restrictScalars ℤ
    have hx : (∑ j, σ (c j) ⊗ₜ[ℤ] (θ j • b)) ∈
        Submodule.span V (Set.range fun i => ∑ m, T i m ⊗ₜ[ℤ] a m) := by
      apply hL.2.2
      intro o
      have h1 := congrArg (TensorProduct.map σ.toIntAlgHom.toLinearMap g) (hc o)
      simp only [map_sum, TensorProduct.map_tmul] at h1
      simp only [map_sum, LinearMap.baseChange_tmul, Finset.smul_sum, TensorProduct.smul_tmul']
      simp only [g, LinearMap.restrictScalars_apply, LinearMap.toSpanSingleton_apply, mul_smul, map_mul,
        AlgHom.toLinearMap_apply] at h1
      exact h1
    have h2 := hΦ _ hx
    convert h2 using 1
    simp [Q, LinearMap.sum_apply, Point.actV, GlobalTheory.EigenSplit.baseChangeAction_apply,
      LinearMap.baseChange_tmul, hι, TensorProduct.smul_tmul', phi_tmul, χ]
  have hall : ∀ w, Q w ∈ Sp := by
    have hsm : ∀ (r : ℤ_[p]) (t : P.T), (1 : ℂ_[p]) ⊗ₜ[ℤ_[p]] (r • t) =
        (algebraMap ℤ_[p] ℂ_[p] r) • ((1 : ℂ_[p]) ⊗ₜ[ℤ_[p]] t) := by
      intro r t
      rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one, smul_eq_mul, _root_.mul_one]
    let M : Submodule ℤ_[p] P.T :=
      { carrier := {t | Q ((1 : ℂ_[p]) ⊗ₜ[ℤ_[p]] t) ∈ Sp}
        add_mem' := fun {x y} hx hy => by
          simp only [Set.mem_setOf_eq, TensorProduct.tmul_add, map_add] at hx hy ⊢
          exact Sp.add_mem hx hy
        zero_mem' := by simp
        smul_mem' := fun r t ht => by
          simp only [Set.mem_setOf_eq, hsm, map_smul] at ht ⊢
          exact Sp.smul_mem _ ht }
    have hM : M = ⊤ := by
      rw [eq_top_iff, ← hsp, Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      exact hb b
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul z t =>
      have ht : t ∈ M := hM ▸ Submodule.mem_top
      have he : z ⊗ₜ[ℤ_[p]] t = z • ((1 : ℂ_[p]) ⊗ₜ[ℤ_[p]] t) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [he, map_smul]
      exact Sp.smul_mem _ ht
    | add x y hx hy => rw [map_add]; exact Sp.add_mem hx hy
  intro w hw
  have hw' := GlobalTheory.EigenSplit.mem_eigenSub.1 hw
  have hQ : Q w = χ (∑ j, c j * θ j) • w := by
    simp only [Q, LinearMap.sum_apply, LinearMap.smul_apply, hw', smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    simp [χ, map_sum, map_mul]
  have : w = (χ (∑ j, c j * θ j))⁻¹ • Q w := by
    rw [hQ, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [this]
  exact Sp.smul_mem _ (hall w)

theorem eigV_le_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (V : Type) [CommRing V]
    (β : V →+* 𝓞_ℂ_[p]) (σ : 𝓞 E →+* V) (J : Type) [DecidableEq J] (N : ℕ) (a : Fin N → Dw.La)
    (T S : J → Fin N → V) (tι : Dw.La →+ P.T), LatData Dw σ a T S → (∀ (o : 𝓞 E) b, tι (o • b) = P.actT o (tι b)) →
    Submodule.span ℤ_[p] (Set.range tι) = ⊤ →
    P.eigV (β.comp σ) ≤ Submodule.span ℂ_[p] (Set.range fun i => ∑ m, (β (T i m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] tι (a m)) := by
  intro E _ _ _ H Dw p _ _ P V _ β σ J _ N a T S tι hL hι hsp
  obtain ⟨d, c, θ, hc, hne⟩ := GlobalTheory.T.exists_nonzero_trace_element E
  refine le_span_of_casimir β σ a T S tι hL hι hsp c θ hc ?_
  have hinj := GlobalTheory.ringHom_integers_injective_of_charZero E ℂ_[p] ((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (β.comp σ))
  intro h
  apply hne
  apply hinj
  simpa using h

end GlobalTheory.FlatModel.EigSpan
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_data_tate_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (V : Type) [CommRing V]
    (β : V →+* 𝓞_ℂ_[p]) (σ : 𝓞 E →+* V) (J : Type) [DecidableEq J] (N : ℕ) (a : Fin N → Dw.La)
    (T S : J → Fin N → V) (tι : Dw.La →+ P.T), LatData Dw σ a T S → (∀ (o : 𝓞 E) b, tι (o • b) = P.actT o (tι b)) →
    Submodule.span ℤ_[p] (Set.range tι) = ⊤ →
    P.eigV (β.comp σ) ≤ Submodule.span ℂ_[p] (Set.range fun i => ∑ m, (β (T i m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] tι (a m)) := by
  atlas_forward_decl GlobalTheory.FlatModel.EigSpan.eigV_le_span
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

theorem tateSt : TateSt := by
  intro E _ _ _ H Dw l' Xo' c' W Y p _ n _ hstar hA yb yy P π ψ hP β σ J _ N a T S hL
  obtain ⟨ev, ζ, hζp, hζpow, hadd, hlin, honto, htow, hweil, hlev⟩ :=
    GlobalTheory.T.p_adic_point_level_power E H Dw l' Xo' c' W Y p n hA yb yy P π ψ hP
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hev1 : ∀ b, ev 1 b = 1 := fun b => by
    have := (honto 1 one_pos (ev 1 b)).2 ⟨b, rfl⟩
    simpa using this
  obtain ⟨f, hflev, hflin⟩ := GlobalTheory.T.exists_tate_module_of_evaluations E H Dw p P ev hadd hlin htow hev1
  have hspan := GlobalTheory.T.tate_lattice_spans E H Dw p P f (fun x hx => by
    obtain ⟨b, hb⟩ := (honto p hp x).1 hx
    exact ⟨b, by rw [hflev, pow_one, hb]⟩)
  obtain ⟨u, hu, hpair⟩ := GlobalTheory.T.weil_pairing_unit_scalar E H Dw p P f ζ hζp hζpow (fun k b b' => by
    rw [hflev, hflev]; exact hweil _ (pow_pos hp k) b b')
  have hmem : ∀ (c : 𝓞_ℂ_[p]) (t : P.T), ((c : ℂ_[p]) ⊗ₜ[ℤ_[p]] t : P.V) ∈ P.latT := fun c t =>
    ⟨c ⊗ₜ t, by rw [Point.inclT_tmul]; rfl⟩
  have hsum : ∀ (X : Fin N → 𝓞_ℂ_[p]), (∑ m, ((X m : ℂ_[p]) ⊗ₜ[ℤ_[p]] f (a m)) : P.V) ∈ P.latT := fun X =>
    Submodule.sum_mem _ fun m _ => hmem _ _
  let Φ : (c'.V W) ⊗[ℤ] Dw.La →ₗ[ℤ] P.V := TensorProduct.lift (LinearMap.mk₂ ℤ
    (fun (v : c'.V W) (b : Dw.La) => ((β v : ℂ_[p]) ⊗ₜ[ℤ_[p]] f b : P.V))
    (fun v v' b => by simp [TensorProduct.add_tmul])
    (fun z v b => by simp [TensorProduct.smul_tmul'])
    (fun v b b' => by simp [TensorProduct.tmul_add])
    (fun z v b => by simp [TensorProduct.tmul_smul]))
  have hΦ : ∀ v b, Φ (v ⊗ₜ b) = (β v : ℂ_[p]) ⊗ₜ[ℤ_[p]] f b := fun v b => rfl
  refine ⟨fun m => f (a m), algebraMap ℤ_[p] ℂ_[p] u, fun m => by rw [hflev]; exact hlev _, ?_⟩
  refine ⟨fun i => ⟨hsum _, ?_⟩, fun i => hsum _, ?_, fun i j => ?_, ?_⟩
  · refine EigenSplit.mem_eigenSub.2 fun o => ?_
    have e1 := congrArg Φ (hL.1 i o)
    simp only [map_sum, hΦ] at e1
    have e2 : ∀ (c : ℂ_[p]) (t : P.T), P.actV o (c ⊗ₜ[ℤ_[p]] t) = c ⊗ₜ[ℤ_[p]] P.actT o t := fun c t => rfl
    simp only [map_sum, e2, ← hflin]
    rw [e1, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [TensorProduct.smul_tmul', map_mul]
    rfl
  · change ‖algebraMap ℚ_[p] ℂ_[p] (u : ℚ_[p])‖ = 1
    rw [norm_algebraMap']
    exact PadicInt.isUnit_iff.1 hu
  · have hc : ∀ x : 𝓞_ℂ_[p], algebraMap 𝓞_ℂ_[p] ℂ_[p] x = (x : ℂ_[p]) := fun x => rfl
    have e := congrArg (fun x : c'.V W => algebraMap 𝓞_ℂ_[p] ℂ_[p] (β x)) (hL.2.1 i j)
    simp only [map_sum, map_mul, map_intCast] at e
    simp only [hc] at e
    simp only [map_sum, LinearMap.sum_apply, Point.pairV_tmul, hpair]
    simp only [Algebra.smul_def, map_mul, map_intCast]
    have e4 : ∀ m m', algebraMap ℤ_[p] ℂ_[p] u * ((Dw.EF (a m) (a m') : ℤ) : ℂ_[p]) * (((β (S i m) : 𝓞_ℂ_[p]) : ℂ_[p]) * ((β (T j m') : 𝓞_ℂ_[p]) : ℂ_[p])) =
        algebraMap ℤ_[p] ℂ_[p] u * (((β (S i m) : 𝓞_ℂ_[p]) : ℂ_[p]) * ((β (T j m') : 𝓞_ℂ_[p]) : ℂ_[p]) * ((Dw.EF (a m) (a m') : ℤ) : ℂ_[p])) :=
      fun m m' => by ring
    rw [Finset.sum_comm]
    simp only [e4, ← Finset.mul_sum, e]
    by_cases h : i = j <;> simp [h]
  · exact GlobalTheory.T.lattice_data_tate_span E H Dw p P (c'.V W) β (embV c' W σ) J N a T S f hL hflin hspan

end GlobalTheory.FlatModel
end
end

open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_statement_holds : TateSt := by
  atlas_forward_decl GlobalTheory.FlatModel.tateSt
end
