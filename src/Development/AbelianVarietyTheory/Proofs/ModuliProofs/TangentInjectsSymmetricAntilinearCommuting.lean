import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGoodUniformisationKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DerivationEqZeroOfKodairaSpencerZero
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EntireAntilinearLatticePeriodsConst
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDifferentiableOnVerticalVectorField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HolomorphicPeriodicCocycleCoboundary
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueUniformisingVectorVerticalTangent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalDerivationAlongFibreOfSmooth
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LocDerRegularCoeff
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CauchyRiemannIffDifferentiableOnComplex
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PeriodicCechCocycleSmoothCoboundary

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
theorem _root_.GlobalTheory.T.exists_goodUniformisation_kodairaSpencer : ThetaUnifAV → ∀ P₀ : Out.PolAV (Sp ℂ), ∃ (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ ∧ ∀ w : Fin P₀.g → ℂ, KSRel u P₀.A.hom (𝟙 _) (fun _ => 0) 0 (fun z W f => fderiv ℂ (fn u (𝟙 _) W f) z w) := by
  first | exact @GlobalTheory.KSInh.exists_goodU_ksRel | exact GlobalTheory.KSInh.exists_goodU_ksRel | (intros; apply GlobalTheory.KSInh.exists_goodU_ksRel <;> assumption)
end

section
open Complex Matrix
open scoped ContDiff BigOperators Real
theorem _root_.GlobalTheory.T.entire_antilinear_lattice_periods_const : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (v : (Fin g → ℂ) → ℂ) (t : (Fin g → ℂ)), Differentiable ℂ v → (∀ (l : Λ) z, v (z + l) = v z + t ⬝ᵥ star (l : (Fin g → ℂ))) → t = 0 ∧ ∀ z, v z = v 0 := by
  first | exact @GlobalTheory.entire_antilinear_periods_const | exact GlobalTheory.entire_antilinear_periods_const | (intros; apply GlobalTheory.entire_antilinear_periods_const <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section

namespace GlobalTheory.KS.Endo

private theorem valAt'_comp_lemma {Y Z : Scheme.{0}} (x : Sp ℂ ⟶ Y) (φ : Y ⟶ Z) (U : Z.Opens) (a : Γ(Z, U)) :
    valAt' (x ≫ φ) U a = valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom a) := by
  unfold valAt'
  by_cases h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U
  · have h' : ⊤ ≤ x ⁻¹ᵁ φ ⁻¹ᵁ U := h
    rw [dif_pos h, dif_pos h']
    unfold valAt
    rw [Scheme.Hom.comp_appLE]
    rfl
  · have h' : ¬ ⊤ ≤ x ⁻¹ᵁ φ ⁻¹ᵁ U := h
    rw [dif_neg h, dif_neg h']

theorem ptDer_push {X Y : Scheme.{0}} (y : Sp ℂ ⟶ X) (f : X ⟶ Y) (δ : ∀ W : X.Opens, Γ(X, W) → ℂ) (h : PtDer y δ) :
    PtDer (y ≫ f) (fun W a => δ (f ⁻¹ᵁ W) ((f.app W).hom a)) where
  add W hW a b := by
    rw [map_add]
    exact h.add (f ⁻¹ᵁ W) hW _ _
  mul W hW a b := by
    rw [map_mul, valAt'_comp_lemma y f W a, valAt'_comp_lemma y f W b]
    exact h.mul (f ⁻¹ᵁ W) hW _ _
  res W W' hle hW a := by
    have hle' : f ⁻¹ᵁ W' ≤ f ⁻¹ᵁ W := fun x hx => hle hx
    have nat : (f.app W').hom (resG Y hle a) = resG X hle' ((f.app W).hom a) :=
      congrArg (fun φ : Γ(Y, W) ⟶ Γ(X, f ⁻¹ᵁ W') => φ.hom a) (f.naturality (homOfLE hle).op)
    rw [nat]
    exact h.res (f ⁻¹ᵁ W) (f ⁻¹ᵁ W') hle' hW _

theorem ptDer_sub {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (δ δ' : ∀ W : X.Opens, Γ(X, W) → ℂ) (h : PtDer y δ) (h' : PtDer y δ') :
    PtDer y (fun W a => δ W a - δ' W a) where
  add W hW a b := by
    rw [h.add W hW, h'.add W hW]
    ring
  mul W hW a b := by
    rw [h.mul W hW, h'.mul W hW]
    ring
  res W W' hle hW a := by
    rw [h.res W W' hle hW, h'.res W W' hle hW]

theorem app_top_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (f : X ⟶ X) (hf : f ≫ p = p) (r : R) :
    (f.app ⊤).hom (constFn p ⊤ r) = resG X (le_top : f ⁻¹ᵁ ⊤ ≤ ⊤) (constFn p ⊤ r) := by
  have aux : ∀ q : X ⟶ Sp R, q = p → ∀ e e', q.appLE ⊤ (f ⁻¹ᵁ ⊤) e = p.appLE ⊤ (f ⁻¹ᵁ ⊤) e' := by
    rintro q rfl e e'
    rfl
  have key : ∀ e, p.appLE ⊤ ⊤ e ≫ f.app ⊤ =
      p.appLE ⊤ ⊤ e ≫ X.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ ⊤ ≤ ⊤)).op := by
    intro e
    rw [Scheme.Hom.appLE_map, Scheme.Hom.app_eq_appLE f, Scheme.Hom.appLE_comp_appLE]
    exact aux _ hf _ _
  unfold constFn
  exact congrArg (fun φ : Γ(Sp R, ⊤) ⟶ Γ(X, f ⁻¹ᵁ ⊤) => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    (key _)

variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g) {X : Scheme.{0}}

theorem ex_add_lattice (z l : Fin g → ℂ) (hl : l ∈ u.Λ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).2 hl, _root_.mul_one]

theorem fn_differentiableAt (m : A₀.left ⟶ X) (W : X.Opens) (a : Γ(X, W)) (z : Fin g → ℂ) (hz : z ∈ dom u m W) :
    DifferentiableAt ℂ (fn u m W a) z := by
  have hU := u.hol (m ⁻¹ᵁ W) ((m.app W).hom a)
  have hz' : z ∈ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (m ⁻¹ᵁ W)} := hz
  have heq : fn u m W a = fun z => valAt' (u.ex z).left (m ⁻¹ᵁ W) ((m.app W).hom a) := by
    funext w
    exact valAt'_comp_lemma (u.ex w).left m W a
  rw [heq]
  exact hU.2.differentiableAt (hU.1.mem_nhds hz')

theorem fderiv_fn_add_lattice (m : A₀.left ⟶ X) (W : X.Opens) (a : Γ(X, W)) (z l : Fin g → ℂ) (hl : l ∈ u.Λ) :
    fderiv ℂ (fn u m W a) (z + l) = fderiv ℂ (fn u m W a) z := by
  have hper : (fun w => fn u m W a (w + l)) = fn u m W a := by
    funext w
    unfold fn
    rw [ex_add_lattice u w l hl]
  rw [← fderiv_comp_add_right, hper]

theorem comm_of_endo : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D Θ s, KSRel u p m D Θ s → ∀ (f : X ⟶ X) (f₀ : P₀.A ⟶ P₀.A) (F : (Fin P₀.g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ)), f ≫ p = p → f₀.left ≫ m = m ≫ f → (∀ z, u.ex (F z) = u.ex z ≫ f₀) → Comm Θ F := by
  intro P₀ u Hm χ hU R instR x₀ X p m hp hpb D Θ s hKS f f₀ F hfp hf₀ hF
  have hFdiff : Differentiable ℂ F := by
    have := (LinearMap.toContinuousLinearMap F).differentiable
    rwa [LinearMap.coe_toContinuousLinearMap'] at this

  have hpt : ∀ z, (u.ex z).left ≫ m ≫ f = (u.ex (F z)).left ≫ m := by
    intro z
    rw [hF z, Over.comp_left, Category.assoc, hf₀]

  have hex0 : u.ex 0 = 1 := (u.ker 0).2 (zero_mem _)
  have hone : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ P₀.A) ≫ f₀ = 1 := by
    have h0 := hF 0
    rw [map_zero, hex0] at h0
    exact h0.symm
  have hFl : ∀ l ∈ u.Λ, F l ∈ u.Λ := by
    intro l hl
    rw [← u.ker, hF, (u.ker l).2 hl, hone]
  have hexF : ∀ z, ∀ l ∈ u.Λ, u.ex (F (z + l)) = u.ex (F z) := by
    intro z l hl
    rw [map_add]
    exact ex_add_lattice u _ _ (hFl l hl)
  have hdom : ∀ W z, z ∈ dom u m (f ⁻¹ᵁ W) ↔ F z ∈ dom u m W := by
    intro W z
    show ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ (f ⁻¹ᵁ W) ↔ ⊤ ≤ ((u.ex (F z)).left ≫ m) ⁻¹ᵁ W
    rw [← hpt z]
    rfl
  have hfn : ∀ W a z, fn u m (f ⁻¹ᵁ W) ((f.app W).hom a) z = fn u m W a (F z) := by
    intro W a z
    show valAt' ((u.ex z).left ≫ m) (f ⁻¹ᵁ W) ((f.app W).hom a) = valAt' ((u.ex (F z)).left ≫ m) W a
    rw [← hpt z, ← Category.assoc, valAt'_comp_lemma ((u.ex z).left ≫ m) f W a]
  have hfd : ∀ W a z, F z ∈ dom u m W → fderiv ℂ (fn u m (f ⁻¹ᵁ W) ((f.app W).hom a)) z =
      (fderiv ℂ (fn u m W a) (F z)).comp (LinearMap.toContinuousLinearMap F) := by
    intro W a z hz
    have e : fn u m (f ⁻¹ᵁ W) ((f.app W).hom a) = fn u m W a ∘ (LinearMap.toContinuousLinearMap F) := by
      funext w
      exact hfn W a w
    rw [e]
    exact ((fn_differentiableAt u m W a (F z) hz).hasFDerivAt.comp z
      (LinearMap.toContinuousLinearMap F).hasFDerivAt).fderiv

  let d : (Fin P₀.g → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ :=
    fun z W a => s (F z) W a - s z (f ⁻¹ᵁ W) ((f.app W).hom a)
  have hd : ∀ z, PtDer ((u.ex (F z)).left ≫ m) (d z) ∧ ∀ r, d z ⊤ (constFn p ⊤ r) = 0 := by
    intro z
    refine ⟨?_, ?_⟩
    · have h1 := ptDer_push _ f (s z) (hKS.der z)
      rw [Category.assoc, hpt z] at h1
      exact ptDer_sub _ _ _ (hKS.der (F z)) h1
    · intro r
      have htop : ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ (f ⁻¹ᵁ ⊤) := fun x _ => trivial
      show s (F z) ⊤ (constFn p ⊤ r) - s z (f ⁻¹ᵁ ⊤) ((f.app ⊤).hom (constFn p ⊤ r)) = 0
      rw [app_top_constFn p f hfp r, (hKS.der z).res ⊤ (f ⁻¹ᵁ ⊤) le_top htop, hKS.base, hKS.base, sub_self]
  have hdhol : ∀ W a, DifferentiableOn ℂ (fun z => d z W a) {z ∈ Set.univ | F z ∈ dom u m W} := by
    intro W a
    have h1 : DifferentiableOn ℂ (fun z => s (F z) W a) {z ∈ Set.univ | F z ∈ dom u m W} :=
      (hKS.hol W a).comp hFdiff.differentiableOn (fun z hz => hz.2)
    have h2 : DifferentiableOn ℂ (fun z => s z (f ⁻¹ᵁ W) ((f.app W).hom a)) {z ∈ Set.univ | F z ∈ dom u m W} :=
      (hKS.hol (f ⁻¹ᵁ W) ((f.app W).hom a)).mono (fun z hz => (hdom W z).2 hz.2)
    exact h1.sub h2
  obtain ⟨w, hwd, hw⟩ := GlobalTheory.T.exists_differentiableOn_verticalVectorField P₀ u Hm χ hU R x₀ X p m hp hpb P₀.g Set.univ F d isOpen_univ hFdiff
    (fun z _ => hd z) hdhol

  have hper : ∀ z, ∀ l ∈ u.Λ,
      w (z + l) = w z + (Θ.mulVec (star (F l)) - F (Θ.mulVec (star l))) := by
    intro z l hl
    have hFl' := hFl l hl
    have hpt' : PtDer ((u.ex (F z)).left ≫ m) (d (z + l)) ∧ ∀ r, d (z + l) ⊤ (constFn p ⊤ r) = 0 := by
      rw [← hexF z l hl]
      exact hd (z + l)
    obtain ⟨w0, -, huniq⟩ := GlobalTheory.T.existsUnique_uniformising_vector_vertical_tangent P₀ u Hm χ hU R x₀ X p m hp hpb (F z) (d (z + l)) hpt'.1 hpt'.2
    refine (huniq _ ?_).trans (huniq _ ?_).symm
    · intro W a hz
      have hz' : F (z + l) ∈ dom u m W := by
        show ⊤ ≤ ((u.ex (F (z + l))).left ≫ m) ⁻¹ᵁ W
        rw [hexF z l hl]
        exact hz
      rw [hw (z + l) (Set.mem_univ _) W a hz', map_add, fderiv_fn_add_lattice u m W a (F z) (F l) hFl']
    · intro W a hz
      have hzf : z ∈ dom u m (f ⁻¹ᵁ W) := (hdom W z).2 hz
      have e1 := hKS.per ⟨F l, hFl'⟩ W a (F z) hz
      have e2 := hKS.per ⟨l, hl⟩ (f ⁻¹ᵁ W) ((f.app W).hom a) z hzf
      have hd0 := hw z (Set.mem_univ _) W a hz
      show s (F (z + l)) W a - s (z + l) (f ⁻¹ᵁ W) ((f.app W).hom a) = _
      rw [map_add, e1, e2, hfd W a z hz]
      show _ = fderiv ℂ (fn u m W a) (F z) (w z + (Θ.mulVec (star (F l)) - F (Θ.mulVec (star l))))
      rw [ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap', map_add, map_sub, ← hd0]
      ring

  have hc_add : ∀ v v' : Fin P₀.g → ℂ,
      Θ.mulVec (star (F (v + v'))) - F (Θ.mulVec (star (v + v'))) =
        (Θ.mulVec (star (F v)) - F (Θ.mulVec (star v))) + (Θ.mulVec (star (F v')) - F (Θ.mulVec (star v'))) := by
    intro v v'
    rw [map_add, star_add, star_add, Matrix.mulVec_add, Matrix.mulVec_add, map_add]
    abel
  have hc_smul : ∀ (a : ℂ) (v : Fin P₀.g → ℂ),
      Θ.mulVec (star (F (a • v))) - F (Θ.mulVec (star (a • v))) =
        star a • (Θ.mulVec (star (F v)) - F (Θ.mulVec (star v))) := by
    intro a v
    rw [map_smul, star_smul, star_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, map_smul, smul_sub]
  let cA : (Fin P₀.g → ℂ) →+ (Fin P₀.g → ℂ) :=
    AddMonoidHom.mk' (fun v => Θ.mulVec (star (F v)) - F (Θ.mulVec (star v))) hc_add
  have hexp : ∀ v : Fin P₀.g → ℂ, Θ.mulVec (star (F v)) - F (Θ.mulVec (star v)) =
      ∑ j, star (v j) • cA (fun k => if j = k then 1 else 0) := by
    intro v
    have h1 : cA v = ∑ j, cA (v j • fun k => if j = k then 1 else 0) := by
      conv_lhs => rw [pi_eq_sum_univ v]
      exact map_sum cA _ _
    refine h1.trans (Finset.sum_congr rfl fun j _ => ?_)
    exact hc_smul (v j) _

  have hwdiff : Differentiable ℂ w := differentiableOn_univ.1 hwd
  have hzero : ∀ i j, cA (fun k => if j = k then 1 else 0) i = 0 := by
    intro i j
    have hperi : ∀ (l : u.Λ) (z : Fin P₀.g → ℂ), w (z + l) i =
        w z i + (fun j => cA (fun k => if j = k then 1 else 0) i) ⬝ᵥ star (l : Fin P₀.g → ℂ) := by
      intro l z
      rw [hper z l l.2, Pi.add_apply, hexp (l : Fin P₀.g → ℂ)]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dotProduct, Pi.star_apply]
      congr 1
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hI := GlobalTheory.T.entire_antilinear_lattice_periods_const P₀.g u.Λ u.discrete u.full (fun z => w z i) _ (differentiable_pi.1 hwdiff i) hperi
    exact congrFun hI.1 j
  intro z
  have hz := hexp z
  have hz0 : Θ.mulVec (star (F z)) - F (Θ.mulVec (star z)) = 0 := by
    rw [hz]
    funext i
    simp [hzero]
  exact (sub_eq_zero.1 hz0).symm

end GlobalTheory.KS.Endo
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencer_commutes_with_endomorphism : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D Θ s, KSRel u p m D Θ s → ∀ (f : X ⟶ X) (f₀ : P₀.A ⟶ P₀.A) (F : (Fin P₀.g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ)), f ≫ p = p → f₀.left ≫ m = m ≫ f → (∀ z, u.ex (F z) = u.ex z ≫ f₀) → Comm Θ F := by
  atlas_forward_decl GlobalTheory.KS.Endo.comm_of_endo
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localDerivationAlongFibre_of_smooth : ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (Y X : Scheme.{0}) (q : Y ⟶ Sp ℂ) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → ℂ) (W₀ : X.Opens), Smooth p → m ≫ p = q ≫ spMap x₀ → IsDer x₀ D → IsAffineOpen W₀ → ∃ d, LocDer q p m D W₀ d := by
  first | exact @GlobalTheory.KS.exists_locDer_of_smooth | exact GlobalTheory.KS.exists_locDer_of_smooth | (intros; apply GlobalTheory.KS.exists_locDer_of_smooth <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.Exist

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (f : Γ(X, U)) :
    resG X h' (resG X h f) = resG X (h'.trans h) f := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem res_const {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (h : V ≤ U) (a : R) : resG X h (constFn p U a) = constFn p V a :=
  congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map p (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)

theorem const_zero {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) :
    constFn p U 0 = 0 := by
  unfold constFn
  rw [map_zero, map_zero]

theorem ptDer_add {X : Scheme.{0}} {y : Sp ℂ ⟶ X} {δ δ' : ∀ W : X.Opens, Γ(X, W) → ℂ} (h : PtDer y δ) (h' : PtDer y δ') :
    PtDer y (fun W f => δ W f + δ' W f) where
  add W hW f f' := by rw [h.add W hW, h'.add W hW]; ring
  mul W hW f f' := by rw [h.mul W hW, h'.mul W hW]; ring
  res W W' e hW f := by rw [h.res W W' e hW, h'.res W W' e hW]

theorem locDer_sub {R : Type} [CommRing R] {Y X : Scheme.{0}} {q : Y ⟶ Sp ℂ} {p : X ⟶ Sp R} {m : Y ⟶ X} {D : R → ℂ}
    {W₀ W₁ : X.Opens} {d d' : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)} (h : LocDer q p m D W₀ d)
    (h' : LocDer q p m D W₁ d') : LocDer q p m (fun _ => 0) (W₀ ⊓ W₁) (fun W f => d W f - d' W f) where
  add W hW f f' := by rw [h.add W (hW.trans inf_le_left), h'.add W (hW.trans inf_le_right)]; ring
  mul W hW f f' := by rw [h.mul W (hW.trans inf_le_left), h'.mul W (hW.trans inf_le_right)]; ring
  res W W' e hW f := by rw [h.res W W' e (hW.trans inf_le_left), h'.res W W' e (hW.trans inf_le_right), map_sub]
  base W hW r := by rw [h.base W (hW.trans inf_le_left), h'.base W (hW.trans inf_le_right), sub_self, const_zero]

variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g) {X : Scheme.{0}}
  (m : A₀.left ⟶ X)

theorem ex_hom (z : Fin g → ℂ) : (u.ex z).left ≫ A₀.hom = 𝟙 _ := Over.w (u.ex z)

theorem ex_per (l : u.Λ) (z : Fin g → ℂ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]

theorem dom_open (W : X.Opens) : IsOpen (dom u m W) := (u.hol (m ⁻¹ᵁ W) 0).1

theorem dom_inf {W W' : X.Opens} {z : Fin g → ℂ} : z ∈ dom u m (W ⊓ W') ↔ z ∈ dom u m W ∧ z ∈ dom u m W' :=
  top_le_preimage_inf _ _ _

theorem dom_per (l : u.Λ) (W : X.Opens) (z : Fin g → ℂ) : z + l ∈ dom u m W ↔ z ∈ dom u m W := by
  simp only [dom, Set.mem_setOf_eq, ex_per]

theorem val_hol (W : X.Opens) (c : Γ(A₀.left, m ⁻¹ᵁ W)) :
    DifferentiableOn ℂ (fun z => valAt' (u.ex z).left (m ⁻¹ᵁ W) c) (dom u m W) := (u.hol (m ⁻¹ᵁ W) c).2

theorem fn_hol (W : X.Opens) (f : Γ(X, W)) : DifferentiableOn ℂ (fn u m W f) (dom u m W) := by
  have : fn u m W f = fun z => valAt' (u.ex z).left (m ⁻¹ᵁ W) ((m.app W).hom f) :=
    funext fun z => (valAt'_comp _ _ _ _).symm
  rw [this]
  exact val_hol u m W _

theorem fn_diffAt {W : X.Opens} (f : Γ(X, W)) {z : Fin g → ℂ} (hz : z ∈ dom u m W) :
    DifferentiableAt ℂ (fn u m W f) z :=
  (fn_hol u m W f).differentiableAt ((dom_open u m W).mem_nhds hz)

theorem fderiv_res {W W' : X.Opens} (h : W' ≤ W) (f : Γ(X, W)) {z : Fin g → ℂ}
    (hz : z ∈ dom u m W') : fderiv ℂ (fn u m W' (resG X h f)) z = fderiv ℂ (fn u m W f) z := by
  refine Filter.EventuallyEq.fderiv_eq ?_
  filter_upwards [(dom_open u m W').mem_nhds hz] with y hy
  exact valAt'_res _ h f hy

theorem fderiv_per (l : u.Λ) (W : X.Opens) (f : Γ(X, W)) (z : Fin g → ℂ) :
    fderiv ℂ (fn u m W f) (z + l) = fderiv ℂ (fn u m W f) z := by
  rw [← fderiv_comp_add_right]
  congr 1
  funext y
  simp only [fn, ex_per]

theorem ptDer_fderiv (z w : Fin g → ℂ) :
    PtDer ((u.ex z).left ≫ m) (fun W f => fderiv ℂ (fn u m W f) z w) where
  add W hW f f' := by
    have : fn u m W (f + f') = fn u m W f + fn u m W f' := funext fun y => valAt'_add _ _ _ _
    rw [this, fderiv_add (fn_diffAt u m f hW) (fn_diffAt u m f' hW)]; rfl
  mul W hW f f' := by
    have : fn u m W (f * f') = fn u m W f * fn u m W f' := funext fun y => valAt'_mul _ _ _ _
    rw [this, fderiv_mul (fn_diffAt u m f hW) (fn_diffAt u m f' hW)]; rfl
  res W W' h hW f := by rw [fderiv_res u m h f hW]

theorem fderiv_const_eq {R : Type} [CommRing R] {x₀ : R →+* ℂ} {p : X ⟶ Sp R} (hm : m ≫ p = A₀.hom ≫ spMap x₀)
    (r : R) (z w : Fin g → ℂ) : fderiv ℂ (fn u m ⊤ (constFn p ⊤ r)) z w = 0 := by
  have : fn u m ⊤ (constFn p ⊤ r) =
      fun _ => valAt' (spMap x₀) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    funext y
    refine (valAt'_appLE _ p ⊤ ⊤ le_top _ le_top).trans ?_
    rw [Category.assoc, hm, ← Category.assoc, ex_hom]
    exact congrArg (fun x => valAt' x ⊤ _) (Category.id_comp _)
  rw [this]
  simp

def ev (W₀ : X.Opens) (d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m ⁻¹ᵁ W)) (z : Fin g → ℂ) (W : X.Opens)
    (f : Γ(X, W)) : ℂ :=
  valAt' (u.ex z).left (m ⁻¹ᵁ (W ⊓ W₀)) (d (W ⊓ W₀) (resG X inf_le_left f))

variable {R : Type} [CommRing R] {p : X ⟶ Sp R} {D : R → ℂ} {W₀ : X.Opens}
  {d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m ⁻¹ᵁ W)}

theorem ev_eq (hd : LocDer A₀.hom p m D W₀ d) {z : Fin g → ℂ} {W W' : X.Opens} (h : W' ≤ W) (h₀ : W' ≤ W₀)
    (hz : z ∈ dom u m W') (f : Γ(X, W)) :
    ev u m W₀ d z W f = valAt' (u.ex z).left (m ⁻¹ᵁ W') (d W' (resG X h f)) := by
  rw [ev, ← res_res (inf_le_left : W ⊓ W₀ ≤ W) (le_inf h h₀), hd.res _ _ _ inf_le_right]
  exact (valAt'_res (u.ex z).left (V := m ⁻¹ᵁ W') _ _ hz).symm

theorem ptDer_ev (hd : LocDer A₀.hom p m D W₀ d) {z : Fin g → ℂ} (hz : z ∈ dom u m W₀) :
    PtDer ((u.ex z).left ≫ m) (ev u m W₀ d z) where
  add W hW f f' := by
    simp only [ev, map_add, hd.add _ inf_le_right, valAt'_add]
  mul W hW f f' := by
    have h : z ∈ dom u m (W ⊓ W₀) := (dom_inf u m).2 ⟨hW, hz⟩
    simp only [ev, map_mul, hd.mul _ inf_le_right, valAt'_add, valAt'_mul, valAt'_comp]
    rw [valAt'_res _ _ f h, valAt'_res _ _ f' h]
  res W W' e hW f := by
    have h : z ∈ dom u m (W' ⊓ W₀) := (dom_inf u m).2 ⟨hW, hz⟩
    rw [ev_eq u m hd (inf_le_left.trans e) inf_le_right h f, ev, res_res]

theorem ev_base (hd : LocDer A₀.hom p m D W₀ d) {z : Fin g → ℂ} (hz : z ∈ dom u m W₀) (r : R) :
    ev u m W₀ d z ⊤ (constFn p ⊤ r) = D r := by
  rw [ev_eq u m hd le_top le_rfl hz, res_const, hd.base _ le_rfl]
  exact valAt'_constFn _ _ (ex_hom u z) _ _ hz

theorem ev_hol (W : X.Opens) (f : Γ(X, W)) :
    DifferentiableOn ℂ (fun z => ev u m W₀ d z W f) (dom u m (W ⊓ W₀)) := val_hol u m _ _

theorem ev_per (l : u.Λ) (z : Fin g → ℂ) : ev u m W₀ d (z + l) = ev u m W₀ d z := by
  funext W f
  simp only [ev, ex_per]

theorem fderiv_field_hol (W : X.Opens) (f : Γ(X, W)) {S : Set (Fin g → ℂ)} (hS : S ⊆ dom u m W)
    (h : Fin g → (Fin g → ℂ) → ℂ) (hh : ∀ a, DifferentiableOn ℂ (h a) S) :
    DifferentiableOn ℂ (fun z => fderiv ℂ (fn u m W f) z (fun a => h a z)) S := by
  have e : (fun z => fderiv ℂ (fn u m W f) z (fun a => h a z)) =
      fun z => ∑ a, h a z * fderiv ℂ (fn u m W f) z (Pi.single a 1) := by
    funext z
    conv_lhs => rw [show (fun a => h a z) = ∑ a, h a z • (Pi.single a 1 : Fin g → ℂ) from
      (pi_eq_sum_univ' _)]
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [e]
  refine DifferentiableOn.fun_sum fun a _ => (hh a).mul ?_
  exact (((GlobalTheory.cauchyRiemann_iff_differentiableOn_complex g _ _ (dom_open u m W)).2 (fn_hol u m W f)).2 _).mono hS

theorem exists_affine_dom (z : Fin g → ℂ) : ∃ i : X.affineOpens, z ∈ dom u m i.1 := by
  obtain ⟨W, hW, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X)
    (x := ((u.ex z).left ≫ m) (default : PrimeSpectrum ℂ)) (U := ⊤) trivial
  exact ⟨⟨W, hW⟩, (top_le_preimage_iff_mem _ _).2 hx⟩

theorem exists_ksRel : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D, IsDer x₀ D → ∃ Θ s, KSRel u p m D Θ s := by
  intro P₀ u Hm χ hu R _ x₀ X p m hp hm D hD
  choose d hd using fun i : X.affineOpens => GlobalTheory.T.exists_localDerivationAlongFibre_of_smooth R x₀ _ X P₀.A.hom p m D i.1 hp hm.w hD i.2
  choose c hc using fun i j : X.affineOpens =>
    GlobalTheory.KS.locDer_regular_coeff P₀ u Hm χ hu R x₀ X p m hp hm _ _ (locDer_sub (hd i) (hd j))
  let C : X.affineOpens → X.affineOpens → (Fin P₀.g → ℂ) → Fin P₀.g → ℂ :=
    fun i j z a => valAt' (u.ex z).left (m ⁻¹ᵁ (i.1 ⊓ j.1)) (c i j a)
  have hC : ∀ i j z W f, z ∈ dom u m i.1 → z ∈ dom u m j.1 → z ∈ dom u m W →
      ev u m i.1 (d i) z W f - ev u m j.1 (d j) z W f = fderiv ℂ (fn u m W f) z (C i j z) := by
    intro i j z W f hi hj hW
    have h : z ∈ dom u m (W ⊓ (i.1 ⊓ j.1)) := (dom_inf u m).2 ⟨hW, (dom_inf u m).2 ⟨hi, hj⟩⟩
    rw [ev_eq u m (hd i) inf_le_left (inf_le_right.trans inf_le_left) h,
      ev_eq u m (hd j) inf_le_left (inf_le_right.trans inf_le_right) h, ← valAt'_sub,
      hc i j _ inf_le_right _ z h, fderiv_res u m _ _ h]
  have hco : ∀ i j k z, z ∈ dom u m i.1 → z ∈ dom u m j.1 → z ∈ dom u m k.1 → C i j z + C j k z = C i k z := by
    intro i j k z hi hj hk
    refine (GlobalTheory.T.existsUnique_uniformising_vector_vertical_tangent P₀ u Hm χ hu R x₀ X p m hp hm z _ (ptDer_fderiv u m z (C i k z))
      (fun r => fderiv_const_eq u m hm.w r z _)).unique (fun W f hW => ?_) (fun _ _ _ => rfl)
    rw [map_add, ← hC i j z W f hi hj hW, ← hC j k z W f hj hk hW, ← hC i k z W f hi hk hW]
    ring
  choose t h hh hch using fun a : Fin P₀.g =>
    GlobalTheory.holomorphic_periodic_cocycle_coboundary P₀.g u.Λ u.discrete u.full X.affineOpens (fun i => dom u m i.1)
      (fun i j z => C i j z a) (fun i => dom_open u m _) (fun i l z hz => (dom_per u m l _ z).2 hz)
      (exists_affine_dom u m)
      (fun i j => (val_hol u m _ (c i j a)).mono fun z hz => (dom_inf u m).2 hz)
      (fun i j l z _ => by simp only [C, ex_per])
      (fun i j k z hz => congrFun (hco i j k z hz.1.1 hz.1.2 hz.2) a)
  choose κ hκ using exists_affine_dom u m
  let s : (Fin P₀.g → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ := fun z W f =>
    ev u m (κ z).1 (d (κ z)) z W f + fderiv ℂ (fn u m W f) z (fun a => h a (κ z) z)
  have hs : ∀ j z W f, z ∈ dom u m j.1 → z ∈ dom u m W →
      s z W f = ev u m j.1 (d j) z W f + fderiv ℂ (fn u m W f) z (fun a => h a j z) := by
    intro j z W f hj hW
    have e₁ := hC (κ z) j z W f (hκ z) hj hW
    have e₂ : C (κ z) j z = (fun a => h a j z) - fun a => h a (κ z) z :=
      funext fun a => hch a (κ z) j z ⟨hκ z, hj⟩
    rw [e₂, map_sub] at e₁
    simp only [s]
    linear_combination e₁
  refine ⟨Matrix.of t, s, fun z => ptDer_add (ptDer_ev u m (hd _) (hκ z)) (ptDer_fderiv u m z _), fun z r => ?_,
    fun W f z hz => ?_, fun l W f z hz => ?_⟩
  · simp only [s]
    rw [ev_base u m (hd _) (hκ z), fderiv_const_eq u m hm.w, add_zero]
  · have hz' : z ∈ dom u m (W ⊓ (κ z).1) := (dom_inf u m).2 ⟨hz, hκ z⟩
    have hn := (dom_open u m _).mem_nhds hz'
    have h₁ := (ev_hol u m (W₀ := (κ z).1) (d := d (κ z)) W f).add
      (fderiv_field_hol u m W f (S := dom u m (W ⊓ (κ z).1)) (fun y hy => ((dom_inf u m).1 hy).1)
        (fun a => h a (κ z)) fun a => (hh a (κ z)).1.mono fun y hy => ((dom_inf u m).1 hy).2)
    refine ((h₁.congr fun y hy => ?_).differentiableAt hn).differentiableWithinAt
    exact hs (κ z) y W f ((dom_inf u m).1 hy).2 ((dom_inf u m).1 hy).1
  · rw [hs (κ z) (z + l) W f ((dom_per u m l _ z).2 (hκ z)) ((dom_per u m l _ z).2 hz), ev_per, fderiv_per]
    have e : (fun a => h a (κ z) (z + l)) = (fun a => h a (κ z) z) + (Matrix.of t).mulVec (star (l : Fin P₀.g → ℂ)) :=
      funext fun a => (hh a (κ z)).2 l z (hκ z)
    rw [e, map_add]
    simp only [s]
    ring

end GlobalTheory.KS.Exist
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analytic_kodairaSpencer_class : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D, IsDer x₀ D → ∃ Θ s, KSRel u p m D Θ s := by
  atlas_forward_decl GlobalTheory.KS.Exist.exists_ksRel
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.Uniq

section
variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g) {X : Scheme.{0}}

theorem ex_add_lattice (z : Fin g → ℂ) (l : u.Λ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]

theorem mem_dom_add_lattice (m : A₀.left ⟶ X) (W : X.Opens) (z : Fin g → ℂ) (l : u.Λ) :
    z + l ∈ dom u m W ↔ z ∈ dom u m W := by
  show ⊤ ≤ ((u.ex (z + l)).left ≫ m) ⁻¹ᵁ W ↔ ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ W
  rw [ex_add_lattice]

theorem fderiv_fn_add_lattice (m : A₀.left ⟶ X) (W : X.Opens) (f : Γ(X, W)) (z : Fin g → ℂ) (l : u.Λ) :
    fderiv ℂ (fn u m W f) (z + l) = fderiv ℂ (fn u m W f) z := by
  have h : (fun w => fn u m W f (w + (l : Fin g → ℂ))) = fn u m W f := by
    funext w
    unfold fn
    rw [ex_add_lattice]
  calc fderiv ℂ (fn u m W f) (z + l) = fderiv ℂ (fun w => fn u m W f (w + (l : Fin g → ℂ))) z :=
        (fderiv_comp_add_right (l : Fin g → ℂ)).symm
    _ = fderiv ℂ (fn u m W f) z := by rw [h]

theorem ptDer_sub {y : Sp ℂ ⟶ X} {δ δ' : ∀ W : X.Opens, Γ(X, W) → ℂ} (h : PtDer y δ) (h' : PtDer y δ') :
    PtDer y (fun W f => δ W f - δ' W f) where
  add W hW f f' := by
    rw [h.add W hW f f', h'.add W hW f f']
    ring
  mul W hW f f' := by
    rw [h.mul W hW f f', h'.mul W hW f f']
    ring
  res W W' hle hW' f := by
    rw [h.res W W' hle hW' f, h'.res W W' hle hW' f]
end

theorem ks_unique : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D Θ Θ' s s', KSRel u p m D Θ s → KSRel u p m D Θ' s' → Θ = Θ' := by
  intro P₀ u Hm χ hG R _ x₀ X p m hp hpb D Θ Θ' s s' hs hs'
  obtain ⟨w, hwd, hw⟩ := GlobalTheory.T.exists_differentiableOn_verticalVectorField P₀ u Hm χ hG R x₀ X p m hp hpb P₀.g Set.univ id
    (fun z W f => s z W f - s' z W f) isOpen_univ differentiable_id
    (fun z _ => ⟨ptDer_sub (hs.der z) (hs'.der z), fun r => by
      show s z ⊤ (constFn p ⊤ r) - s' z ⊤ (constFn p ⊤ r) = 0
      rw [hs.base, hs'.base, sub_self]⟩)
    (fun W f => ((hs.hol W f).sub (hs'.hol W f)).mono fun z hz => hz.2)
  have hw' : ∀ z W f, z ∈ dom u m W → s z W f - s' z W f = fderiv ℂ (fn u m W f) z (w z) :=
    fun z W f hz => hw z (Set.mem_univ z) W f hz
  have hper : ∀ (l : u.Λ) z, w (z + l) = w z + (Θ - Θ').mulVec (star (l : Fin P₀.g → ℂ)) := by
    intro l z
    obtain ⟨v, -, huniq⟩ := GlobalTheory.T.existsUnique_uniformising_vector_vertical_tangent P₀ u Hm χ hG R x₀ X p m hp hpb z
      (fun W f => s z W f - s' z W f) (ptDer_sub (hs.der z) (hs'.der z)) (fun r => by
        show s z ⊤ (constFn p ⊤ r) - s' z ⊤ (constFn p ⊤ r) = 0
        rw [hs.base, hs'.base, sub_self])
    have e1 := huniq (w z) (fun W f hz => hw' z W f hz)
    have e2 := huniq (w (z + l) - (Θ - Θ').mulVec (star (l : Fin P₀.g → ℂ))) (fun W f hz => by
      have a1 := hw' (z + l) W f ((mem_dom_add_lattice u m W z l).2 hz)
      have a2 := hs.per l W f z hz
      have a3 := hs'.per l W f z hz
      rw [fderiv_fn_add_lattice] at a1
      show s z W f - s' z W f = _
      rw [map_sub, Matrix.sub_mulVec, map_sub]
      linear_combination a1 - a2 + a3)
    rw [← e1] at e2
    exact sub_eq_iff_eq_add.mp e2
  have hdisc : DiscreteTopology u.Λ := u.discrete
  have hspan : Submodule.span ℝ (u.Λ : Set (Fin P₀.g → ℂ)) = ⊤ := u.full
  have hwd' : Differentiable ℂ w := differentiableOn_univ.mp hwd
  ext i j
  have key := GlobalTheory.entire_antilinear_periods_const P₀.g u.Λ hdisc hspan (fun z => w z i) ((Θ - Θ') i)
    (differentiable_pi.mp hwd' i) (fun l z => congrFun (hper l z) i)
  have hij := congrFun key.1 j
  simp only [Matrix.sub_apply, Pi.zero_apply, sub_eq_zero] at hij
  exact hij

end GlobalTheory.KS.Uniq
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.Lin

section
variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} {u : HolUnif A₀ L₀ g} {X : Scheme.{0}}
  {R : Type} [CommRing R] {p : X ⟶ Sp R} {m : A₀.left ⟶ X}

theorem ksRel_add {D D' : R → ℂ} {Θ Θ' : Matrix (Fin g) (Fin g) ℂ}
    {s s' : (Fin g → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ}
    (h : KSRel u p m D Θ s) (h' : KSRel u p m D' Θ' s') :
    KSRel u p m (fun r => D r + D' r) (Θ + Θ') (fun z W f => s z W f + s' z W f) where
  der z :=
    { add := fun W hW f f' => by
        simp only [(h.der z).add W hW, (h'.der z).add W hW]
        ring
      mul := fun W hW f f' => by
        simp only [(h.der z).mul W hW, (h'.der z).mul W hW]
        ring
      res := fun W W' hle hW' f => by
        simp only [(h.der z).res W W' hle hW', (h'.der z).res W W' hle hW'] }
  base z r := by simp only [h.base, h'.base]
  hol W f := (h.hol W f).add (h'.hol W f)
  per l W f z hz := by
    simp only [h.per l W f z hz, h'.per l W f z hz, Matrix.add_mulVec, map_add]
    ring

theorem ksRel_smul (c : ℂ) {D : R → ℂ} {Θ : Matrix (Fin g) (Fin g) ℂ}
    {s : (Fin g → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ} (h : KSRel u p m D Θ s) :
    KSRel u p m (fun r => c * D r) (c • Θ) (fun z W f => c * s z W f) where
  der z :=
    { add := fun W hW f f' => by
        simp only [(h.der z).add W hW]
        ring
      mul := fun W hW f f' => by
        simp only [(h.der z).mul W hW]
        ring
      res := fun W W' hle hW' f => by
        simp only [(h.der z).res W W' hle hW'] }
  base z r := by simp only [h.base]
  hol W f := (h.hol W f).const_mul c
  per l W f z hz := by
    simp only [h.per l W f z hz, Matrix.smul_mulVec, map_smul, smul_eq_mul]
    ring
end

theorem ks_linear : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (o R : Type) [CommRing o] [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap (algebraMap R ℂ)) → ∃ κ : Derivation o R ℂ →ₗ[ℂ] Matrix (Fin P₀.g) (Fin P₀.g) ℂ, ∀ D : Derivation o R ℂ, ∃ s, KSRel u p m (fun r => D r) (κ D) s := by
  intro P₀ u Hm χ hG o R _ _ _ _ _ _ X p m hs hpb
  have hder : ∀ D : Derivation o R ℂ, IsDer (algebraMap R ℂ) (fun r => D r) := fun D =>
    ⟨fun a b => D.map_add a b, fun a b => by
      show D (a * b) = _
      rw [D.leibniz, Algebra.smul_def, Algebra.smul_def]⟩
  have hex : ∀ D : Derivation o R ℂ, ∃ Θ s, KSRel u p m (fun r => D r) Θ s := fun D =>
    GlobalTheory.T.exists_analytic_kodairaSpencer_class P₀ u Hm χ hG R (algebraMap R ℂ) X p m hs hpb _ (hder D)
  choose Θ s hΘ using hex
  have huniq : ∀ (D : Derivation o R ℂ) Θ' s', KSRel u p m (fun r => D r) Θ' s' → Θ D = Θ' :=
    fun D Θ' s' h => GlobalTheory.KS.Uniq.ks_unique P₀ u Hm χ hG R (algebraMap R ℂ) X p m hs hpb _ _ _ _ _ (hΘ D) h
  refine ⟨{ toFun := Θ, map_add' := ?_, map_smul' := ?_ }, fun D => ⟨s D, hΘ D⟩⟩
  · intro D D'
    apply huniq (D + D')
    have e : (fun r => (D + D') r) = fun r => D r + D' r := funext fun _ => Derivation.add_apply _
    rw [e]
    exact ksRel_add (hΘ D) (hΘ D')
  · intro c D
    rw [RingHom.id_apply]
    apply huniq (c • D)
    have e : (fun r => (c • D) r) = fun r => c * D r := funext fun r => by
      rw [Derivation.smul_apply, smul_eq_mul]
    rw [e]
    exact ksRel_smul c (hΘ D)

end GlobalTheory.KS.Lin
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencer_matrix_linear_in_derivation : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (o R : Type) [CommRing o] [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap (algebraMap R ℂ)) → ∃ κ : Derivation o R ℂ →ₗ[ℂ] Matrix (Fin P₀.g) (Fin P₀.g) ℂ, ∀ D : Derivation o R ℂ, ∃ s, KSRel u p m (fun r => D r) (κ D) s := by
  atlas_forward_decl GlobalTheory.KS.Lin.ks_linear
end

section
open Complex Matrix
open scoped ContDiff BigOperators Real
open MeasureTheory Module
open scoped Pointwise

namespace GlobalTheory

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in

theorem setIntegral_comp_add_of_lattice_periodic [SecondCountableTopology E]
    (L : Submodule ℤ E) [Countable L] {D : Set E}
    (hD : IsAddFundamentalDomain L D μ) {F : E → ℂ} (hF : ∀ (l : L) z, F (z + l) = F z) (c : E) :
    ∫ z in D, F (z + c) ∂μ = ∫ z in D, F z ∂μ := by
  have : VAddInvariantMeasure L E μ := ⟨fun g s _ => measure_preimage_add μ (g : E) s⟩
  have hpres := measurePreserving_add_right μ c
  have hD' : IsAddFundamentalDomain L ((fun x => x + c) '' D) μ :=
    hD.image_of_equiv (Equiv.addRight c)
      (measurePreserving_add_right μ (-c)).quasiMeasurePreserving (Equiv.refl _)
      (fun g x => add_assoc _ _ _)
  rw [← hpres.setIntegral_image_emb (MeasurableEquiv.addRight c).measurableEmbedding]
  refine (hD'.setIntegral_eq hD fun g x => ?_)
  show F ((g : E) + x) = F x
  rw [add_comm]
  exact hF g x

theorem setIntegral_fderiv_eq_zero_of_lattice_periodic
    (L : Submodule ℤ E) [Countable L] {D : Set E}
    (hD : IsAddFundamentalDomain L D μ) (hm : MeasurableSet D) (hb : Bornology.IsBounded D)
    {F : E → ℂ} (hF1 : ContDiff ℝ 1 F) (hF : ∀ (l : L) z, F (z + l) = F z) (v : E) :
    ∫ z in D, fderiv ℝ F z v ∂μ = 0 := by
  have hcont : Continuous (fderiv ℝ F) := hF1.continuous_fderiv one_ne_zero
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  have hK : IsCompact (Metric.closedBall (0 : E) (R + ‖v‖)) := isCompact_closedBall _ _
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  have hfin : μ D < ⊤ := hb.measure_lt_top
  have : IsFiniteMeasure (μ.restrict D) := isFiniteMeasure_restrict.2 hfin.ne
  have hint : ∀ G : E → ℂ, Continuous G → Integrable G (μ.restrict D) := fun G hG =>
    (hG.continuousOn.integrableOn_compact (isCompact_closedBall (0 : E) R)).mono_set hR
  have hmem : ∀ z ∈ D, ∀ t ∈ Metric.ball (0 : ℝ) 1,
      z + t • v ∈ Metric.closedBall (0 : E) (R + ‖v‖) := by
    intro z hz t ht
    rw [mem_closedBall_zero_iff]
    have h1 : ‖z‖ ≤ R := mem_closedBall_zero_iff.1 (hR hz)
    have ht' : ‖t‖ < 1 := by simpa using ht
    have h2 : ‖t • v‖ ≤ ‖v‖ := by
      rw [norm_smul]
      nlinarith [norm_nonneg v, norm_nonneg t]
    calc ‖z + t • v‖ ≤ ‖z‖ + ‖t • v‖ := norm_add_le _ _
      _ ≤ R + ‖v‖ := add_le_add h1 h2
  have hderiv : ∀ (z : E) (t : ℝ),
      HasDerivAt (fun s : ℝ => F (z + s • v)) (fderiv ℝ F (z + t • v) v) t := by
    intro z t
    have hd : HasFDerivAt F (fderiv ℝ F (z + t • v)) (z + t • v) :=
      (hF1.differentiable one_ne_zero _).hasFDerivAt
    have hl : HasDerivAt (fun s : ℝ => z + s • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add z
    exact hd.comp_hasDerivAt t hl
  have hmeas : ∀ᶠ s in nhds (0 : ℝ), AEStronglyMeasurable (fun z => F (z + s • v)) (μ.restrict D) :=
    Filter.Eventually.of_forall fun s =>
      (hF1.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable
  have hint0 : Integrable (fun z => F (z + (0 : ℝ) • v)) (μ.restrict D) :=
    hint _ (hF1.continuous.comp (continuous_id.add continuous_const))
  have hmeas' : AEStronglyMeasurable (fun z => fderiv ℝ F (z + (0 : ℝ) • v) v) (μ.restrict D) :=
    ((hcont.comp (continuous_id.add continuous_const)).clm_apply continuous_const).aestronglyMeasurable
  have hbound : ∀ᵐ z ∂(μ.restrict D), ∀ s ∈ Metric.ball (0 : ℝ) 1,
      ‖fderiv ℝ F (z + s • v) v‖ ≤ M * ‖v‖ := by
    refine (ae_restrict_iff' hm).2 (Filter.Eventually.of_forall fun z hz s hs => ?_)
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hM _ (hmem z hz s hs)) (norm_nonneg _))
  have hdiff : ∀ᵐ z ∂(μ.restrict D), ∀ s ∈ Metric.ball (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => F (z + t • v)) (fderiv ℝ F (z + s • v) v) s :=
    Filter.Eventually.of_forall fun z s _ => hderiv z s
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (μ := μ.restrict D)
    (F := fun (s : ℝ) (z : E) => F (z + s • v)) (x₀ := 0) (bound := fun _ => M * ‖v‖)
    (F' := fun (s : ℝ) (z : E) => fderiv ℝ F (z + s • v) v)
    (Metric.ball_mem_nhds (0 : ℝ) one_pos) hmeas hint0 hmeas' hbound (integrable_const _) hdiff
  have hconst : (fun s : ℝ => ∫ z in D, F (z + s • v) ∂μ) = fun _ => ∫ z in D, F z ∂μ :=
    funext fun s => setIntegral_comp_add_of_lattice_periodic μ L hD hF (s • v)
  have h3 : HasDerivAt (fun _ : ℝ => ∫ z in D, F z ∂μ)
      (∫ z in D, fderiv ℝ F (z + (0 : ℝ) • v) v ∂μ) 0 := by
    rw [← hconst]
    exact key.2
  simpa using h3.unique (hasDerivAt_const _ _)

theorem const_eq_zero_of_sum_fderiv_lattice_periodic
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] {ι : Type*} [Fintype ι]
    {F : ι → E → ℂ} {a : ι → ℂ} {v : ι → E} {C : ℂ}
    (hF : ∀ k, ContDiff ℝ 1 (F k) ∧ ∀ (l : L) z, F k (z + l) = F k z)
    (hC : ∀ z, ∑ k, a k * fderiv ℝ (F k) z (v k) = C) : C = 0 := by
  classical
  let μ : Measure E := Measure.addHaar
  let b := Module.Free.chooseBasis ℤ L
  have hD : IsAddFundamentalDomain L (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) μ :=
    ZLattice.isAddFundamentalDomain b μ
  have hm : MeasurableSet (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) :=
    ZSpan.fundamentalDomain_measurableSet _
  have hb : Bornology.IsBounded (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) :=
    ZSpan.fundamentalDomain_isBounded _
  set D := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ) with hDdef
  have hzero : ∀ k, ∫ z in D, fderiv ℝ (F k) z (v k) ∂μ = 0 := fun k =>
    setIntegral_fderiv_eq_zero_of_lattice_periodic μ L hD hm hb (hF k).1 (hF k).2 (v k)
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  have hint : ∀ k, IntegrableOn (fun z => a k * fderiv ℝ (F k) z (v k)) D μ := fun k =>
    ((continuous_const.mul
      (((hF k).1.continuous_fderiv one_ne_zero).clm_apply continuous_const)).continuousOn.integrableOn_compact
        (isCompact_closedBall (0 : E) R)).mono_set hR
  have hsum : ∫ z in D, (∑ k, a k * fderiv ℝ (F k) z (v k)) ∂μ = 0 := by
    rw [integral_finsetSum _ (fun k _ => hint k)]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [integral_const_mul, hzero k, mul_zero]
  simp_rw [hC] at hsum
  rw [setIntegral_const] at hsum
  have : VAddInvariantMeasure L E μ := ⟨fun g s _ => measure_preimage_add μ (g : E) s⟩
  have hne : μ D ≠ 0 := hD.measure_ne_zero (NeZero.ne μ)
  have hfin : μ D ≠ ⊤ := hb.measure_lt_top.ne
  rcases smul_eq_zero.1 hsum with h | h
  · exact absurd h (ENNReal.toReal_ne_zero.2 ⟨hne, hfin⟩)
  · exact h

end General

theorem const_eq_zero_of_sum_fderiv_periodic :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ →
      Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
      ∀ (n : ℕ) (F : Fin n → (Fin g → ℂ) → ℂ) (a : Fin n → ℂ) (v : Fin n → (Fin g → ℂ)) (C : ℂ),
      (∀ k, ContDiff ℝ 1 (F k) ∧ ∀ (l : Λ) z, F k (z + l) = F k z) →
      (∀ z, ∑ k, a k * fderiv ℝ (F k) z (v k) = C) → C = 0 := by
  intro g Λ hdisc hspan n F a v C hF hC
  have : IsZLattice ℝ Λ := ⟨hspan⟩
  exact const_eq_zero_of_sum_fderiv_lattice_periodic Λ hF hC

end GlobalTheory
end

section
section
open Complex Matrix
open scoped ContDiff BigOperators Real
open Filter Topology

namespace GlobalTheory.PeriodSymm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

noncomputable def dbar (f : E → ℂ) (u : E) (z : E) : ℂ :=
  fderiv ℝ f z u + I * fderiv ℝ f z (I • u)

theorem dbar_congr {f f' : E → ℂ} {z : E} (h : f =ᶠ[𝓝 z] f') (u : E) :
    dbar f u z = dbar f' u z := by
  rw [dbar, dbar, h.fderiv_eq (𝕜 := ℝ)]

theorem dbar_holo {f : E → ℂ} {z : E} (h : DifferentiableAt ℂ f z) (u : E) :
    dbar f u z = 0 := by
  rw [dbar, h.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  linear_combination (fderiv ℂ f z u) * I_sq

theorem dbar_add {f f' : E → ℂ} {z : E} (h : DifferentiableAt ℝ f z) (h' : DifferentiableAt ℝ f' z)
    (u : E) : dbar (fun x => f x + f' x) u z = dbar f u z + dbar f' u z := by
  have H : HasFDerivAt (fun x => f x + f' x) (fderiv ℝ f z + fderiv ℝ f' z) z :=
    h.hasFDerivAt.add h'.hasFDerivAt
  rw [dbar, dbar, dbar, H.fderiv]
  simp only [ContinuousLinearMap.add_apply]
  ring

theorem dbar_sub {f f' : E → ℂ} {z : E} (h : DifferentiableAt ℝ f z) (h' : DifferentiableAt ℝ f' z)
    (u : E) : dbar (fun x => f x - f' x) u z = dbar f u z - dbar f' u z := by
  have H : HasFDerivAt (fun x => f x - f' x) (fderiv ℝ f z - fderiv ℝ f' z) z :=
    h.hasFDerivAt.sub h'.hasFDerivAt
  rw [dbar, dbar, dbar, H.fderiv]
  simp only [ContinuousLinearMap.sub_apply]
  ring

theorem dbar_mul {f f' : E → ℂ} {z : E} (h : DifferentiableAt ℝ f z) (h' : DifferentiableAt ℝ f' z)
    (u : E) : dbar (fun x => f x * f' x) u z = dbar f u z * f' z + f z * dbar f' u z := by
  have H : HasFDerivAt (fun x => f x * f' x) (f z • fderiv ℝ f' z + f' z • fderiv ℝ f z) z :=
    h.hasFDerivAt.mul h'.hasFDerivAt
  rw [dbar, dbar, dbar, H.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

private lemma hasFDerivAt_finset_sum {ι : Type*} (s : Finset ι) {A : ι → E → ℂ}
    {A' : ι → E →L[ℝ] ℂ} {x : E} (h : ∀ i ∈ s, HasFDerivAt (A i) (A' i) x) :
    HasFDerivAt (fun y => ∑ i ∈ s, A i y) (∑ i ∈ s, A' i) x := by
  exact HasFDerivAt.fun_sum h

theorem dbar_sum {ι : Type*} (s : Finset ι) {f : ι → E → ℂ} {z : E}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) (u : E) :
    dbar (fun x => ∑ i ∈ s, f i x) u z = ∑ i ∈ s, dbar (f i) u z := by
  have H := hasFDerivAt_finset_sum s (fun i hi => (h i hi).hasFDerivAt)
  rw [dbar, H.fderiv, ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  rfl

theorem dbar_anti (φ : E →L[ℝ] ℂ) (hφ : ∀ u, φ (I • u) = -I * φ u) (u z : E) :
    dbar φ u z = 2 * φ u := by
  simp only [dbar, ContinuousLinearMap.fderiv, hφ]
  linear_combination (-φ u) * I_sq

theorem dbar_translate (f : E → ℂ) (u z l : E) :
    dbar (fun x => f (x + l)) u z = dbar f u (z + l) := by
  simp only [dbar, fderiv_comp_add_right]

theorem dbar_contDiffAt {f : E → ℂ} {z : E} (h : ContDiffAt ℝ 2 f z) (u : E) :
    ContDiffAt ℝ 1 (dbar f u) z := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) z := h.fderiv_right (by norm_num)
  exact (h1.clm_apply contDiffAt_const).add (contDiffAt_const.mul (h1.clm_apply contDiffAt_const))

private lemma fderiv_apply_lemma {f : E → ℂ} {z : E}
    (hD : DifferentiableAt ℝ (fderiv ℝ f) z) (u w : E) :
    fderiv ℝ (fun x => fderiv ℝ f x u) z w = fderiv ℝ (fderiv ℝ f) z w u := by
  rw [fderiv_clm_apply hD (differentiableAt_const u)]
  simp

theorem dbar_symm {f : E → ℂ} {z : E} (h : ContDiffAt ℝ 2 f z) (u v : E) :
    dbar (dbar f u) v z = dbar (dbar f v) u z := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) z := h.fderiv_right (by norm_num)
  have hD : DifferentiableAt ℝ (fderiv ℝ f) z := h1.differentiableAt (by norm_num)
  have hs := h.isSymmSndFDerivAt (by simp)
  have e : ∀ a w : E, fderiv ℝ (dbar f a) z w
      = fderiv ℝ (fderiv ℝ f) z w a + I * fderiv ℝ (fderiv ℝ f) z w (I • a) := by
    intro a w
    have d1 : DifferentiableAt ℝ (fun x => fderiv ℝ f x a) z :=
      hD.clm_apply (differentiableAt_const _)
    have d2 : DifferentiableAt ℝ (fun x => fderiv ℝ f x (I • a)) z :=
      hD.clm_apply (differentiableAt_const _)
    have H : HasFDerivAt (dbar f a) (fderiv ℝ (fun x => fderiv ℝ f x a) z
        + I • fderiv ℝ (fun x => fderiv ℝ f x (I • a)) z) z :=
      d1.hasFDerivAt.add (d2.hasFDerivAt.const_mul I)
    rw [H.fderiv, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      fderiv_apply_lemma hD, fderiv_apply_lemma hD]
  rw [dbar, dbar, e, e, e, e, hs v u, hs v (I • u), hs (I • v) u, hs (I • v) (I • u)]
  ring

private lemma dbar_const_mul {f : E → ℂ} {z : E} (c : ℂ) (h : DifferentiableAt ℝ f z)
    (u : E) : dbar (fun x => c * f x) u z = c * dbar f u z := by
  have H : HasFDerivAt (fun x => c * f x) (c • fderiv ℝ f z) z := h.hasFDerivAt.const_mul c
  rw [dbar, dbar, H.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

private lemma contDiffAt_two_of_contDiffOn_infty_of_isOpen {s : Set E} {f : E → ℂ} {x : E} (hf : ContDiffOn ℝ ∞ f s)
    (hs : IsOpen s) (hx : x ∈ s) : ContDiffAt ℝ 2 f x := by
  have := (contDiffOn_infty.1 hf 2).contDiffAt (hs.mem_nhds hx)
  exact_mod_cast this

private lemma contDiffOn_infty_finset_sum {ι : Type*} (s : Finset ι) {A : ι → E → ℂ} {t : Set E}
    (h : ∀ i ∈ s, ContDiffOn ℝ ∞ (A i) t) : ContDiffOn ℝ ∞ (fun y => ∑ i ∈ s, A i y) t := by
  exact ContDiffOn.sum h

private lemma contDiffAt_one_finset_sum {ι : Type*} (s : Finset ι) {A : ι → E → ℂ} {x : E}
    (h : ∀ i ∈ s, ContDiffAt ℝ 1 (A i) x) : ContDiffAt ℝ 1 (fun y => ∑ i ∈ s, A i y) x := by
  exact ContDiffAt.sum h

theorem symm_of_cocycle (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (hd : DiscreteTopology Λ)
    (hsp : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (ι : Type) (U : ι → Set (Fin g → ℂ))
    (p : ι → Fin g → (Fin g → ℂ) → ℂ) (k : ι → ι → (Fin g → ℂ) → ℂ)
    (θ h : Fin g → (Fin g → ℂ) →L[ℝ] ℂ)
    (hθ : ∀ m u, θ m (I • u) = -I * θ m u) (hh : ∀ m u, h m (I • u) = -I * h m u)
    (hU : ∀ i, IsOpen (U i)) (hinv : ∀ i (l : Λ) z, z ∈ U i → z + l ∈ U i)
    (hcov : ∀ z, ∃ i, z ∈ U i) (hp : ∀ i m, DifferentiableOn ℂ (p i m) (U i))
    (hper : ∀ i m (l : Λ), ∀ z ∈ U i, p i m (z + l) = p i m z - h m l)
    (hk : ∀ i j, DifferentiableOn ℂ (k i j) (U i ∩ U j))
    (hkc : ∀ i j m, ∀ z ∈ U i ∩ U j ∩ U m, k i j z + k j m z = k i m z)
    (hkp : ∀ i j (l : Λ), ∀ z ∈ U i ∩ U j,
      k i j (z + l) = k i j z + (∑ m, θ m l * p i m z - ∑ m, θ m l * p j m z))
    (u v : Fin g → ℂ) : ∑ m, θ m u * h m v = ∑ m, θ m v * h m u := by
  classical
  have hpS : ∀ i m, ContDiffOn ℝ ∞ (p i m) (U i) := fun i m =>
    ((GlobalTheory.cauchyRiemann_iff_differentiableOn_complex g (U i) (p i m) (hU i)).2 (hp i m)).1
  have hkS : ∀ i j, ContDiffOn ℝ ∞ (k i j) (U i ∩ U j) := fun i j =>
    ((GlobalTheory.cauchyRiemann_iff_differentiableOn_complex g _ (k i j) ((hU i).inter (hU j))).2
      (hk i j)).1

  obtain ⟨G, hG⟩ : ∃ G : ι → ι → (Fin g → ℂ) → ℂ, ∀ i j z,
      G i j z = k i j z - ∑ m, θ m z * (p i m z - p j m z) := ⟨_, fun _ _ _ => rfl⟩
  have hGs : ∀ i j, ContDiffOn ℝ ∞ (G i j) (U i ∩ U j) := by
    intro i j
    refine ContDiffOn.congr ?_ (fun z _ => hG i j z)
    have hs : ContDiffOn ℝ ∞ (fun z => ∑ m, θ m z * (p i m z - p j m z)) (U i ∩ U j) :=
      contDiffOn_infty_finset_sum (A := fun m z => θ m z * (p i m z - p j m z)) Finset.univ fun m _ => by
        exact (θ m).contDiff.contDiffOn.mul
          (((hpS i m).mono Set.inter_subset_left).sub ((hpS j m).mono Set.inter_subset_right))
    exact (hkS i j).sub hs
  have hGper : ∀ i j (l : Λ), ∀ z ∈ U i ∩ U j, G i j (z + l) = G i j z := by
    intro i j l z hz
    have hi : ∀ m, p i m (z + l) = p i m z - h m l := fun m => hper i m l z hz.1
    have hj : ∀ m, p j m (z + l) = p j m z - h m l := fun m => hper j m l z hz.2
    rw [hG, hG, hkp i j l z hz]
    simp only [hi, hj, map_add, sub_sub_sub_cancel_right, add_mul, Finset.sum_add_distrib, mul_sub,
      Finset.sum_sub_distrib]
    ring
  have hGc : ∀ i j n, ∀ z ∈ U i ∩ U j ∩ U n, G i j z + G j n z = G i n z := by
    intro i j n z hz
    rw [hG, hG, hG, ← hkc i j n z hz]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  obtain ⟨b, hb, hbG⟩ := GlobalTheory.T.exists_periodic_smooth_coboundary_of_cech_cocycle g Λ hd hsp ι U G hU hinv hcov hGs hGper hGc
  have hbA : ∀ i, ∀ x ∈ U i, ContDiffAt ℝ 2 (b i) x := fun i x hx =>
    contDiffAt_two_of_contDiffOn_infty_of_isOpen (hb i).1 (hU i) hx
  have hbD : ∀ i, ∀ x ∈ U i, DifferentiableAt ℝ (b i) x := fun i x hx =>
    (hbA i x hx).differentiableAt (by norm_num)
  have hpD : ∀ i m, ∀ x ∈ U i, DifferentiableAt ℂ (p i m) x := fun i m x hx =>
    (hp i m).differentiableAt ((hU i).mem_nhds hx)

  obtain ⟨W, hW⟩ : ∃ W : ι → (Fin g → ℂ) → (Fin g → ℂ) → ℂ, ∀ i u,
      W i u = fun y => (∑ m, (2 * θ m u) * (p i m y + h m y)) - dbar (b i) u y :=
    ⟨fun i u y => (∑ m, (2 * θ m u) * (p i m y + h m y)) - dbar (b i) u y, fun _ _ => rfl⟩
  have hPH : ∀ i m, ∀ x ∈ U i, DifferentiableAt ℝ (fun y => p i m y + h m y) x := fun i m x hx =>
    ((hpD i m x hx).restrictScalars ℝ).add (h m).differentiableAt
  have hTD : ∀ i u m, ∀ x ∈ U i,
      DifferentiableAt ℝ (fun y => 2 * θ m u * (p i m y + h m y)) x := fun i u m x hx =>
    (hPH i m x hx).const_mul _
  have hSD : ∀ i u, ∀ x ∈ U i,
      DifferentiableAt ℝ (fun y => ∑ m, (2 * θ m u) * (p i m y + h m y)) x := fun i u x hx =>
    (hasFDerivAt_finset_sum (A := fun m y => 2 * θ m u * (p i m y + h m y)) Finset.univ
      fun m _ => (hTD i u m x hx).hasFDerivAt).differentiableAt
  have hWA : ∀ i u, ∀ x ∈ U i, ContDiffAt ℝ 1 (W i u) x := by
    intro i u x hx
    have h1 : ContDiffAt ℝ 1 (fun y => ∑ m, (2 * θ m u) * (p i m y + h m y)) x :=
      contDiffAt_one_finset_sum (A := fun m y => 2 * θ m u * (p i m y + h m y)) Finset.univ fun m _ => by
        exact contDiffAt_const.mul
          (((contDiffAt_two_of_contDiffOn_infty_of_isOpen (hpS i m) (hU i) hx).of_le (by norm_num)).add
            (h m).contDiff.contDiffAt)
    have h2 := dbar_contDiffAt (hbA i x hx) u
    rw [hW]
    exact h1.sub h2
  have hWeq : ∀ i j u, ∀ x ∈ U i ∩ U j, W i u x = W j u x := by
    intro i j u x hx
    have hO : U i ∩ U j ∈ 𝓝 x := ((hU i).inter (hU j)).mem_nhds hx
    have hev : b j =ᶠ[𝓝 x] fun y => b i y + (k i j y - ∑ m, θ m y * (p i m y - p j m y)) := by
      filter_upwards [hO] with y hy
      have e := hbG i j y hy
      rw [hG] at e
      linear_combination -e
    have hkD : DifferentiableAt ℂ (k i j) x := (hk i j).differentiableAt hO
    have hdD : ∀ m, DifferentiableAt ℂ (fun y => p i m y - p j m y) x := fun m =>
      (hpD i m x hx.1).sub (hpD j m x hx.2)
    have hmD : ∀ m, DifferentiableAt ℝ (fun y => θ m y * (p i m y - p j m y)) x := fun m =>
      (θ m).differentiableAt.mul ((hdD m).restrictScalars ℝ)
    have hterm : ∀ m, dbar (fun y => θ m y * (p i m y - p j m y)) u x
        = 2 * θ m u * (p i m x - p j m x) := by
      intro m
      rw [dbar_mul (θ m).differentiableAt ((hdD m).restrictScalars ℝ), dbar_anti (θ m) (hθ m),
        dbar_holo (hdD m)]
      ring
    have hsumD : DifferentiableAt ℝ (fun y => ∑ m, θ m y * (p i m y - p j m y)) x :=
      (hasFDerivAt_finset_sum (A := fun m y => θ m y * (p i m y - p j m y)) Finset.univ
        fun m _ => (hmD m).hasFDerivAt).differentiableAt
    have hbj : dbar (b j) u x
        = dbar (b i) u x + (0 - ∑ m, 2 * θ m u * (p i m x - p j m x)) := by
      have hk2 : DifferentiableAt ℝ (fun y => k i j y - ∑ m, θ m y * (p i m y - p j m y)) x :=
        (hkD.restrictScalars ℝ).sub hsumD
      rw [dbar_congr hev, dbar_add (hbD i x hx.1) hk2,
        dbar_sub (hkD.restrictScalars ℝ) hsumD, dbar_holo hkD,
        dbar_sum (f := fun m y => θ m y * (p i m y - p j m y)) Finset.univ fun m _ => hmD m]
      simp only [hterm]
    simp only [hW]
    rw [hbj]
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  have hWper : ∀ i u (l : Λ), ∀ x ∈ U i, W i u (x + l) = W i u x := by
    intro i u l x hx
    have hev : (fun y => b i (y + l)) =ᶠ[𝓝 x] b i := by
      filter_upwards [(hU i).mem_nhds hx] with y hy using (hb i).2 l y hy
    have hd : dbar (b i) u (x + l) = dbar (b i) u x := by
      rw [← dbar_translate, dbar_congr hev]
    have hi : ∀ m, p i m (x + l) = p i m x - h m l := fun m => hper i m l x hx
    simp only [hW, hd, hi, map_add]
    congr 1
    exact Finset.sum_congr rfl fun m _ => by ring
  have hWd : ∀ i a c, ∀ x ∈ U i,
      dbar (W i a) c x = ∑ m, (2 * θ m a) * (2 * h m c) - dbar (dbar (b i) a) c x := by
    intro i a c x hx
    have hbd1 : DifferentiableAt ℝ (dbar (b i) a) x :=
      (dbar_contDiffAt (hbA i x hx) a).differentiableAt (by norm_num)
    rw [hW, dbar_sub (hSD i a x hx) hbd1,
      dbar_sum (f := fun m y => 2 * θ m a * (p i m y + h m y)) Finset.univ
        fun m _ => hTD i a m x hx]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [dbar_const_mul _ (hPH i m x hx),
      dbar_add ((hpD i m x hx).restrictScalars ℝ) (h m).differentiableAt, dbar_holo (hpD i m x hx),
      dbar_anti (h m) (hh m)]
    ring

  choose ch hch using hcov
  obtain ⟨P, hP⟩ : ∃ P : (Fin g → ℂ) → (Fin g → ℂ) → ℂ, ∀ a z, P a z = W (ch z) a z :=
    ⟨_, fun _ _ => rfl⟩
  have hPloc : ∀ a i, ∀ x ∈ U i, P a =ᶠ[𝓝 x] W i a := by
    intro a i x hx
    filter_upwards [(hU i).mem_nhds hx] with y hy
    rw [hP]
    exact hWeq _ _ a y ⟨hch y, hy⟩
  have hPper : ∀ a (l : Λ) z, P a (z + l) = P a z := by
    intro a l z
    rw [hP, hP, hWeq (ch (z + l)) (ch z) a (z + l) ⟨hch _, hinv _ l z (hch z)⟩,
      hWper _ a l z (hch z)]
  have hPC : ∀ a, ContDiff ℝ 1 (P a) := by
    intro a
    rw [contDiff_iff_contDiffAt]
    intro z
    exact (hWA (ch z) a z (hch z)).congr_of_eventuallyEq (hPloc a (ch z) z (hch z))
  have s1 : ∀ a c, ∑ m, (2 * θ m a) * (2 * h m c) = 4 * ∑ m, θ m a * h m c := by
    intro a c
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hconst : ∀ z, ∑ n : Fin 4, ![(1 : ℂ), I, -1, -I] n
      * fderiv ℝ (![P u, P u, P v, P v] n) z (![v, I • v, u, I • u] n)
      = 4 * (∑ m, θ m u * h m v - ∑ m, θ m v * h m u) := by
    intro z
    refine Eq.trans (b := dbar (P u) v z - dbar (P v) u z) ?_ ?_
    · simp [Fin.sum_univ_four, dbar]
      ring
    rw [dbar_congr (hPloc u _ z (hch z)), dbar_congr (hPloc v _ z (hch z)),
      hWd _ u v z (hch z), hWd _ v u z (hch z), dbar_symm (hbA _ z (hch z)) u v, s1, s1]
    ring
  have h0 := GlobalTheory.const_eq_zero_of_sum_fderiv_periodic g Λ hd hsp 4 ![P u, P u, P v, P v]
    ![1, I, -1, -I] ![v, I • v, u, I • u] _
    (fun n => ⟨by fin_cases n <;> simp [hPC], fun l z => by fin_cases n <;> simp [hPper]⟩) hconst
  have h4 : (4 : ℂ) ≠ 0 := by norm_num
  exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left h4)

noncomputable def antiRow {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (m : Fin g) :
    (Fin g → ℂ) →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => M.mulVec (star z) m
      map_add' := fun x y => by simp [star_add, Matrix.mulVec_add]
      map_smul' := fun r x => by
        simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm] }

theorem antiRow_apply {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (m : Fin g) (z : Fin g → ℂ) :
    antiRow M m z = M.mulVec (star z) m := rfl

theorem antiRow_I {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (m : Fin g) (z : Fin g → ℂ) :
    antiRow M m (I • z) = -I * antiRow M m z := by
  rw [antiRow_apply, antiRow_apply, star_smul, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  simp [Complex.star_def]

theorem clm_eq_sum {g : ℕ} (L : (Fin g → ℂ) →L[ℂ] ℂ) (v : Fin g → ℂ) :
    L v = ∑ m, v m * L (Pi.single m 1) := by
  have hv : v = ∑ m, v m • (Pi.single m 1 : Fin g → ℂ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_sum, map_smul, smul_eq_mul]

theorem logDeriv_translate {g : ℕ} {U : Set (Fin g → ℂ)} (hU : IsOpen U) {a : (Fin g → ℂ) → ℂ}
    (ha : DifferentiableOn ℂ a U) (ha0 : ∀ z ∈ U, a z ≠ 0) (l w : Fin g → ℂ) (e : ℂ)
    (hinv : ∀ z ∈ U, z + l ∈ U)
    (hf : ∀ z ∈ U, a z = e * cexp (π * (z ⬝ᵥ w)) * a (z + l)) (m : Fin g) {z : Fin g → ℂ}
    (hz : z ∈ U) :
    fderiv ℂ a (z + l) (Pi.single m 1) / a (z + l)
      = fderiv ℂ a z (Pi.single m 1) / a z - π * w m := by
  have hz' : z + l ∈ U := hinv z hz
  have ha1 : a (z + l) ≠ 0 := ha0 _ hz'
  let L : (Fin g → ℂ) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun x => x ⬝ᵥ w
      map_add' := fun x y => add_dotProduct x y w
      map_smul' := fun c x => smul_dotProduct c x w }
  have hL : ∀ x, L x = x ⬝ᵥ w := fun x => rfl
  have hE : HasFDerivAt (fun x => e * cexp (π * (x ⬝ᵥ w)))
      (e • (cexp (π * (z ⬝ᵥ w)) • ((π : ℂ) • L))) z := by
    have h0 : HasFDerivAt (fun x => (π : ℂ) * L x) ((π : ℂ) • L) z := L.hasFDerivAt.const_mul _
    exact h0.cexp.const_mul e
  have hA0 : HasFDerivAt a (fderiv ℂ a (z + l)) (z + l) :=
    (ha.differentiableAt (hU.mem_nhds hz')).hasFDerivAt
  have hA : HasFDerivAt (fun x => a (x + l)) (fderiv ℂ a (z + l)) z := by
    have h3 := hA0.comp z ((hasFDerivAt_id z).add_const l)
    simp only [ContinuousLinearMap.comp_id] at h3
    exact h3
  have hev : a =ᶠ[𝓝 z] fun x => e * cexp (π * (x ⬝ᵥ w)) * a (x + l) := by
    filter_upwards [hU.mem_nhds hz] with x hx using hf x hx
  have hP : HasFDerivAt (fun x => e * cexp (π * (x ⬝ᵥ w)) * a (x + l))
      ((e * cexp (π * (z ⬝ᵥ w))) • fderiv ℂ a (z + l)
        + a (z + l) • (e • (cexp (π * (z ⬝ᵥ w)) • ((π : ℂ) • L)))) z := hE.mul hA
  have hD := (hP.congr_of_eventuallyEq hev).fderiv
  have hD' : fderiv ℂ a z (Pi.single m 1)
      = e * cexp (π * (z ⬝ᵥ w)) * fderiv ℂ a (z + l) (Pi.single m 1)
        + a (z + l) * (e * (cexp (π * (z ⬝ᵥ w)) * (π * w m))) := by
    rw [hD]
    simp [hL]
  have hEz : e * cexp (π * (z ⬝ᵥ w)) ≠ 0 := by
    intro h0
    exact ha0 z hz (by rw [hf z hz, h0, zero_mul])
  have he : e ≠ 0 := left_ne_zero_of_mul hEz
  have hX : cexp (π * (z ⬝ᵥ w)) ≠ 0 := Complex.exp_ne_zero _
  rw [hD', hf z hz]
  field_simp
  ring

theorem period_symm : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (Hm Θ : Matrix (Fin g) (Fin g) ℂ) (ι : Type) (U : ι → Set (Fin g → ℂ)) (a : ι → (Fin g → ℂ) → ℂ) (k : ι → ι → (Fin g → ℂ) → ℂ) (e : Λ → ℂ), (∀ i, IsOpen (U i)) → (∀ i (l : Λ) z, z ∈ U i → z + l ∈ U i) → (∀ z, ∃ i, z ∈ U i) → (∀ i, DifferentiableOn ℂ (a i) (U i) ∧ ∀ z ∈ U i, a i z ≠ 0) → (∀ i (l : Λ), ∀ z ∈ U i, a i z = e l * cexp (π * (z ⬝ᵥ Hm.mulVec (star (l : (Fin g → ℂ))))) * a i (z + l)) → (∀ i j, DifferentiableOn ℂ (k i j) (U i ∩ U j)) → (∀ i j m, ∀ z ∈ U i ∩ U j ∩ U m, k i j z + k j m z = k i m z) → (∀ i j (l : Λ), ∀ z ∈ U i ∩ U j, k i j (z + l) = k i j z + (fderiv ℂ (a i) z (Θ.mulVec (star (l : (Fin g → ℂ)))) / a i z - fderiv ℂ (a j) z (Θ.mulVec (star (l : (Fin g → ℂ)))) / a j z)) → ∀ z w, Θ.mulVec (star z) ⬝ᵥ Hm.mulVec (star w) = Θ.mulVec (star w) ⬝ᵥ Hm.mulVec (star z) := by
  intro g Λ hd hsp Hm Θ ι U a k e hU hinv hcov ha hf hk hkc hkp z w
  have key : ∑ m, antiRow Θ m z * ((Real.pi) • antiRow Hm m) w
      = ∑ m, antiRow Θ m w * ((Real.pi) • antiRow Hm m) z := by
    refine symm_of_cocycle g Λ hd hsp ι U (fun i m x => fderiv ℂ (a i) x (Pi.single m 1) / a i x)
      k (fun m => antiRow Θ m) (fun m => (Real.pi) • antiRow Hm m) (fun m u => antiRow_I Θ m u)
      ?_ hU hinv hcov ?_ ?_ hk hkc ?_ z w
    · intro m u
      simp only [ContinuousLinearMap.smul_apply, antiRow_I, Complex.real_smul]
      ring
    · intro i m
      have h1 : DifferentiableOn ℂ (fun x => fderiv ℂ (a i) x (Pi.single m 1)) (U i) :=
        ((GlobalTheory.cauchyRiemann_iff_differentiableOn_complex g (U i) (a i) (hU i)).2 (ha i).1).2 _
      have h2 : DifferentiableOn ℂ (fun x => (a i x)⁻¹) (U i) := (ha i).1.inv (ha i).2
      exact (h1.mul h2).congr fun x _ => div_eq_mul_inv _ _
    · intro i m l x hx
      simp only [ContinuousLinearMap.smul_apply, antiRow_apply, Complex.real_smul]
      exact logDeriv_translate (hU i) (ha i).1 (ha i).2 (l : Fin g → ℂ) _ (e l)
        (fun y hy => hinv i l y hy) (fun y hy => hf i l y hy) m hx
    · intro i j l x hx
      rw [hkp i j l x hx, clm_eq_sum (fderiv ℂ (a i) x), clm_eq_sum (fderiv ℂ (a j) x),
        Finset.sum_div, Finset.sum_div]
      simp only [antiRow_apply, mul_div_assoc]
  have e1 : ∀ x y : Fin g → ℂ, ∑ m, antiRow Θ m x * ((Real.pi) • antiRow Hm m) y
      = Real.pi * (Θ.mulVec (star x) ⬝ᵥ Hm.mulVec (star y)) := by
    intro x y
    simp only [ContinuousLinearMap.smul_apply, antiRow_apply, Complex.real_smul, dotProduct,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [e1, e1] at key
  exact mul_left_cancel₀ hπ key

end GlobalTheory.PeriodSymm
end

open Complex Matrix
open scoped ContDiff BigOperators Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_cocycle_periodic_nonvanishing_sections : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (Hm Θ : Matrix (Fin g) (Fin g) ℂ) (ι : Type) (U : ι → Set (Fin g → ℂ)) (a : ι → (Fin g → ℂ) → ℂ) (k : ι → ι → (Fin g → ℂ) → ℂ) (e : Λ → ℂ), (∀ i, IsOpen (U i)) → (∀ i (l : Λ) z, z ∈ U i → z + l ∈ U i) → (∀ z, ∃ i, z ∈ U i) → (∀ i, DifferentiableOn ℂ (a i) (U i) ∧ ∀ z ∈ U i, a i z ≠ 0) → (∀ i (l : Λ), ∀ z ∈ U i, a i z = e l * cexp (π * (z ⬝ᵥ Hm.mulVec (star (l : (Fin g → ℂ))))) * a i (z + l)) → (∀ i j, DifferentiableOn ℂ (k i j) (U i ∩ U j)) → (∀ i j m, ∀ z ∈ U i ∩ U j ∩ U m, k i j z + k j m z = k i m z) → (∀ i j (l : Λ), ∀ z ∈ U i ∩ U j, k i j (z + l) = k i j z + (fderiv ℂ (a i) z (Θ.mulVec (star (l : (Fin g → ℂ)))) / a i z - fderiv ℂ (a j) z (Θ.mulVec (star (l : (Fin g → ℂ)))) / a j z)) → ∀ z w, Θ.mulVec (star z) ⬝ᵥ Hm.mulVec (star w) = Θ.mulVec (star w) ⬝ᵥ Hm.mulVec (star z) := by
  atlas_forward_decl GlobalTheory.PeriodSymm.period_symm
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section

namespace GlobalTheory.KS

variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g) {X : Scheme.{0}}

theorem ex_add_lattice (z : Fin g → ℂ) (l : u.Λ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]

theorem isHolFamily_ex_comp (m : A₀.left ⟶ X) : PowUnif.IsHolFamily fun z => (u.ex z).left ≫ m := PowUnif.IsHolFamily.comp (c := fun z => (u.ex z).left) u.hol m

private theorem top_le_preimage_inf_iff {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (A B : X.Opens) :
    ⊤ ≤ x ⁻¹ᵁ (A ⊓ B) ↔ ⊤ ≤ x ⁻¹ᵁ A ∧ ⊤ ≤ x ⁻¹ᵁ B := by
  show ⊤ ≤ x ⁻¹ᵁ A ⊓ x ⁻¹ᵁ B ↔ _
  exact le_inf_iff

private theorem valAt'_units_val_ne_zero {X : Scheme.{0}} (y : Sp ℂ ⟶ X) {W : X.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W)
    (f : (Γ(X, W))ˣ) : valAt' y W f.val ≠ 0 := by
  have h1 : valAt' y W (f.val * f.inv) = valAt' y W f.val * valAt' y W f.inv := by
    unfold valAt'
    simp only [dif_pos hW]
    unfold valAt
    simp only [map_mul]
  have h2 : valAt' y W (1 : Γ(X, W)) = 1 := by
    unfold valAt'
    simp only [dif_pos hW]
    unfold valAt
    simp only [map_one]
  intro h0
  rw [f.val_inv, h2, h0, zero_mul] at h1
  exact one_ne_zero h1

theorem exists_frame_on_family (hL₀ : L₀.IsLB) (m : A₀.left ⟶ X) (L : LB X) (hL : L.IsLB)
    (hw : LBIso L₀ (L.pull m)) :
    ∃ a : L.ι → (Fin g → ℂ) → ℂ,
      (∀ i, DifferentiableOn ℂ (a i) (dom u m (L.U i)) ∧ ∀ z ∈ dom u m (L.U i), a i z ≠ 0) ∧
      (∀ i j, ∀ z ∈ dom u m (L.U i) ∩ dom u m (L.U j), a i z = fn u m _ (L.g i j).val z * a j z) ∧
      ∀ i (l : u.Λ) z (c : ℂ), z ∈ dom u m (L.U i) →
        (∀ b, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L₀.U b → u.fr b z = c * u.fr b (z + l)) → a i z = c * a i (z + l) := by
  obtain ⟨w, hw⟩ := hw

  have hJ : ∀ (i : L.ι) (z : Fin g → ℂ), ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ L.U i →
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.pull m).U (fun _ => i) := fun i z hi =>
    (PowUnif.le_wchart_iff (u.ex z).left L (fun _ : PUnit => m) (fun _ => i)).2 (fun _ => hi)

  have hM : ∀ (i j : L.ι) (z : Fin g → ℂ), ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ L.U i →
      ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ L.U j →
      valAt' (u.ex z).left ((L.pull m).U (fun _ => i) ⊓ (L.pull m).U (fun _ => j))
        ((L.pull m).g (fun _ => i) (fun _ => j)).val = fn u m (L.U i ⊓ L.U j) (L.g i j).val z := by
    intro i j z hi hj
    have h := PowUnif.val_linComb_g (u.ex z).left L (fun _ : PUnit => m) (fun _ => i) (fun _ => j)
      ((top_le_preimage_inf_iff _ _ _).2 ⟨hJ i z hi, hJ j z hj⟩)
    rw [Fintype.prod_unique] at h
    exact h

  have indep : ∀ (i : L.ι) (z : Fin g → ℂ) (b b' : L₀.ι), ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ L.U i →
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ L₀.U b → ⊤ ≤ (u.ex z).left ⁻¹ᵁ L₀.U b' →
      valAt' (u.ex z).left (((L.pull m).div L₀).U ((fun _ => i), b)) (w.s ((fun _ => i), b)).val * u.fr b z =
        valAt' (u.ex z).left (((L.pull m).div L₀).U ((fun _ => i), b')) (w.s ((fun _ => i), b')).val *
          u.fr b' z := by
    intro i z b b' hi hb hb'
    have hbb : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (((L.pull m).div L₀).U ((fun _ => i), b) ⊓
        ((L.pull m).div L₀).U ((fun _ => i), b')) :=
      (top_le_preimage_inf_iff _ _ _).2 ⟨(top_le_preimage_inf_iff _ _ _).2 ⟨hJ i z hi, hb⟩, (top_le_preimage_inf_iff _ _ _).2 ⟨hJ i z hi, hb'⟩⟩
    have h1 := PowUnif.val_gen hw (u.ex z).left ((fun _ => i), b) ((fun _ => i), b') hbb
    have h2 : valAt' (u.ex z).left (((L.pull m).div L₀).U ((fun _ => i), b) ⊓
        ((L.pull m).div L₀).U ((fun _ => i), b'))
        (((L.pull m).div L₀).g ((fun _ => i), b) ((fun _ => i), b')).val =
        valAt' (u.ex z).left ((L.pull m).U (fun _ => i) ⊓ (L.pull m).U (fun _ => i))
          ((L.pull m).g (fun _ => i) (fun _ => i)).val *
        (valAt' (u.ex z).left (L₀.U b ⊓ L₀.U b') (L₀.g b b').val)⁻¹ :=
      PowUnif.val_div_g (L.pull m) L₀ (u.ex z).left (fun _ => i) (fun _ => i) b b' hbb
    have h3 : valAt' (u.ex z).left ((L.pull m).U (fun _ => i) ⊓ (L.pull m).U (fun _ => i))
        ((L.pull m).g (fun _ => i) (fun _ => i)).val = 1 := by
      rw [hM i i z hi hi]
      exact PowUnif.val_g_self hL ((u.ex z).left ≫ m) i hi
    have hbb' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L₀.U b ⊓ L₀.U b') := (top_le_preimage_inf_iff _ _ _).2 ⟨hb, hb'⟩
    have h4 := u.fr_compat b b' z hbb'
    have n4 := valAt'_units_val_ne_zero (u.ex z).left hbb' (L₀.g b b')
    rw [h1, h2, h3, h4]
    field_simp

  have ch : ∀ z : Fin g → ℂ, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L₀.U (Classical.choose (PowUnif.exists_chart hL₀ (u.ex z).left)) :=
    fun z => Classical.choose_spec (PowUnif.exists_chart hL₀ (u.ex z).left)
  have hdom : ∀ (i : L.ι) (z : Fin g → ℂ), z ∈ dom u m (L.U i) ↔ ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ L.U i :=
    fun _ _ => Iff.rfl
  refine ⟨fun i z => valAt' (u.ex z).left (((L.pull m).div L₀).U ((fun _ => i),
      Classical.choose (PowUnif.exists_chart hL₀ (u.ex z).left)))
      (w.s ((fun _ => i), Classical.choose (PowUnif.exists_chart hL₀ (u.ex z).left))).val *
      u.fr (Classical.choose (PowUnif.exists_chart hL₀ (u.ex z).left)) z, ?_, ?_, ?_⟩
  · intro i
    refine ⟨?_, ?_⟩
    · intro z₀ hz₀
      obtain ⟨b₀, hb₀⟩ := PowUnif.exists_chart hL₀ (u.ex z₀).left
      have hO := (u.hol (((L.pull m).div L₀).U ((fun _ => i), b₀)) (w.s ((fun _ => i), b₀)).val)
      have hz : z₀ ∈ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (((L.pull m).div L₀).U ((fun _ => i), b₀))} :=
        (top_le_preimage_inf_iff _ _ _).2 ⟨hJ i z₀ hz₀, hb₀⟩
      have hsub : {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (((L.pull m).div L₀).U ((fun _ => i), b₀))} ⊆
          {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L₀.U b₀} := fun z hz => ((top_le_preimage_inf_iff _ _ _).1 hz).2
      have hd : DifferentiableAt ℂ (fun z => valAt' (u.ex z).left (((L.pull m).div L₀).U ((fun _ => i), b₀))
          (w.s ((fun _ => i), b₀)).val * u.fr b₀ z) z₀ :=
        (hO.2.mul ((u.fr_hol b₀).mono hsub)).differentiableAt (hO.1.mem_nhds hz)
      refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [hO.1.mem_nhds hz] with z hz'
      have hz1 := (top_le_preimage_inf_iff _ _ _).1 hz'
      have hi : ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ L.U i :=
        (PowUnif.le_wchart_iff (u.ex z).left L (fun _ : PUnit => m) (fun _ => i)).1 hz1.1 PUnit.unit
      exact indep i z _ _ hi (ch z) hz1.2
    · intro z hz
      have hzz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (((L.pull m).div L₀).U ((fun _ => i),
          Classical.choose (PowUnif.exists_chart hL₀ (u.ex z).left))) :=
        (top_le_preimage_inf_iff _ _ _).2 ⟨hJ i z hz, ch z⟩
      exact mul_ne_zero (valAt'_units_val_ne_zero _ hzz _) (u.fr_ne _ z (ch z))
  · intro i j z hz
    dsimp only
    obtain ⟨hzi, hzj⟩ := hz
    have hzi' : ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ L.U i := hzi
    have hzj' : ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ L.U j := hzj
    set b := Classical.choose (PowUnif.exists_chart hL₀ (u.ex z).left) with hbdef
    have hbb : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (((L.pull m).div L₀).U ((fun _ => i), b) ⊓
        ((L.pull m).div L₀).U ((fun _ => j), b)) :=
      (top_le_preimage_inf_iff _ _ _).2 ⟨(top_le_preimage_inf_iff _ _ _).2 ⟨hJ i z hzi', ch z⟩, (top_le_preimage_inf_iff _ _ _).2 ⟨hJ j z hzj', ch z⟩⟩
    have h1 := PowUnif.val_gen hw (u.ex z).left ((fun _ => i), b) ((fun _ => j), b) hbb
    have h2 : valAt' (u.ex z).left (((L.pull m).div L₀).U ((fun _ => i), b) ⊓
        ((L.pull m).div L₀).U ((fun _ => j), b))
        (((L.pull m).div L₀).g ((fun _ => i), b) ((fun _ => j), b)).val =
        valAt' (u.ex z).left ((L.pull m).U (fun _ => i) ⊓ (L.pull m).U (fun _ => j))
          ((L.pull m).g (fun _ => i) (fun _ => j)).val *
        (valAt' (u.ex z).left (L₀.U b ⊓ L₀.U b) (L₀.g b b).val)⁻¹ :=
      PowUnif.val_div_g (L.pull m) L₀ (u.ex z).left (fun _ => i) (fun _ => j) b b hbb
    rw [h1, h2, hM i j z hzi' hzj', PowUnif.val_g_self hL₀ (u.ex z).left b (ch z), inv_one, _root_.mul_one]
    ring
  · intro i l z c hz hper
    have hx : (u.ex (z + l)).left = (u.ex z).left := by rw [ex_add_lattice]
    have hz' : ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ L.U i := hz
    have hzl : ⊤ ≤ ((u.ex (z + l)).left ≫ m) ⁻¹ᵁ L.U i := by rw [hx]; exact hz'
    have e1 := indep i (z + l) (Classical.choose (PowUnif.exists_chart hL₀ (u.ex (z + l)).left))
      (Classical.choose (PowUnif.exists_chart hL₀ (u.ex z).left)) hzl (ch (z + l)) (by rw [hx]; exact ch z)
    dsimp only
    rw [e1, hper _ (ch z), hx]
    ring

private theorem valAt'_mul_of_whole_le_preimage {X : Scheme.{0}} (y : Sp ℂ ⟶ X) {W : X.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W)
    (f f' : Γ(X, W)) : valAt' y W (f * f') = valAt' y W f * valAt' y W f' := by
  unfold valAt'
  simp only [dif_pos hW]
  unfold valAt
  simp only [map_mul]

private theorem valAt'_one_of_whole_le_preimage {X : Scheme.{0}} (y : Sp ℂ ⟶ X) {W : X.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W) :
    valAt' y W 1 = 1 := by
  unfold valAt'
  simp only [dif_pos hW]
  unfold valAt
  simp only [map_one]

private theorem valAt'_unit_ne_zero' {X : Scheme.{0}} (y : Sp ℂ ⟶ X) {W : X.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W)
    (f : (Γ(X, W))ˣ) : valAt' y W f.val ≠ 0 := by
  intro h0
  have h1 := valAt'_mul_of_whole_le_preimage y hW f.val f.inv
  rw [f.val_inv, valAt'_one_of_whole_le_preimage y hW, h0, zero_mul] at h1
  exact one_ne_zero h1

theorem PtDer.log_cocycle {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (h : PtDer y δ) {L : LB X} (hL : L.IsLB)
    (i j k : L.ι) (hi : ⊤ ≤ y ⁻¹ᵁ L.U i) (hj : ⊤ ≤ y ⁻¹ᵁ L.U j) (hk : ⊤ ≤ y ⁻¹ᵁ L.U k) :
    δ _ (L.g i j).val / valAt' y _ (L.g i j).val + δ _ (L.g j k).val / valAt' y _ (L.g j k).val =
      δ _ (L.g i k).val / valAt' y _ (L.g i k).val := by
  have hT : ⊤ ≤ y ⁻¹ᵁ (L.U i ⊓ L.U j ⊓ L.U k) := le_inf (le_inf hi hj) hk
  have hc := congrArg Units.val (hL.cocycle i j k)
  rw [Units.val_mul] at hc
  have hv := congrArg (valAt' y _) hc
  have hd := congrArg (δ _) hc
  rw [valAt'_mul_of_whole_le_preimage y hT, PowUnif.val_res y _ _ hT, PowUnif.val_res y _ _ hT,
    PowUnif.val_res y _ _ hT] at hv
  rw [h.mul _ hT, PowUnif.val_res y _ _ hT, PowUnif.val_res y _ _ hT] at hd
  have hd1 : ∀ (a b : L.ι) (hab : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U a ⊓ L.U b),
      δ _ (Semi.res hab (L.g a b)).val = δ (L.U a ⊓ L.U b) (L.g a b).val := fun a b hab =>
    h.res _ _ hab hT _
  rw [hd1, hd1, hd1] at hd
  have na : valAt' y (L.U i ⊓ L.U j) (L.g i j).val ≠ 0 := valAt'_unit_ne_zero' y (W := L.U i ⊓ L.U j) (le_inf hi hj) _
  have nb : valAt' y (L.U j ⊓ L.U k) (L.g j k).val ≠ 0 := valAt'_unit_ne_zero' y (W := L.U j ⊓ L.U k) (le_inf hj hk) _
  rw [← hv, ← hd]
  field_simp
  ring

private theorem top_le_preimage_inf_iff_and {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (A B : X.Opens) :
    ⊤ ≤ x ⁻¹ᵁ (A ⊓ B) ↔ ⊤ ≤ x ⁻¹ᵁ A ∧ ⊤ ≤ x ⁻¹ᵁ B := top_le_preimage_inf_iff x A B

private theorem valAt'_val_unit_ne_zero {X : Scheme.{0}} (y : Sp ℂ ⟶ X) {W : X.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W)
    (f : (Γ(X, W))ˣ) : valAt' y W f.val ≠ 0 := by
  apply valAt'_units_val_ne_zero (y := y) (hW := hW) (f := f) <;> assumption

theorem isSymm_of_lift : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D Θ s, KSRel u p m D Θ s → ∀ L : LB X, L.IsLB → LBIso P₀.L (L.pull m) → IsSymm Hm Θ := by
  intro P₀ u Hm χ hG R _ x₀ X p m hp hpb D Θ s hks L hL hw
  obtain ⟨a, ha1, ha2, ha3⟩ := exists_frame_on_family u P₀.isLB m L hL hw
  have hhol := isHolFamily_ex_comp u m
  have hopen : ∀ W : X.Opens, IsOpen (dom u m W) := fun W => (hhol W 0).1
  have hfn : ∀ (W : X.Opens) (f : Γ(X, W)), DifferentiableOn ℂ (fn u m W f) (dom u m W) :=
    fun W f => (hhol W f).2
  have hdom : ∀ A B : X.Opens, dom u m (A ⊓ B) = dom u m A ∩ dom u m B := by
    intro A B
    ext z
    exact top_le_preimage_inf_iff_and _ _ _
  have hfnper : ∀ (W : X.Opens) (f : Γ(X, W)) (z : Fin P₀.g → ℂ) (l : u.Λ),
      fn u m W f (z + l) = fn u m W f z := by
    intro W f z l
    unfold fn
    rw [ex_add_lattice]
  have key := _root_.GlobalTheory.T.theta_cocycle_periodic_nonvanishing_sections P₀.g u.Λ u.discrete u.full Hm Θ L.ι (fun i => dom u m (L.U i)) a
    (fun i j z => s z (L.U i ⊓ L.U j) (L.g i j).val / fn u m (L.U i ⊓ L.U j) (L.g i j).val z)
    (fun l => χ l * Complex.exp (↑Real.pi / 2 * ((l : Fin P₀.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P₀.g → ℂ)))))
    (fun i => hopen _)
    (by
      intro i l z hz
      show ⊤ ≤ ((u.ex (z + l)).left ≫ m) ⁻¹ᵁ L.U i
      rw [ex_add_lattice]
      exact hz)
    (fun z => PowUnif.exists_chart hL ((u.ex z).left ≫ m))
    ha1
    (by
      intro i l z hz
      refine ha3 i l z _ hz fun b hb => ?_
      rw [hG.ah.2.2.2 l b z hb, Complex.exp_add]
      ring)
    (by
      intro i j
      rw [← hdom]
      have h1 : DifferentiableOn ℂ (fun z => s z (L.U i ⊓ L.U j) (L.g i j).val) (dom u m (L.U i ⊓ L.U j)) :=
        hks.hol _ _
      have h2 : DifferentiableOn ℂ (fn u m (L.U i ⊓ L.U j) (L.g i j).val) (dom u m (L.U i ⊓ L.U j)) := hfn _ _
      have h3 : ∀ z ∈ dom u m (L.U i ⊓ L.U j), fn u m (L.U i ⊓ L.U j) (L.g i j).val z ≠ 0 :=
        fun z hz => valAt'_val_unit_ne_zero _ hz _
      refine (h1.mul (h2.inv h3)).congr fun z _ => ?_
      exact div_eq_mul_inv _ _)
    (by
      intro i j k z hz
      obtain ⟨⟨hi, hj⟩, hk⟩ := hz
      exact PtDer.log_cocycle (hks.der z) hL i j k hi hj hk)
    (by
      intro i j l z hz
      have hzW : z ∈ dom u m (L.U i ⊓ L.U j) := by
        rw [hdom]
        exact hz
      have hs := hks.per l (L.U i ⊓ L.U j) (L.g i j).val z hzW
      show s (z + l) (L.U i ⊓ L.U j) (L.g i j).val / fn u m (L.U i ⊓ L.U j) (L.g i j).val (z + l) = _
      rw [hs, hfnper]
      have hdf : DifferentiableAt ℂ (fn u m (L.U i ⊓ L.U j) (L.g i j).val) z :=
        (hfn _ _).differentiableAt ((hopen _).mem_nhds hzW)
      have hda : DifferentiableAt ℂ (a j) z := (ha1 j).1.differentiableAt ((hopen _).mem_nhds hz.2)
      have hEq : fderiv ℂ (a i) z = fderiv ℂ (fun y => fn u m (L.U i ⊓ L.U j) (L.g i j).val y * a j y) z := by
        apply Filter.EventuallyEq.fderiv_eq
        filter_upwards [(hopen _).mem_nhds hzW] with y hy
        rw [hdom] at hy
        exact ha2 i j y hy
      have nf : fn u m (L.U i ⊓ L.U j) (L.g i j).val z ≠ 0 := valAt'_val_unit_ne_zero _ hzW _
      have na : a j z ≠ 0 := (ha1 j).2 z hz.2
      rw [hEq, fderiv_fun_mul hdf hda, ha2 i j z hz]
      simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring)
  intro z w
  unfold hermForm
  exact key z w

end GlobalTheory.KS
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencer_class_isSymm_of_lift : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D Θ s, KSRel u p m D Θ s → ∀ L : LB X, L.IsLB → LBIso P₀.L (L.pull m) → IsSymm Hm Θ := by
  atlas_forward_decl GlobalTheory.KS.isSymm_of_lift
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM GlobalTheory.KS

namespace GlobalTheory.KS

theorem tangent_injects_symm_antilinear : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (R : Type) [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (t : TObj g k J b (spMap (algebraMap o R))), (∀ (x : Sp (DualNumber ℂ) ⟶ Sp R) (t' : TObj g k J b (x ≫ spMap (algebraMap o R))), x ≫ spMap (algebraMap o R) = constPt x ≫ spMap (algebraMap o R) → TMap t' t x → TMap t' t (constPt x) → x = constPt x) → ∃ (t₀ : TObj g k J b (spMap (algebraMap o ℂ))) (m : t₀.A.left ⟶ t.A.left) (u : HolUnif t₀.pol.A t₀.pol.L t₀.pol.g) (Hm : Matrix (Fin t₀.pol.g) (Fin t₀.pol.g) ℂ) (χ : u.Λ → ℂ) (κ : Derivation o R ℂ →ₗ[ℂ] Matrix (Fin t₀.pol.g) (Fin t₀.pol.g) ℂ), GoodU u Hm χ ∧ (IsGrpPullback t₀.A t.A (spMap (algebraMap R ℂ)) m ∧ LBIso t₀.L (t.L.pull m) ∧ (∀ i, (t₀.pt i).left ≫ m = (spMap (algebraMap R ℂ)) ≫ (t.pt i).left) ∧ ∀ jj, (t₀.act jj).left ≫ m = m ≫ (t.act jj).left) ∧ Function.Injective κ ∧ ∀ D, IsSymm Hm (κ D) ∧ ∀ (f : t.A ⟶ t.A) (f₀ : t₀.pol.A ⟶ t₀.pol.A) (F : (Fin t₀.pol.g → ℂ) →ₗ[ℂ] (Fin t₀.pol.g → ℂ)), f₀.left ≫ m = m ≫ f.left → (∀ z, u.ex (F z) = u.ex z ≫ f₀) → Comm (κ D) F := by
  intro h1 h2 hU o _ g k J b R _ _ _ _ _ t hun
  have hcomp : spMap (algebraMap R ℂ) ≫ spMap (algebraMap o R) = spMap (algebraMap o ℂ) := by
    rw [IsScalarTower.algebraMap_eq o R ℂ]
    exact (Spec.map_comp (CommRingCat.ofHom (algebraMap o R)) (CommRingCat.ofHom (algebraMap R ℂ))).symm
  obtain ⟨t₀, m, hm⟩ := GlobalTheory.T.exists_thetaLevelAbelianScheme_pullback o g k J b _ _ _ _ (spMap (algebraMap R ℂ)) t hcomp
  obtain ⟨u, Hm, χ, hG, -⟩ := GlobalTheory.T.exists_goodUniformisation_kodairaSpencer hU t₀.pol
  have hsm : Smooth t.A.hom := by
    haveI := t.dim
    exact SmoothOfRelativeDimension.smooth g _
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.kodairaSpencer_matrix_linear_in_derivation t₀.pol u Hm χ hG o R t.A.left t.A.hom m hsm hm.1.1
  refine ⟨t₀, m, u, Hm, χ, κ, hG, hm, ?_, fun D => ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro D hD
    obtain ⟨s, hs⟩ := hκ D
    rw [hD] at hs
    exact GlobalTheory.T.derivation_eq_zero_of_kodairaSpencer_zero h1 h2 hU o g k J b R t _ t₀ m u Hm χ hG hm hun D s hs
  · obtain ⟨s, hs⟩ := hκ D
    refine ⟨GlobalTheory.T.kodairaSpencer_class_isSymm_of_lift t₀.pol u Hm χ hG R _ t.A.left t.A.hom m hsm hm.1.1 _ _ s hs t.L t.isLB hm.2.1, ?_⟩
    intro f f₀ F hf hF
    exact GlobalTheory.T.kodairaSpencer_commutes_with_endomorphism t₀.pol u Hm χ hG R _ t.A.left t.A.hom m hsm hm.1.1 _ _ s hs f.left f₀ F (Over.w f) hf hF

end GlobalTheory.KS
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_injects_symmetric_antilinear_commuting : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (R : Type) [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (t : TObj g k J b (spMap (algebraMap o R))), (∀ (x : Sp (DualNumber ℂ) ⟶ Sp R) (t' : TObj g k J b (x ≫ spMap (algebraMap o R))), x ≫ spMap (algebraMap o R) = constPt x ≫ spMap (algebraMap o R) → TMap t' t x → TMap t' t (constPt x) → x = constPt x) → ∃ (t₀ : TObj g k J b (spMap (algebraMap o ℂ))) (m : t₀.A.left ⟶ t.A.left) (u : HolUnif t₀.pol.A t₀.pol.L t₀.pol.g) (Hm : Matrix (Fin t₀.pol.g) (Fin t₀.pol.g) ℂ) (χ : u.Λ → ℂ) (κ : Derivation o R ℂ →ₗ[ℂ] Matrix (Fin t₀.pol.g) (Fin t₀.pol.g) ℂ), GoodU u Hm χ ∧ (IsGrpPullback t₀.A t.A (spMap (algebraMap R ℂ)) m ∧ LBIso t₀.L (t.L.pull m) ∧ (∀ i, (t₀.pt i).left ≫ m = (spMap (algebraMap R ℂ)) ≫ (t.pt i).left) ∧ ∀ jj, (t₀.act jj).left ≫ m = m ≫ (t.act jj).left) ∧ Function.Injective κ ∧ ∀ D, IsSymm Hm (κ D) ∧ ∀ (f : t.A ⟶ t.A) (f₀ : t₀.pol.A ⟶ t₀.pol.A) (F : (Fin t₀.pol.g → ℂ) →ₗ[ℂ] (Fin t₀.pol.g → ℂ)), f₀.left ≫ m = m ≫ f.left → (∀ z, u.ex (F z) = u.ex z ≫ f₀) → Comm (κ D) F := by
  atlas_forward_decl GlobalTheory.KS.tangent_injects_symm_antilinear
end
