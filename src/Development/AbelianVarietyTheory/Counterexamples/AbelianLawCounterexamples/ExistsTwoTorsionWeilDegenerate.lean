import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsOfCubeBundleGenerator
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTheoremAndSectionsFiniteGrowthAbelianVariety
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PairingLawZeroCounterexample

open GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

theorem laws : WeilSt ∧ WeilNondegSt ∧ CharPairSt :=
  have h := GlobalTheory.AbLaw.FromCube.all_of_cubeGen GlobalTheory.AbLaw.CubeAssembly.cube_and_sections.1
  ⟨h.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩

theorem lifts : ∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A), x ^ N = 1 →
    ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θ : ThetaGrp P.A P.L N (overRes V), θ.pt = overResι V ≫ x :=
  (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube GlobalTheory.AbLaw.CubeAssembly.cube_and_sections.1).1).2.2

theorem skew {S : Scheme.{0}} (P : PolAV S) (k : ℕ) {T : Over S} {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ}
    (h : WeilIs P.A P.L k x y c) : WeilIs P.A P.L k y x c⁻¹ :=
  (GlobalTheory.weilIs_alternating_skew_natural GlobalTheory.laws_without_cohomology.1 lifts S P k T).2.1 x y c h

theorem mul_right {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ) {T : Over S}
    {x y y' : T ⟶ P.A} {c c' : Γ(T.left, ⊤)ˣ}
    (h : WeilIs P.A P.L k x y c) (h' : WeilIs P.A P.L k x y' c') :
    WeilIs P.A P.L k x (y * y') (c * c') := by
  have := skew P k ((laws.1 S P k T).2.1 _ _ _ _ _ (skew P k h) (skew P k h'))
  rwa [← mul_inv, inv_inv] at this

def zeroLift {S : Scheme.{0}} (P : PolAV S) {T : Over S} (x : T ⟶ P.A) : ThetaGrp P.A P.L ((0 : ℕ) : ℤ) T where
  pt := x
  φ := ⟨fun _ => 1⟩
  isGen := by
    intro i j
    have h : (thetaLB P.A P.L ((0 : ℕ) : ℤ) x).g i j = 1 := by
      unfold thetaLB LB.LinComb
      dsimp only
      refine (Fin.prod_univ_two _).trans ?_
      exact (congrArg₂ (· * ·) (zpow_zero _) (zpow_zero _)).trans (_root_.mul_one _)
    rw [h]
    exact (map_one _).trans ((_root_.one_mul _).trans (map_one _)).symm

theorem weilIs_zero {S : Scheme.{0}} (P : PolAV S) {T : Over S} (x y : T ⟶ P.A) :
    WeilIs P.A P.L ((0 : ℕ) : ℤ) x y 1 := by
  have g := GlobalTheory.laws_without_cohomology.1
  refine ((GlobalTheory.weilIs_iff_commIsOf_and_lift_subsingleton g lifts
    (GlobalTheory.symLift_odd g lifts (GlobalTheory.exists_gen_negLB g)).1 S P 0 T).1 (zeroLift P x) (zeroLift P y) 1).2 ?_
  intro j j' _ _ _
  have h : ∀ {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) {a : Γ(X, U)ˣ}, a = 1 → res h a = 1 :=
    fun h a e => e ▸ map_one _
  have m : ∀ {G : Type} [Monoid G] {a b : G}, a = 1 → b = 1 → a * b = 1 :=
    fun ha hb => by rw [ha, hb, _root_.mul_one]
  refine (h _ (m (h _ rfl) (h _ (h _ (map_one _))))).trans (h _ ?_).symm
  exact m (h _ (m (h _ rfl) (h _ (h _ (map_one _))))) (h _ (h _ (map_one _)))

def curve (K : Type) [Field K] : _root_.WeierstrassCurve K := ⟨1, 0, 0, 1, 0⟩

theorem isElliptic_curve (K : Type) [Field K] (h : (63 : K) ≠ 0) : (curve K).IsElliptic := ⟨by
  have : (curve K).Δ = -63 := by
    norm_num [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
  rw [this]
  exact Ne.isUnit (neg_ne_zero.2 h)⟩

theorem exists_order_two (K : Type) [Field K] (h : (63 : K) ≠ 0) :
    ∃ (P : PolAV (Spec (CommRingCat.of K))) (x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A),
      P.g = 1 ∧ x ≠ 1 ∧ x ^ 2 = 1 := by
  haveI := isElliptic_curve K h
  have sol : IsUnimodularSol ((curve K).baseChange K) ![0, 0, 1] :=
    isUnimodularSol_some (by
      rw [WeierstrassCurve.Affine.equation_iff]
      simp [curve])
  let p : specOver K K ⟶ (ellPolAV (curve K)).A := ptOver (curve K) _ sol
  have hinv : p⁻¹ = p := by
    refine (ptOver_inv (curve K) sol).trans
      (Over.OverMorphism.ext (pt_congr (curve K) _ sol.neg ?_ sol))
    simp [curve, WeierstrassCurve.Projective.neg, WeierstrassCurve.Projective.negY]
  have hsq : p ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [← hinv]
    exact inv_mul_cancel p
  have hne : p ≠ 1 := by
    intro e
    have e' : ptOver (curve K) _ sol = 1 := e
    rw [one_eq_ptOver] at e'
    obtain ⟨v, hv⟩ := (ptOver_eq_ptOver_iff (curve K) _ _).mp e'.symm
    simpa using congrFun hv 2
  have h1 : Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 _ := Spec.map_id _
  let e : baseOver (Spec (CommRingCat.of K)) ≅ specOver K K :=
    Over.isoMk (Iso.refl _) (by exact (Category.id_comp _).trans h1)
  refine ⟨ellPolAV (curve K), e.hom ≫ p, rfl, fun hx => hne ?_, ?_⟩
  · rw [← cancel_epi e.hom, hx, MonObj.comp_one]
  · rw [← MonObj.comp_pow, hsq, MonObj.comp_one]







end GlobalTheory.PairingLawZeroCounterexample
