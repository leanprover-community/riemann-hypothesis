import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexMetrics.Assembly
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.Statements
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveSpaceChart
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.IntegralMonoInnerEqZero

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace GroundTheory.Arith.SchemeCoh

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace SectionsLatticeFS

open ProjScheme

variable {A : Type u} [CommRing A] {N : ℕ}

lemma X_pow_mem_grading (j : Fin (N + 1)) (n : ℕ) :
    (MvPolynomial.X j ^ n : MvPolynomial (Fin (N + 1)) A) ∈ ProjSpace.grading A N n := by
  simpa using SetLike.pow_mem_graded n (ProjSpace.X_mem (A := A) (n := N) j)

def fracOn {n : ℕ} {P : MvPolynomial (Fin (N + 1)) A} (hP : P ∈ ProjSpace.grading A N n)
    (j : Fin (N + 1)) : ringOn (self A N).X (ProjSpace.stdOpen A N j) :=
  (Proj.awayToSection (ProjSpace.grading A N) (MvPolynomial.X j)).hom
    (HomogeneousLocalization.mk ⟨n, ⟨P, hP⟩, ⟨MvPolynomial.X j ^ n, X_pow_mem_grading j n⟩, ⟨n, rfl⟩⟩)

lemma resM_polySection {n : ℕ} {P : MvPolynomial (Fin (N + 1)) A} (hP : P ∈ ProjSpace.grading A N n)
    (j : Fin (N + 1)) :
    resM ((preMod (self A N).X).obj (twistN A N n)) le_top
        (polySection hP : ((preMod (self A N).X).obj (twistN A N n)).obj (op ⊤)) =
      fracOn hP j • stdFrame A j n := by
  apply ProjTwist.ext (k := (n : ℤ)) (U := ProjSpace.stdOpen A N j)
  funext x
  change Localization.mk P 1 = ((fracOn hP j).1 x).val *
    ProjTwist.val (k := (n : ℤ)) (U := Proj.basicOpen (ProjSpace.grading A N) (MvPolynomial.X j))
      (ProjTwist.upow (ProjSpace.grading A N) (ProjSpace.X_mem j) (n : ℤ)) x
  erw [ProjTwist.val_upow]
  change Localization.mk P 1 = (HomogeneousLocalization.mk _).val * _
  rw [HomogeneousLocalization.val_mk]
  unfold ProjTwist.twistFrac
  rw [Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul, Int.toNat_natCast]
  simp
  ring

lemma evalAtPoint_fracOn {ρ : A →+* ℂ} (x : (self A N).complexPoints ρ) {j : Fin (N + 1)}
    (hp : (self A N).point x ∈ ProjSpace.stdOpen A N j) {n : ℕ} {P : MvPolynomial (Fin (N + 1)) A}
    (hP : P ∈ ProjSpace.grading A N n) :
    (self A N).evalAtPoint x (germR (X := (self A N).X) hp (fracOn hP j)) = evalAt ρ x.1.rep P / x.1.rep j ^ n := by
  have e := Scheme.Hom.germ_stalkMap_apply (self A N).ι (ProjSpace.stdOpen A N j) ((self A N).point x)
    hp (fracOn hP j)
  have e2 : germR (X := (self A N).X) hp (fracOn hP j) = ((self A N).ι.stalkMap ((self A N).point x)).hom
      ((projectiveSpace A N).presheaf.germ (ProjSpace.stdOpen A N j)
        ((self A N).ι.base ((self A N).point x)) hp (fracOn hP j)) := by
    rw [e]
    rfl
  rw [e2]
  change (self A N).evalStalk ((self A N).isOver_point x) _ = _
  rw [evalStalk_stalkMap]
  unfold evalStalkProj
  rw [RingHom.comp_apply]
  have e1 : (Proj.stalkIso (ProjSpace.grading A N) _).hom.hom
      ((projectiveSpace A N).presheaf.germ (ProjSpace.stdOpen A N j)
        ((self A N).ι.base ((self A N).point x)) hp (fracOn hP j)) = (fracOn hP j).1 ⟨_, hp⟩ :=
    Proj.stalkIso'_germ _ _ _ hp _
  rw [e1]
  refine (evalAtPrime_mk _ _).trans ?_
  simp [evalAt]

lemma fibreEquivComplex_fibreMk {X : Scheme.{u}} {L : X.Modules} {p : X} {φ : locRing X p →+* ℂ}
    {U : X.Opens} (hp : p ∈ U) {e : ((preMod X).obj L).obj (op U)}
    (he : IsBasisOn ((preMod X).obj L) U e) (r : locRing X p) :
    fibreEquivComplex φ hp he (fibreMk L φ 1 (r • germM hp e)) = φ r := by
  have h := fibreEquiv_fibreMk (φ := φ) hp he 1 r
  rw [mul_one] at h
  exact (congrArg (Via.ofComplex φ).symm h).trans (RingEquiv.symm_apply_apply _ _)

theorem FSCoord.proof : FSCoord.Statement.{u} := by
  intro A _ N n ρ P hP x j hj
  have hp := point_mem_stdOpen x hj
  have hg := (germM_resM (X := (self A N).X) (le_top : ProjSpace.stdOpen A N j ≤ ⊤) hp
      (polySection hP : ((preMod (self A N).X).obj (twistN A N n)).obj (op ⊤))).symm.trans
    ((congrArg (germM (X := (self A N).X) hp) (resM_polySection hP j)).trans (germM_smul hp _ _))
  have hv : (self A N).evalGlobalSection (twistN A N n) x (polySection hP) =
      fibreMk _ ((self A N).evalAtPoint x) 1
        (germR (X := (self A N).X) hp (fracOn hP j) • germM (X := (self A N).X) hp (stdFrame A j n)) :=
    congrArg (fibreMk _ ((self A N).evalAtPoint x) 1) hg
  have key := (congrArg (fibreEquivComplex ((self A N).evalAtPoint x) hp
      (isBasisOn_frame (A := A) j n)) hv).trans
    ((fibreEquivComplex_fibreMk hp (isBasisOn_frame (A := A) j n) _).trans (evalAtPoint_fracOn x hp hP))
  exact (congrArg (· * x.1.rep j ^ n) key).trans (div_mul_cancel₀ _ (pow_ne_zero _ hj))

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace NumberField GroundTheory.Arith.SchemeCoh

universe u

noncomputable section

namespace SectionsLatticeFS

open ProjScheme

theorem FSIndex.proof (h : FSCoord.Statement.{u}) : FSIndex.Statement.{u} := by
  intro A _ N n ρ x j hj s
  set k := CP.chartIndex x.1
  have hk : x.1.rep k ≠ 0 := rep_chartIndex_ne_zero x.1
  have hP : (MvPolynomial.X k : MvPolynomial (Fin (N + 1)) A) ^ n ∈ ProjSpace.grading A N n :=
    (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X_pow k n)
  set w := (self A N).evalGlobalSection (twistN A N n) x (polySection hP)
  set ek := fsFrameCoord n ρ x
  set ej := fibreEquivComplex ((self A N).evalAtPoint x) (point_mem_stdOpen x hj)
    (isBasisOn_frame (A := A) j n)
  have hev : evalAt ρ x.1.rep ((MvPolynomial.X k : MvPolynomial (Fin (N + 1)) A) ^ n) =
      x.1.rep k ^ n := by simp [evalAt]
  have hwk : ek w = 1 := by
    have h1 := h A N n ρ _ hP x k hk
    rw [hev] at h1
    exact mul_right_cancel₀ (pow_ne_zero n hk) (h1.trans (one_mul _).symm)
  have hwj : ej w * x.1.rep j ^ n = x.1.rep k ^ n := by
    have h1 := h A N n ρ _ hP x j hj
    rwa [hev] at h1

  have hs : s = ek s • w := by
    apply ek.injective
    rw [LinearEquiv.map_smul, hwk, smul_eq_mul, mul_one]
  have hnj : ‖ej w‖ * ‖x.1.rep j‖ ^ n = ‖x.1.rep k‖ ^ n := by
    rw [← norm_pow, ← norm_pow, ← norm_mul, hwj]
  have hfs : fsFibreNorm n ρ x s = ‖ek s‖ * ‖x.1.rep k‖ ^ n / norm2 x.1.rep ^ n := rfl
  rw [hfs]
  conv_rhs => rw [hs, LinearEquiv.map_smul, smul_eq_mul, norm_mul, mul_assoc, hnj]

example (h : FSCoord.Statement.{0}) (s : (self (𝓞 ℚ) 1).Fibre (twistN (𝓞 ℚ) 1 1) pointQ) :
    fsFibreNorm 1 _ pointQ s =
      ‖fibreEquivComplex ((self (𝓞 ℚ) 1).evalAtPoint pointQ) (point_mem_stdOpen pointQ pointQ_rep_ne_zero)
          (isBasisOn_frame (A := 𝓞 ℚ) 0 1) s‖ * ‖pointQ.1.rep 0‖ ^ 1 / norm2 pointQ.1.rep ^ 1 :=
  FSIndex.proof h _ _ _ _ _ _ pointQ_rep_ne_zero _

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

noncomputable section

namespace SectionsLatticeFS

open ProjScheme

theorem FSValue.proof (h : FSCoord.Statement.{u}) : FSValue.Statement.{u} := by
  intro A _ N n ρ P hP x
  have hj := rep_chartIndex_ne_zero x.1
  have hc := h A N n ρ P hP x (CP.chartIndex x.1) hj
  have hcoord : fsFrameCoord n ρ x ((self A N).evalGlobalSection (twistN A N n) x (polySection hP)) =
      evalAt ρ x.1.rep P / x.1.rep (CP.chartIndex x.1) ^ n :=
    eq_div_of_mul_eq (pow_ne_zero _ hj) hc
  have hpos : 0 < ‖x.1.rep (CP.chartIndex x.1)‖ ^ n := pow_pos (norm_pos_iff.mpr hj) n
  rw [fsFibreNorm, hcoord, CP.fsNormPoly, MvPolynomial.eval_map, norm_div, norm_pow,
    div_mul_cancel₀ _ hpos.ne']

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TensorProduct GroundTheory.Arith.SchemeCoh

universe u

noncomputable section

namespace SectionsLatticeFS

open ProjScheme

lemma rep_ne_zero_of_mem_chartDomain {N : ℕ} {j : Fin (N + 1)} {v : CP N}
    (hv : v ∈ CP.chartDomain j) : v.rep j ≠ 0 := by
  have h := CP.mk_mem_chartDomain j v.rep v.rep_nonzero
  rw [Projectivization.mk_rep] at h
  exact h.mp hv

lemma norm_rep_pow_div {N : ℕ} (n : ℕ) (j : Fin (N + 1)) (v : CP N) :
    ‖v.rep j‖ ^ n / norm2 v.rep ^ n =
      CP.fsNormPoly n ((MvPolynomial.X j : MvPolynomial (Fin (N + 1)) ℂ) ^ n) v := by
  simp [CP.fsNormPoly, norm_pow]

theorem continuousOn_chart (h₁ : FSIndex.Statement.{u}) (h₂ : ComplexMetric.RegularContinuous.Statement.{u})
    {A : Type u} [CommRing A] {N n : ℕ} (ρ : A →+* ℂ) {U : (self A N).X.Opens}
    (e : ((preMod (self A N).X).obj (twistN A N n)).obj (op U)) (j : Fin (N + 1)) :
    ContinuousOn (fun y : {x : (self A N).complexPoints ρ // (self A N).point x ∈ U} =>
        fsFibreNorm n ρ y.1 ((self A N).sectionValue y.1 y.2 e))
      {y | y.1.1 ∈ CP.chartDomain j} := by
  let V : (self A N).X.Opens := U ⊓ ProjSpace.stdOpen A N j
  have hVU : V ≤ U := inf_le_left
  have hVj : V ≤ ProjSpace.stdOpen A N j := inf_le_right

  obtain ⟨f, hf⟩ := (isBasisOn_frame (A := A) j n V hVj).2 (resM _ hVU e)
  have hV : ∀ y : {y : {x : (self A N).complexPoints ρ // (self A N).point x ∈ U} //
      y.1.1 ∈ CP.chartDomain j}, (self A N).point y.1.1 ∈ V := fun y =>
    ⟨y.1.2, point_mem_stdOpen y.1.1 (rep_ne_zero_of_mem_chartDomain y.2)⟩
  let ι := fun y : {y : {x : (self A N).complexPoints ρ // (self A N).point x ∈ U} //
      y.1.1 ∈ CP.chartDomain j} => (⟨y.1.1, hV y⟩ : {x : (self A N).complexPoints ρ // (self A N).point x ∈ V})
  have hι : Continuous ι :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

  have hval : ∀ y : {y : {x : (self A N).complexPoints ρ // (self A N).point x ∈ U} //
      y.1.1 ∈ CP.chartDomain j},
      fsFibreNorm n ρ y.1.1 ((self A N).sectionValue y.1.1 y.1.2 e) =
        ‖(self A N).evalAtPoint y.1.1 (germR (hV y) f)‖ *
          CP.fsNormPoly n ((MvPolynomial.X j : MvPolynomial (Fin (N + 1)) ℂ) ^ n) y.1.1.1 := by
    intro y
    have hyj := rep_ne_zero_of_mem_chartDomain y.2
    have hp := point_mem_stdOpen y.1.1 hyj
    rw [h₁ A N n ρ y.1.1 j hyj, mul_div_assoc, norm_rep_pow_div]
    congr 2
    change (Via.ofComplex ((self A N).evalAtPoint y.1.1)).symm
      (fibreEquiv (X := (self A N).X) (L := twistN A N n) ((self A N).evalAtPoint y.1.1) hp
        (isBasisOn_frame (A := A) j n)
        (fibreMk (X := (self A N).X) (twistN A N n) ((self A N).evalAtPoint y.1.1) 1
          (germM (X := (self A N).X) (L := twistN A N n) y.1.2 e))) = _
    rw [← germM_resM hVU (hV y) e, ← hf, germM_smul, germM_resM hVj (hV y)]
    have key := fibreEquiv_fibreMk (φ := (self A N).evalAtPoint y.1.1) hp
      (isBasisOn_frame (A := A) j n) 1 (germR (hV y) f)
    rw [mul_one] at key
    exact (congrArg (Via.ofComplex ((self A N).evalAtPoint y.1.1)).symm key).trans
      (RingEquiv.symm_apply_apply _ _)
  rw [continuousOn_iff_continuous_domRestrict]
  have hc : Continuous fun y : {y : {x : (self A N).complexPoints ρ // (self A N).point x ∈ U} //
      y.1.1 ∈ CP.chartDomain j} =>
        ‖(self A N).evalAtPoint y.1.1 (germR (hV y) f)‖ *
          CP.fsNormPoly n ((MvPolynomial.X j : MvPolynomial (Fin (N + 1)) ℂ) ^ n) y.1.1.1 :=
    (continuous_norm.comp ((h₂ A N (self A N) ρ V f).comp hι)).mul
      ((CP.continuous_fsNormPoly (MvPolynomial.isHomogeneous_X_pow j n)).comp
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)))
  exact hc.congr fun y => (hval y).symm

theorem FSContinuousFrame.proof (h₁ : FSIndex.Statement.{u})
    (h₂ : ComplexMetric.RegularContinuous.Statement.{u}) : FSContinuousFrame.Statement.{u} := by
  intro A _ N n ρ U e _
  rw [continuous_iff_continuousAt]
  intro y₀
  let j := CP.chartIndex y₀.1.1
  have hW : IsOpen {y : {x : (self A N).complexPoints ρ // (self A N).point x ∈ U} |
      y.1.1 ∈ CP.chartDomain j} :=
    (CP.isOpen_chartDomain j).preimage
      (continuous_subtype_val.comp continuous_subtype_val :
        Continuous fun y : {x : (self A N).complexPoints ρ // (self A N).point x ∈ U} => y.1.1)
  exact (continuousOn_chart h₁ h₂ ρ e j).continuousAt
    (hW.mem_nhds (CP.mem_chartDomain_chartIndex y₀.1.1))

example (h₁ : FSIndex.Statement.{0}) (h₂ : ComplexMetric.RegularContinuous.Statement.{0}) :
    Continuous fun y : {x : (self (NumberField.RingOfIntegers ℚ) 1).complexPoints
        (intEmb (Rat.castHom ℂ)) // (self _ 1).point x ∈ ProjSpace.stdOpen _ 1 0} =>
      fsFibreNorm 1 _ y.1 ((self _ 1).sectionValue y.1 y.2 (stdFrame _ 0 1)) :=
  FSContinuousFrame.proof h₁ h₂ _ _ _ _ _ _ (isBasisOn_frame 0 1)

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace GroundTheory.Arith.SchemeCoh

universe u

noncomputable section

namespace SectionsLatticeFS

open ProjScheme

lemma fibreEquivComplex_value_eq {X : Scheme.{u}} {L : X.Modules} {p : X}
    (φ : locRing X p →+* ℂ) {U V : X.Opens} (hpU : p ∈ U) (hpV : p ∈ V)
    {e : ((preMod X).obj L).obj (op V)} (he : IsBasisOn ((preMod X).obj L) V e)
    (s : ((preMod X).obj L).obj (op U)) (r : locRing X p) (hr : germM hpU s = r • germM hpV e) :
    fibreEquivComplex φ hpV he (value φ hpU s) = φ r := by
  change (Via.ofComplex φ).symm (fibreEquiv φ hpV he (fibreMk L φ 1 (germM hpU s))) = φ r
  rw [hr, fibreEquiv_fibreMk, mul_one, RingEquiv.symm_apply_apply]

theorem FSNormConj.proof (h : FSIndex.Statement.{u}) : FSNormConj.Statement.{u} := by
  intro A _ N n ρ U s x hx hx'
  obtain ⟨j, hj⟩ : ∃ j, x.1.rep j ≠ 0 := ⟨_, rep_chartIndex_ne_zero x.1⟩
  obtain ⟨c, hc⟩ := exists_rep_conj x.1
  have hcj : (CP.conj x.1).rep j = (c : ℂ) * starRingEnd ℂ (x.1.rep j) := by
    rw [hc, Pi.smul_apply, smul_eq_mul, CP.conjVec_apply]
  have hj' : ((self A N).conjPoint ρ x).1.rep j ≠ 0 := by
    change (CP.conj x.1).rep j ≠ 0
    rw [hcj]
    exact mul_ne_zero c.ne_zero ((map_ne_zero _).mpr hj)
  have hpj := point_mem_stdOpen x hj
  obtain ⟨r, hr⟩ := (bijective_smul_germ hpj (isBasisOn_frame (A := A) j n)).2 (germM hx s)
  obtain ⟨V, -, hpV, f, rfl⟩ :=
    TopCat.Presheaf.exists_le_germ_eq (X := (self A N).X.toTopCat) (self A N).X.sheaf.obj r hx
  have key : ∀ (q : (self A N).X) (_ : q = (self A N).point x) (φ : locRing (self A N).X q →+* ℂ)
      (hqU : q ∈ U) (hqj : q ∈ ProjSpace.stdOpen A N j) (hqV : q ∈ V),
      fibreEquivComplex φ hqj (isBasisOn_frame (A := A) j n) (value φ hqU s) = φ (germR hqV f) := by
    intro q hq φ hqU hqj hqV
    subst hq
    exact fibreEquivComplex_value_eq φ hqU hqj _ s _ hr.symm
  have hV' : (self A N).point ((self A N).conjPoint ρ x) ∈ V := by
    rw [point_conjPoint]
    exact hpV
  have hj'' := point_mem_stdOpen _ hj'
  rw [h A N n _ _ j hj', h A N n ρ x j hj]
  unfold sectionValue
  rw [key _ (point_conjPoint _ x) _ hx' hj'' hV', key _ rfl _ hx hpj hpV,
    evalAtPoint_conjPoint_germ _ x hpV hV', Complex.norm_conj]
  have hn : norm2 (CP.conj x.1).rep = ‖(c : ℂ)‖ * norm2 x.1.rep := by
    rw [hc, euclideanNorm_smul]
    congr 1
    simp [norm2, normSq2, CP.conjVec_apply]
  have hc0 : 0 < ‖(c : ℂ)‖ := norm_pos_iff.mpr c.ne_zero
  change _ * ‖(CP.conj x.1).rep j‖ ^ n / norm2 (CP.conj x.1).rep ^ n = _
  rw [hn, hcj, norm_mul, Complex.norm_conj, mul_pow, mul_pow]
  field_simp

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory GroundTheory.Arith.SchemeCoh MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace SectionsLatticeFS

open ProjScheme

lemma chart_structureMap_eq (A : Type u) [CommRing A] (N : ℕ) (j : Fin (N + 1)) :
    (HomogeneousLocalization.fromZeroRingHom (ProjSpace.grading A N)
        (Submonoid.powers (X j : MvPolynomial (Fin (N + 1)) A))).comp
        (algebraMap A (ProjSpace.grading A N 0)) =
      (ProjSpace.polyToChart A j).comp C := by
  rw [ProjSpace.polyToChart, MvPolynomial.eval₂Hom_comp_C]

lemma flat_chart_structureMap (A : Type u) [CommRing A] (N : ℕ) (j : Fin (N + 1)) :
    ((HomogeneousLocalization.fromZeroRingHom (ProjSpace.grading A N)
        (Submonoid.powers (X j : MvPolynomial (Fin (N + 1)) A))).comp
        (algebraMap A (ProjSpace.grading A N 0))).Flat := by
  rw [chart_structureMap_eq]
  refine RingHom.Flat.comp ?_ (RingHom.Flat.of_bijective (ProjSpace.chartEquiv A j).symm.bijective)
  rw [← MvPolynomial.algebraMap_eq, RingHom.flat_algebraMap_iff]
  infer_instance

theorem PNFlat.proof : PNFlat.Statement.{u} := by
  intro A _ N
  change Flat (𝟙 _ ≫ ProjSpace.toSpecBase A N)
  rw [Category.id_comp]
  have : IsZariskiLocalAtSource @Flat := HasRingHomProperty.instIsZariskiLocalAtSource
  refine (IsZariskiLocalAtSource.iff_of_iSup_eq_top _ (ProjSpace.iSup_stdOpen (A := A) (n := N))).mpr
    fun j => ?_
  change Flat ((Proj.basicOpen (ProjSpace.grading A N) (X j)).ι ≫ ProjSpace.toSpecBase A N)
  have e : (Proj.basicOpen (ProjSpace.grading A N) (X j)).ι =
      (Proj.basicOpenIsoSpec (ProjSpace.grading A N) (X j) (ProjSpace.X_mem j) one_pos).hom ≫
        Proj.awayι (ProjSpace.grading A N) (X j) (ProjSpace.X_mem j) one_pos := by
    rw [← Proj.basicOpenIsoSpec_inv_ι, Iso.hom_inv_id_assoc]
  have h : Flat (Proj.awayι (ProjSpace.grading A N) (X j) (ProjSpace.X_mem j) one_pos ≫
      ProjSpace.toSpecBase A N) := by
    rw [ProjSpace.toSpecBase, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, Flat.SpecMap_iff]
    exact flat_chart_structureMap A N j
  rw [e, Category.assoc]
  infer_instance

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry GroundTheory.Arith.SchemeCoh

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

lemma SectionsLatticeFS.isReduced_homogeneousLocalization {ι R A : Type*} [CommRing R]
    [CommRing A] [Algebra R A] [AddCommMonoid ι] [DecidableEq ι] {𝒜 : ι → Submodule R A}
    [GradedAlgebra 𝒜] {S : Submonoid A} [IsReduced (Localization S)] :
    IsReduced (HomogeneousLocalization 𝒜 S) := by
  refine ⟨fun y ⟨n, hn⟩ => HomogeneousLocalization.val_injective (𝒜 := 𝒜) (x := S) ?_⟩
  rw [HomogeneousLocalization.val_zero]
  refine IsReduced.eq_zero _ ⟨n, ?_⟩
  rw [← HomogeneousLocalization.val_pow, hn, HomogeneousLocalization.val_zero]

theorem SectionsLatticeFS.PNReduced.proof : SectionsLatticeFS.PNReduced.Statement.{u} := by
  intro A _ _ N
  have : ∀ x : projectiveSpace A N,
      _root_.IsReduced ((projectiveSpace A N).presheaf.stalk x) := fun x => by
    have := x.isPrime
    have : _root_.IsReduced (CommRingCat.of
        (HomogeneousLocalization.AtPrime (ProjSpace.grading A N)
          x.asHomogeneousIdeal.toIdeal)) :=
      SectionsLatticeFS.isReduced_homogeneousLocalization
    exact isReduced_of_injective _
      (Proj.stalkIso (ProjSpace.grading A N) x).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk (projectiveSpace A N)

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Set

noncomputable section

namespace SectionsLatticeFS

lemma FSFullSupport.inter_chartDomain_nonempty {N : ℕ} {U : Set (CP N)} (hU : IsOpen U)
    (hne : U.Nonempty) : (U ∩ CP.chartDomain 0).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  induction x using Projectivization.ind with
  | h v hv =>
    rw [ProjTopology.isOpen_iff] at hU
    obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.mp hU
    let g : ℂ → (Fin (N + 1) → ℂ) := fun t => v + t • Pi.single 0 1
    have hg : Continuous g := continuous_const.add (continuous_id.smul continuous_const)
    have hvO : v ∈ O := by
      have : (⟨v, hv⟩ : {w : Fin (N + 1) → ℂ // w ≠ 0}) ∈ Projectivization.mk' ℂ ⁻¹' U := hx
      rw [← hOU] at this
      exact this
    have h0 : (g ⁻¹' O).Nonempty := ⟨0, by simpa [g] using hvO⟩
    obtain ⟨t, htO, ht⟩ :=
      (dense_compl_singleton (-(v 0))).inter_open_nonempty _ (hO.preimage hg) h0
    have hw0 : g t 0 ≠ 0 := by
      intro h
      apply ht
      simp only [g, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h
      simp only [mem_singleton_iff]
      linear_combination h
    have hw : g t ≠ 0 := fun h => hw0 (by rw [h]; rfl)
    refine ⟨Projectivization.mk ℂ (g t) hw, ?_, hw0⟩
    have : (⟨g t, hw⟩ : {w : Fin (N + 1) → ℂ // w ≠ 0}) ∈ Subtype.val ⁻¹' O := htO
    rw [hOU] at this
    exact this

theorem FSFullSupport.proof : FSFullSupport.Statement := by
  intro N U hU hne
  obtain ⟨x, hxU, hx0⟩ := FSFullSupport.inter_chartDomain_nonempty hU hne
  rw [CP.fsMeasure, Measure.map_apply (CP.measurable_chartInv 0) hU.measurableSet, CP.fsChartMeasure,
    pos_iff_ne_zero, Ne,
    withDensity_apply_eq_zero' (CP.measurable_fsVolumeDensity 0).ennreal_ofReal.aemeasurable]
  have hset : {z : Fin N → ℂ | ENNReal.ofReal (CP.fsVolumeDensity 0 z) ≠ 0} = univ := by
    ext z
    simp [CP.fsVolumeDensity_pos 0 z]
  rw [hset, univ_inter, ← Ne, ← pos_iff_ne_zero]
  refine ((CP.continuous_chartInv 0).isOpen_preimage U hU).measure_pos volume
    ⟨CP.chartCoord 0 x, ?_⟩
  simpa [CP.chartInv_chartCoord 0 hx0] using hxU

example : 0 < CP.fsMeasure 1 univ := FSFullSupport.proof 1 univ isOpen_univ univ_nonempty

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

noncomputable section

namespace SectionsLatticeFS

theorem FSConjInvariant.proof : FSConjInvariant.Statement := by
  intro N
  let cv : (Fin N → ℂ) → (Fin N → ℂ) := fun z k => starRingEnd ℂ (z k)
  have hc : MeasurePreserving (starRingEnd ℂ) (volume : Measure ℂ) volume :=
    LinearIsometryEquiv.measurePreserving Complex.conjLIE
  have hcv : MeasurePreserving cv volume volume := volume_preserving_pi fun _ => hc
  have hchart : CP.conj ∘ CP.chartInv 0 = CP.chartInv 0 ∘ cv := by
    funext z
    simp only [Function.comp, CP.chartInv, CP.conj_mk]
    congr 1
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [CP.conjVec_apply]
    · have h1 := CP.chartVec_succAbove (0 : Fin (N + 1)) z j
      have h2 := CP.chartVec_succAbove (0 : Fin (N + 1)) (cv z) j
      simp only [Fin.succAbove_zero] at h1 h2
      rw [CP.conjVec_apply, h1, h2]
  have hdens : ∀ z, CP.fsVolumeDensity (0 : Fin (N + 1)) (cv z) = CP.fsVolumeDensity 0 z := by
    intro z
    simp only [CP.fsVolumeDensity_eq, normSqSum, cv, Complex.norm_conj]
  have hmeas : Measurable fun z => ENNReal.ofReal (CP.fsVolumeDensity (0 : Fin (N + 1)) z) :=
    ENNReal.measurable_ofReal.comp (CP.measurable_fsVolumeDensity 0)
  have hmap : (CP.fsChartMeasure (N := N) 0).map cv = CP.fsChartMeasure 0 := by
    ext s hs
    rw [Measure.map_apply hcv.measurable hs, CP.fsChartMeasure,
      withDensity_apply _ (hcv.measurable hs), withDensity_apply _ hs,
      ← hcv.setLIntegral_comp_preimage hs hmeas]
    simp only [hdens]
  rw [CP.fsMeasure, Measure.map_map CP.continuous_conj.measurable (CP.measurable_chartInv 0), hchart,
    ← Measure.map_map (CP.measurable_chartInv 0) hcv.measurable, hmap]

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace GroundTheory.Arith.SchemeCoh
  GroundTheory.Arith.SchemeCoh.ProjSpace MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra algebraOfOver

noncomputable section

namespace SectionsLatticeFS.PolySections

variable {A : Type u} [CommRing A] {N : ℕ}

lemma degree_eq_of_weight {e : Fin (N + 1) →₀ ℕ} {n : ℕ} (h : Finsupp.weight 1 e = n) :
    e.degree = n := by
  rw [← h, Finsupp.degree_eq_weight_one]
  rfl

lemma toLaurent_mem_LDeg {n : ℕ} {P : MvPolynomial (Fin (N + 1)) A} (hP : P ∈ grading A N n)
    (s : Set (Fin (N + 1))) : toLaurent A N P ∈ LDeg A s n := by
  intro m hm
  by_cases hr : m ∈ Set.range (expHom N)
  · obtain ⟨e, rfl⟩ := hr
    rw [coeff_toLaurent_expHom] at hm
    refine ⟨?_, fun j _ => ?_⟩
    · rw [sum_expHom]
      exact_mod_cast degree_eq_of_weight ((mem_homogeneousSubmodule n P).mp hP hm)
    · simp [expHom]
  · exact (hm (coeff_toLaurent_eq_zero hr)).elim

lemma exists_toLaurent_eq {n : ℕ} {ℓ : Laurent A N} (hℓ : ∀ j, ℓ ∈ LDeg A {j} (n : ℤ)) :
    ∃ P ∈ grading A N n, toLaurent A N P = ℓ := by
  classical
  have hnn : ∀ m, ℓ.coeff m ≠ 0 → ∀ i, 0 ≤ m i := by
    intro m hm i
    by_cases h : ∃ j, j ≠ i
    · obtain ⟨j, hj⟩ := h
      exact (hℓ j m hm).2 i (by simpa [eq_comm] using hj)
    · push Not at h
      have hs : ∑ j, m j = m i :=
        Finset.sum_eq_single i (fun j _ hj => absurd (h j) hj) (by simp)
      have := (hℓ i m hm).1
      omega
  have hrange : ∀ m, ℓ.coeff m ≠ 0 → m ∈ Set.range (expHom N) := by
    intro m hm
    refine ⟨Finsupp.equivFunOnFinite.symm fun i => (m i).toNat, funext fun i => ?_⟩
    simp [expHom, Int.toNat_of_nonneg (hnn m hm i)]
  let S : Finset (Fin (N + 1) →₀ ℕ) :=
    ℓ.coeff.support.preimage (expHom N) expHom_injective.injOn
  let P : MvPolynomial (Fin (N + 1)) A := ∑ e ∈ S, monomial e (ℓ.coeff (expHom N e))
  have hcoeff : ∀ e, P.coeff e = ℓ.coeff (expHom N e) := by
    intro e
    simp only [P, coeff_sum, coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with he
    · rfl
    · simp only [S, Finset.mem_preimage, Finsupp.mem_support_iff, not_not] at he
      exact he.symm
  refine ⟨P, (mem_homogeneousSubmodule n P).mpr fun e he => ?_, ?_⟩
  · rw [hcoeff] at he
    have h1 := (hℓ 0 _ he).1
    rw [sum_expHom] at h1
    have h2 : e.degree = n := by exact_mod_cast h1
    rw [← h2, Finsupp.degree_eq_weight_one]
    rfl
  · apply AddMonoidAlgebra.coeff_injective
    ext m
    by_cases hm : m ∈ Set.range (expHom N)
    · obtain ⟨e, rfl⟩ := hm
      rw [coeff_toLaurent_expHom, hcoeff]
    · rw [coeff_toLaurent_eq_zero hm]
      by_contra h
      exact hm (hrange m (Ne.symm h))

variable (A N) in

def lpoly (n : ℕ) (s : (ProjScheme.self A N).H0 (ProjScheme.twistN A N n)) : Laurent A N :=
  lval (globalCocycle (twistAb A N n) (cover A N) s).1 (fun _ => 0)

lemma isCocycle (n : ℕ) (s : (ProjScheme.self A N).H0 (ProjScheme.twistN A N n)) :
    d _ _ 0 (globalCocycle (twistAb A N n) (cover A N) s).1 = 0 :=
  (mem_cocycles _).1 (globalCocycle (twistAb A N n) (cover A N) s).2

lemma lpoly_mem (n : ℕ) (s : (ProjScheme.self A N).H0 (ProjScheme.twistN A N n)) (j : Fin (N + 1)) :
    lpoly A N n s ∈ LDeg A {j} (n : ℤ) := by
  have h := lval_mem (globalCocycle (twistAb A N n) (cover A N) s).1 (fun _ => j)
  rw [lpoly, lval_eq_of_cocycle _ (isCocycle n s) (fun _ => 0) (fun _ => j)]
  rwa [range_const_fin_one] at h

lemma lpoly_injective (n : ℕ) : Function.Injective (lpoly A N n) := by
  intro s t h
  apply globalCocycle_injective (twistAb A N n) (cover A N)
    (modulesAb (twistingSheaf (grading A N) (n : ℤ))).property iSup_stdOpen
  apply Subtype.ext
  apply cochain_ext
  intro i
  rw [lval_eq_of_cocycle _ (isCocycle n s) i (fun _ => 0),
    lval_eq_of_cocycle _ (isCocycle n t) i (fun _ => 0)]
  exact h

lemma algebraMap_mem_awayDeg {n : ℕ} {P : MvPolynomial (Fin (N + 1)) A} (hP : P ∈ grading A N n)
    (i : Fin 1 → Fin (N + 1)) :
    algebraMap (MvPolynomial (Fin (N + 1)) A) (Localization.Away (xprod (A := A) i)) P ∈
      ProjTwist.awayDeg (grading A N) (xprod_mem i) (Nat.succ_pos 0) (n : ℤ) := by
  have h := ProjTwist.mk_mem_awayDeg (xprod_mem i) (Nat.succ_pos 0) (k := (n : ℤ)) (n := 0) (j := n)
    (a := P) hP (by simp)
  have e : ProjTwist.fpow (xprod (A := A) i) 0 = 1 := Subtype.ext (pow_zero _)
  rwa [e, Localization.mk_one_eq_algebraMap] at h

lemma lpoly_polySection {n : ℕ} {P : MvPolynomial (Fin (N + 1)) A} (hP : P ∈ grading A N n) :
    lpoly A N n (ProjScheme.polySection hP) = toLaurent A N P := by
  have hz : (awayDegEquiv (fun _ : Fin 1 => (0 : Fin (N + 1))) (n : ℤ)).symm
      ⟨toLaurent A N P, toLaurent_mem_LDeg hP _⟩ = ⟨_, algebraMap_mem_awayDeg hP _⟩ := by
    rw [AddEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [awayDegEquiv_apply, awayToLaurent_algebraMap]
  have key : (globalCocycle (twistAb A N n) (cover A N) (ProjScheme.polySection hP)).1
      (fun _ => 0) = theta (fun _ : Fin 1 => (0 : Fin (N + 1))) (n : ℤ)
        ⟨toLaurent A N P, toLaurent_mem_LDeg hP _⟩ := by
    apply ProjTwist.ext
    funext x
    rw [val_theta, hz]
    refine Eq.trans ?_ (ProjTwist.locMap_algebraMap (𝒜 := grading A N) x.1 _ P).symm
    rw [← Localization.mk_one_eq_algebraMap]
    rfl
  rw [lpoly, lval, key, AddEquiv.symm_apply_apply]

lemma polySection_add {n : ℕ} {P Q : MvPolynomial (Fin (N + 1)) A} (hP : P ∈ grading A N n)
    (hQ : Q ∈ grading A N n) (hPQ : P + Q ∈ grading A N n) :
    ProjScheme.polySection hPQ = ProjScheme.polySection hP + ProjScheme.polySection hQ := by
  apply ProjTwist.ext
  funext x
  exact (Localization.add_mk_self P 1 Q).symm

lemma polySection_smul {n : ℕ} (a : A) {P : MvPolynomial (Fin (N + 1)) A} (hP : P ∈ grading A N n)
    (haP : a • P ∈ grading A N n) :
    ProjScheme.polySection haP = a • ProjScheme.polySection hP := by
  apply ProjTwist.ext
  funext x
  change Localization.mk (a • P) 1 =
    projValue (grading A N) (algebraMap A Γ(projectiveSpace A N, ⊤) a) x.1 trivial *
      Localization.mk P 1
  rw [projValue_algebraMap, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul, mul_one,
    smul_eq_C_mul]

theorem proof : SectionsLatticeFS.PolySections.Statement.{u} := by
  intro A _ N n
  let f : grading A N n →ₗ[A] (ProjScheme.self A N).H0 (ProjScheme.twistN A N n) :=
    { toFun := fun P => ProjScheme.polySection P.2
      map_add' := fun P Q => polySection_add P.2 Q.2 _
      map_smul' := fun a P => polySection_smul a P.2 _ }
  have hinj : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    apply toLaurent_injective
    rw [← lpoly_polySection P.2, ← lpoly_polySection Q.2]
    exact congrArg (lpoly A N n) h
  have hsurj : Function.Surjective f := by
    intro s
    obtain ⟨P, hP, hPs⟩ := exists_toLaurent_eq (lpoly_mem n s)
    exact ⟨⟨P, hP⟩, lpoly_injective n (by rw [← hPs]; exact lpoly_polySection hP)⟩
  exact ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, fun P => rfl⟩

end SectionsLatticeFS.PolySections

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry GroundTheory.Arith.SchemeCoh

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace SectionsLatticeFS

open ProjScheme

lemma polySection_congr {A : Type u} [CommRing A] {N n : ℕ} {P Q : MvPolynomial (Fin (N + 1)) A}
    (hP : P ∈ ProjSpace.grading A N n) (hQ : Q ∈ ProjSpace.grading A N n) (h : P = Q) :
    polySection hP = polySection hQ := by
  subst h; rfl

def monomialBasisGrading (A : Type u) [CommRing A] (N n : ℕ) :
    Module.Basis {a : Fin (N + 1) →₀ ℕ // a.degree = n} A (ProjSpace.grading A N n) :=
  (MvPolynomial.basisRestrictSupport A {a : Fin (N + 1) →₀ ℕ | a.degree = n}).map
    (LinearEquiv.ofEq _ _ (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (σ := Fin (N + 1)) (R := A) n).symm)

lemma monomialBasisGrading_apply (A : Type u) [CommRing A] (N n : ℕ)
    (a : {a : Fin (N + 1) →₀ ℕ // a.degree = n}) :
    (monomialBasisGrading A N n a : MvPolynomial (Fin (N + 1)) A) = MvPolynomial.monomial a.1 1 := by
  have h : monomialBasisGrading A N n a = ⟨_, monomial_mem_grading (A := A) a.1 a.2⟩ := by
    rw [Module.Basis.apply_eq_iff]
    ext b
    simp only [monomialBasisGrading, MvPolynomial.basisRestrictSupport, Module.Basis.map_repr,
      Finsupp.single_apply, Subtype.ext_iff]
    change MvPolynomial.coeff b.1 (MvPolynomial.monomial a.1 (1 : A)) = _
    rw [MvPolynomial.coeff_monomial]
  rw [h]

theorem MonomialBasis.proof (h : PolySections.Statement.{u}) : MonomialBasis.Statement.{u} := by
  intro A _ N n
  obtain ⟨e, he⟩ := h A N n
  refine ⟨(monomialBasisGrading A N n).map e, fun a => ?_⟩
  rw [Module.Basis.map_apply, he]
  exact polySection_congr _ _ (monomialBasisGrading_apply A N n a)

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry NumberField TensorProduct GroundTheory.Arith.SchemeCoh
open scoped LinearAlgebra.Projectivization

noncomputable section

namespace SectionsLatticeFS

open ProjScheme

lemma SupMonomial.pow_mul_prod_le {ι : Type*} [Fintype ι] (a : ι → ℕ) (q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) :
    ((∑ i, a i : ℕ) : ℝ) ^ (∑ i, a i) * ∏ i, q i ^ a i ≤
      (∑ i, q i) ^ (∑ i, a i) * ∏ i, (a i : ℝ) ^ a i := by
  rcases Nat.eq_zero_or_pos (∑ i, a i) with h0 | hpos
  · have ha : ∀ i, a i = 0 := fun i => Finset.sum_eq_zero_iff.mp h0 i (Finset.mem_univ i)
    simp [ha]
  set n := ∑ i, a i with hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hpos
  set w : ι → ℝ := fun i => (a i : ℝ) / n
  set z : ι → ℝ := fun i => q i / a i
  have hz : ∀ i, 0 ≤ z i := fun i => div_nonneg (hq i) (Nat.cast_nonneg _)
  have hw : ∑ i, w i = 1 := by
    simp only [w, ← Finset.sum_div]
    rw [← Nat.cast_sum, ← hn, div_self hnR.ne']
  have hamgm := Real.geom_mean_le_arith_mean_weighted Finset.univ w z
    (fun i _ => div_nonneg (Nat.cast_nonneg _) hnR.le) hw (fun i _ => hz i)
  have hsum : ∑ i, w i * z i ≤ (∑ i, q i) / n := by
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [w, z]
    rcases eq_or_ne (a i : ℝ) 0 with h | h
    · rw [h]; simpa using div_nonneg (hq i) hnR.le
    · rw [div_mul_div_comm, mul_comm (a i : ℝ), mul_div_mul_right _ _ h]
  have key : (∏ i, z i ^ w i) ^ n = ∏ i, z i ^ a i := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hz i), div_mul_cancel₀ _ hnR.ne', Real.rpow_natCast]
  have h1 : ∏ i, z i ^ a i ≤ (∑ i, q i) ^ n / (n : ℝ) ^ n := by
    rw [← key, ← div_pow]
    exact pow_le_pow_left₀ (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hz i) _)
      (hamgm.trans hsum) n
  have h2 : ∏ i, q i ^ a i = (∏ i, z i ^ a i) * ∏ i, (a i : ℝ) ^ a i := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [z]
    rcases eq_or_ne (a i) 0 with h | h
    · simp [h]
    · rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (Nat.cast_ne_zero.mpr h))]
  have hA : 0 ≤ ∏ i, (a i : ℝ) ^ a i := Finset.prod_nonneg fun i _ => by positivity
  have hN : 0 < (n : ℝ) ^ n := pow_pos hnR n
  rw [h2]
  calc (n : ℝ) ^ n * ((∏ i, z i ^ a i) * ∏ i, (a i : ℝ) ^ a i)
      ≤ (n : ℝ) ^ n * ((∑ i, q i) ^ n / (n : ℝ) ^ n * ∏ i, (a i : ℝ) ^ a i) := by gcongr
    _ = (∑ i, q i) ^ n * ∏ i, (a i : ℝ) ^ a i := by field_simp

lemma SupMonomial.sq_eq {N : ℕ} (a : Fin (N + 1) →₀ ℕ) (v : Fin (N + 1) → ℂ) :
    (‖MvPolynomial.eval v (MvPolynomial.monomial a (1 : ℂ))‖ / norm2 v ^ a.degree) ^ 2 =
      (∏ i, (‖v i‖ ^ 2) ^ a i) / (∑ i, ‖v i‖ ^ 2) ^ a.degree := by
  rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod_fintype _ _ (fun i => pow_zero _), div_pow,
    show (norm2 v ^ a.degree) ^ 2 = (norm2 v ^ 2) ^ a.degree by ring, euclideanNorm_sq, norm_prod,
    ← Finset.prod_pow]
  simp only [norm_pow, ← pow_mul, mul_comm (a _) 2]
  rfl

lemma SupMonomial.le {N : ℕ} (a : Fin (N + 1) →₀ ℕ) (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) :
    ‖MvPolynomial.eval v (MvPolynomial.monomial a (1 : ℂ))‖ / norm2 v ^ a.degree ≤
      √((∏ i, ((a i : ℝ) ^ a i)) / (a.degree : ℝ) ^ a.degree) := by
  have hx : 0 ≤ ‖MvPolynomial.eval v (MvPolynomial.monomial a (1 : ℂ))‖ / norm2 v ^ a.degree :=
    div_nonneg (norm_nonneg _) (pow_nonneg (euclideanNorm_pos hv).le _)
  rw [← Real.sqrt_sq hx]
  refine Real.sqrt_le_sqrt ?_
  rw [SupMonomial.sq_eq]
  have hS : 0 < (∑ i, ‖v i‖ ^ 2) ^ a.degree := pow_pos (normSq2_pos hv) _
  have hN : 0 < (a.degree : ℝ) ^ a.degree := by
    rcases Nat.eq_zero_or_pos a.degree with h | h
    · simp [h]
    · exact pow_pos (by exact_mod_cast h) _
  rw [div_le_div_iff₀ hS hN]
  have := SupMonomial.pow_mul_prod_le (fun i => a i) (fun i => ‖v i‖ ^ 2) (fun i => by positivity)
  rw [← Finsupp.degree_eq_sum] at this
  linarith

lemma SupMonomial.exists_eq {N : ℕ} (a : Fin (N + 1) →₀ ℕ) :
    ∃ v : Fin (N + 1) → ℂ, v ≠ 0 ∧
      ‖MvPolynomial.eval v (MvPolynomial.monomial a (1 : ℂ))‖ / norm2 v ^ a.degree =
        √((∏ i, ((a i : ℝ) ^ a i)) / (a.degree : ℝ) ^ a.degree) := by
  rcases Nat.eq_zero_or_pos a.degree with h0 | hpos
  · have ha : a = 0 := (Finsupp.degree_eq_zero_iff a).mp h0
    subst ha
    refine ⟨Pi.single 0 1, by simp [funext_iff, Pi.single_apply], ?_⟩
    simp
  set n := a.degree
  have hnR : (0 : ℝ) < n := by exact_mod_cast hpos
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (show ∑ i, a i ≠ 0 by rw [← Finsupp.degree_eq_sum]; exact hpos.ne')
  set v : Fin (N + 1) → ℂ := fun i => ((√((a i : ℝ) / n) : ℝ) : ℂ)
  have hvi : ∀ i, ‖v i‖ ^ 2 = (a i : ℝ) / n := fun i => by
    simp only [v, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact Real.sq_sqrt (div_nonneg (Nat.cast_nonneg _) hnR.le)
  have hv : v ≠ 0 := fun h => by
    have := hvi j
    rw [h, Pi.zero_apply, norm_zero, zero_pow two_ne_zero, eq_comm, div_eq_zero_iff] at this
    exact this.elim (fun h' => hj (by exact_mod_cast h')) hnR.ne'
  refine ⟨v, hv, ?_⟩
  have hx : 0 ≤ ‖MvPolynomial.eval v (MvPolynomial.monomial a (1 : ℂ))‖ / norm2 v ^ n :=
    div_nonneg (norm_nonneg _) (pow_nonneg (euclideanNorm_pos hv).le _)
  rw [← Real.sqrt_sq hx, SupMonomial.sq_eq]
  congr 1
  simp only [hvi]
  rw [← Finset.sum_div, ← Nat.cast_sum, ← Finsupp.degree_eq_sum, div_self hnR.ne', one_pow, div_one,
    Finset.prod_congr rfl fun i _ => div_pow (a i : ℝ) n (a i), Finset.prod_div_distrib,
    Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_eq_sum]

theorem SupMonomial.proof (h : FSValue.Statement.{0}) : SupMonomial.Statement := by
  intro K _ _ N σ a
  have hval : ∀ x : (self (𝓞 K) N).complexPoints (intEmb σ),
      fsFibreNorm a.degree (intEmb σ) x ((self (𝓞 K) N).evalFibre (twistN (𝓞 K) N a.degree) σ x
        ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] polySection (monomial_mem_grading (A := 𝓞 K) a rfl))) =
      CP.fsNormPoly a.degree (MvPolynomial.monomial a (1 : ℂ)) x.1 := by
    intro x
    rw [evalFibre_tmul, map_one, one_smul, h, MvPolynomial.map_monomial, map_one]
  have hle : ∀ y : CP N, CP.fsNormPoly a.degree (MvPolynomial.monomial a (1 : ℂ)) y ≤
      √((∏ i, ((a i : ℝ) ^ a i)) / (a.degree : ℝ) ^ a.degree) :=
    fun y => SupMonomial.le a y.rep y.rep_nonzero
  obtain ⟨v, hv, hveq⟩ := SupMonomial.exists_eq a
  let x₀ : (self (𝓞 K) N).complexPoints (intEmb σ) := selfPoint (intEmb σ) (Projectivization.mk ℂ v hv)
  have : Nonempty ((self (𝓞 K) N).complexPoints (intEmb σ)) := ⟨x₀⟩
  simp only [fsSupNorm, hval]
  refine le_antisymm (ciSup_le fun x => hle x.1)
    (le_ciSup_of_le ⟨√((∏ i, ((a i : ℝ) ^ a i)) / (a.degree : ℝ) ^ a.degree), ?_⟩ x₀ (le_of_eq ?_))
  · rintro _ ⟨x, rfl⟩
    exact hle x.1
  · rw [← hveq]
    exact (CP.fsNormPoly_mk (MvPolynomial.isHomogeneous_monomial 1 rfl) v hv).symm

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MeasureTheory NumberField
  GroundTheory.Arith.SchemeCoh

universe u

noncomputable section

namespace SectionsLatticeFS

theorem FSCoord.full : FSCoord.Statement.{u} := FSCoord.proof

theorem FSIndex.full : FSIndex.Statement.{u} := FSIndex.proof FSCoord.full

theorem FSValue.full : FSValue.Statement.{u} := FSValue.proof FSCoord.full

theorem FSContinuousFrame.full : FSContinuousFrame.Statement.{u} :=
  FSContinuousFrame.proof FSIndex.full ComplexMetric.RegularContinuous.full

theorem FSNormConj.full : FSNormConj.Statement.{u} := FSNormConj.proof FSIndex.full

theorem PNFlat.full : PNFlat.Statement.{u} := PNFlat.proof

theorem PNReduced.full : PNReduced.Statement.{u} := PNReduced.proof

theorem FSFullSupport.full : FSFullSupport.Statement := FSFullSupport.proof

theorem FSConjInvariant.full : FSConjInvariant.Statement := FSConjInvariant.proof

theorem PolySections.full : PolySections.Statement.{u} := PolySections.proof

theorem MonomialBasis.full : MonomialBasis.Statement.{u} := MonomialBasis.proof PolySections.full

theorem SupMonomial.full : SupMonomial.Statement := SupMonomial.proof FSValue.full

theorem L2MonomialOrthogonality.full : L2MonomialOrthogonality.Statement := L2MonomialOrthogonality.proof FSCoord.full FSIndex.full

end SectionsLatticeFS

namespace ProjScheme

open SectionsLatticeFS

def fsBundleFull {A : Type u} [CommRing A] {N : ℕ} (n : ℕ) : (self A N).HermitianLineBundle :=
  fsBundle FSContinuousFrame.full FSNormConj.full n

def fsPointMeasuresFull (K : Type) [Field K] [NumberField K] (N : ℕ) : (self (𝓞 K) N).PointMeasures :=
  fsPointMeasures K N FSFullSupport.full FSConjInvariant.full

example : (self (𝓞 ℚ) 1).HermitianLineBundle := fsBundleFull 1

example : (self (𝓞 ℚ) 1).PointMeasures := fsPointMeasuresFull ℚ 1

end ProjScheme

end

end GroundTheory.Heights₂.Heights
end
