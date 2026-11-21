import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsTranslSum
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFrameChangeIntegralInvertibleMatrix
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TorsionRationalOverFiniteExtensionLevelStructure
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsCdvrFiniteExtension
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralFramedPointBaseChangeStable
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsExtensionAllModelsUniformized
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.TriangularReframeCompBaseChangeBorel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralIff
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.VVAlgebraMapNonneg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTraceOrthogonality
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralScalarOfPulledBackGeneratorExtendsModel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModuliPointIntegralFrameAfterFiniteExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieLatticeOnto
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaTraceBaseChangeIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.VtMoveSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.RegTieAsm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ThetaNuPf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.VGeIffExtended
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsPullByEndOfPullRel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.RegTiePfA
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsExtPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHkIsogEtaleUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsRigIsoOfBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomPairDescendsToFinite
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomIffOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAndIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralFrameExtensionOfRankZeroSignature
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieImageCompatibleWithBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeOfGenericallySurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeIdPowFiniteEtaleSurjective

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduliPoint_integralFrame_after_finiteExtension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → IntFrExt Xo c := by
  first | exact @GlobalTheory.AnyLevelFrame.intFrExt | exact GlobalTheory.AnyLevelFrame.intFrExt | (intros; apply GlobalTheory.AnyLevelFrame.intFrExt <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaTrace_conj_iff_of_rigIso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K L : Type) [Field K] [Field L] [Algebra c.F K] [Algebra c.F L] (φ : K →ₐ[c.F] L) (y z : FrPt Xo c K) (y' z' : FrPt Xo c L) (f : Fib Xo y.x ⟶ Fib Xo z.x) (f' : Fib Xo z.x ⟶ Fib Xo y.x) (g : Fib Xo y'.x ⟶ Fib Xo z'.x) (p : ℕ), 0 < p → FrMap φ y y' → FrMap φ z z' → IsPair (p ^ 2) f f' → IsBC φ.toRingHom f g → AllRat Xo y.x (p ^ 2) → (∃ β, IsRigIso Xo.univ.t.G Xo.univ.t.PP (conj y.x z.x f.left) ((p : ℤ) ^ 2) β) → (IsThetaTrace Xo.univ.t.G Xo.univ.t.PP (conj y.x z.x f.left) p y.s z.s ↔ IsThetaTrace Xo.univ.t.G Xo.univ.t.PP (conj y'.x z'.x g.left) p y'.s z'.s) := by
  first | exact @GlobalTheory.ThetaTraceBC.isThetaTrace_baseChange_iff | exact GlobalTheory.ThetaTraceBC.isThetaTrace_baseChange_iff | (intros; apply GlobalTheory.ThetaTraceBC.isThetaTrace_baseChange_iff <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral.RegSum

def secSum {X : Scheme.{0}} {N : LB X} {n : ℕ} (F : Fin n → LB.Sec N) : LB.Sec N :=
  ⟨fun j => ∑ i, (F i).f j, fun a b => by
    simp only [map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (F i).compat a b⟩

theorem sval_sum {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {n : ℕ}
    {a : LB.Sec (LB.LinComb L φ ε)} {F : Fin n → LB.Sec (LB.LinComb L φ ε)} (h : ∀ j, a.f j = ∑ i, (F i).f j)
    (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) : sval a r z J = ∑ i, sval (F i) r z J := by
  have hm := hJ.mem φ r
  refine (congrArg (gs r z _) (h _)).trans ((gs_eq r z _ hm _).trans ?_)
  exact ((congrArg _ (map_sum _ _ _)).trans (map_sum _ _ _)).trans
    (Finset.sum_congr rfl fun i _ => (gs_eq r z _ hm _).symm)

theorem zCast_sum {S : Scheme.{0}} (A : Over S) {L : LB A.left} {T : Over S} {a b : ℤ} (e : a = b) {n : ℕ}
    {t : LB.Sec (LPow A L a T)} {F : Fin n → LB.Sec (LPow A L a T)} (h : ∀ j, t.f j = ∑ i, (F i).f j) (j) :
    (PullbackSections.zCast A e t).f j = ∑ i, (PullbackSections.zCast A e (F i)).f j := by
  subst e
  exact h j

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

theorem reg_sum (I : IntData Xo c T io y.1) (M : ℕ) {n : ℕ}
    {t : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk (xOf y)))}
    {F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk (xOf y)))}
    (h : ∀ j, t.f j = ∑ i, (F i).f j) (hF : ∀ i, Reg I M (F i)) : Reg I M t := by
  choose σ σt h1 h2 using hF
  refine ⟨secSum σ, secSum σt, fun Z r zp e1 e2 z J J' hJ hJ' => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · refine (sval_sum (zCast_sum _ _ h) zp z hJ).trans ?_
    rw [sval_sum (a := secSum σt) (F := σt) (fun _ => rfl) r z hJ', Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => h1 i Z r zp e1 e2 z J J' hJ hJ'
  · rw [sval_sum (a := secSum σt) (F := σt) (fun _ => rfl) r z hJ',
      sval_sum (a := secSum σ) (F := σ) (fun _ => rfl) _ z hJ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => h2 i Z r z J J' hJ hJ'

theorem reg_of_isTransl (I : IntData Xo c T io y.1) (M : ℕ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk (xOf y))))
    (P : PELUnif (IsLocalRing.maximalIdeal T.V) I.G) (hP : P.TorsionIso) (hM : IsUnit (M : T.V))
    (hF : letI := io.toAlgebra; IsTransl M y.1.s F) : Reg I M F := by
  let _ := io.toAlgebra
  obtain ⟨a, hVt⟩ := hF
  obtain ⟨θ, hθ, θK, hθ1, hθ2⟩ := PullbackSections.thetaTie _ _ _ _ _ _ T io y.1 I
  obtain ⟨ttK, FK, hVK, hFK⟩ := PullbackSections.VtMove.vtMoveSt _ _ _ _ _ y.1.x I.t' I.m1 I.w1 I.rig1 M _ y.1.s _ F hVt
    (fun u hu => hu) θK hθ1
  obtain ⟨σ, hσ⟩ := PullbackSections.regUnif_of' PullbackSections.thetaNu GlobalTheory.EndPullNu.main.2 GlobalTheory.FiniteLiftNu.finNu _ _ T.V I.G P hP θ hθ M hM
    I.t' I.m2 I.w2 I.rig2 θK hθ2 ttK FK hVK
  obtain ⟨σt, hσt⟩ := PullbackSections.exists_restrict I.t' _ (PullbackSections.zCast I.t'.G (PullbackSections.natCast_sq M) FK)
  have hg : ∀ {Z : Scheme.{0}} (r : Z ⟶ I.t'.G.left),
      (r ≫ PullbackSections.gsec I.t'.G) ≫ (snd (𝟙_ (Over (Sp T.Fr))) I.t'.G).left = r := fun r => by
    rw [Category.assoc, PullbackSections.gsec_snd, Category.comp_id]
  refine ⟨σ, σt, fun Z r zp h1 h2 z J J' hJ hJ' => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · rw [hσt Z r z J' hJ']
    exact hFK Z r zp (r ≫ PullbackSections.gsec I.t'.G) h1 h2 (hg r) z J J' hJ hJ'
  · rw [hσt Z r z J' hJ']
    exact hσ Z r (r ≫ PullbackSections.gsec I.t'.G) (hg r) z J J' hJ hJ'

theorem reg_of_isTranslSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (M : ℕ) (t : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk (xOf y)))), (∃ U : PELUnif (IsLocalRing.maximalIdeal T.V) I.G, U.TorsionIso) → IsUnit (M : T.V) → letI := io.toAlgebra; IsTranslSum M y.1.s t → Reg I M t := by
  intro E _ _ _ H Dw l Xo c T io y I M t ⟨P, hP⟩ hM ⟨n, F, hF, h⟩
  exact reg_sum I M h fun i => reg_of_isTransl I M (F i) P hP hM (hF i)

end GlobalTheory.HkIntegral.RegSum
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_symmetricTranslates_thetaPullback_extends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (M : ℕ) (t : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk (xOf y)))), (∃ U : PELUnif (IsLocalRing.maximalIdeal T.V) I.G, U.TorsionIso) → IsUnit (M : T.V) → letI := io.toAlgebra; IsTranslSum M y.1.s t → Reg I M t := by
  atlas_forward_decl GlobalTheory.HkIntegral.RegSum.reg_of_isTranslSum
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem isAbelianScheme_fib {K : Type} [CommRing K] (x : Sp K ⟶ Xo.X) : IsAbelianScheme (Fib Xo x) :=
  have hA := GlobalTheory.HeckePoint.isAbelianScheme_of_proper Xo.univ.t Xo.univ.proper
  { comm := by have := hA.comm; infer_instance
    smooth := by have := hA.smooth; show Smooth (pullback.snd _ _); infer_instance
    proper := by have := hA.proper; show IsProper (pullback.snd _ _); infer_instance
    geomConnected := by have := hA.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }

theorem exists_fibPtsEquiv {K : Type} [Field K] (x : Sp K ⟶ Xo.X) :
    ∃ ρ : (𝟙_ (Over (Sp K)) ⟶ Fib Xo x) ≃* (Over.mk x ⟶ Xo.univ.t.G),
      (∀ u, fibPt _ (ρ u) = u.left) ∧
      ∀ (g : Xo.univ.t.G ⟶ Xo.univ.t.G) u, ρ (u ≫ (Over.pullback x).map g) = ρ u ≫ g := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.HeckePoint.exists_ptsEquiv (isGrpPullback_pullback Xo.univ.t.G x) (𝟙_ (Over (Sp K))) x
    (Category.id_comp _)
  refine ⟨ρ, fun u => ?_, fun g u => Over.OverMorphism.ext ?_⟩
  · apply pullback.hom_ext
    · rw [fibPt, pullback.lift_fst, hρ]
    · rw [fibPt, pullback.lift_snd]
      exact (Over.w u).symm
  · have A : ((Over.pullback x).map g).left ≫ pullback.fst _ x = pullback.fst _ x ≫ g.left :=
      pullback.lift_fst _ _ _
    rw [hρ, Over.comp_left, Over.comp_left, hρ, Category.assoc, Category.assoc]
    exact congrArg (u.left ≫ ·) A

theorem exists_hkWith_of_hkRelFr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime H l P p → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (y : FrPt Xo c Ω) (C : hkKer (Xo := Xo) P p i Ω y) (z : FrPt Xo c Ω), hkRelFr P p i (hkTr Xo c p) Ω y C z → ∃ f f', HkWith p y z f f' := by
  intro E _ _ _ H Dw l Xo c P p i ⟨hP, hco, hp, hpP, hpM⟩ Ω _ _ _ y C z ⟨ψ, ψp, h, hLie, hTr⟩
  obtain ⟨⟨hfin, het, hsur⟩, -⟩ := GlobalTheory.HeckePointLaw.isHkIsog_etale_unique Xo hP hco hp hpP hpM C.2 h
  obtain ⟨-, h0, hf, hact, -, hker, -⟩ := h
  have hL : Out.Laws := abelianSchemeLaws_all.1
  have hA := isAbelianScheme_fib y.x
  have hB := isAbelianScheme_fib z.x
  have := hA.proper
  have := hB.proper
  have := hA.comm
  obtain ⟨ρ, e₁, e₂⟩ := exists_fibPtsEquiv y.x
  obtain ⟨σ, s₁, s₂⟩ := exists_fibPtsEquiv z.x
  let f : Fib Xo y.x ⟶ Fib Xo z.x := Over.homMk ψ h0
  have hψ : ∀ u, σ (u ≫ f) = ψp (ρ u) := fun u => GlobalTheory.HeckePoint.fibPt_injective _ (by
    rw [s₁, ← hf, e₁]; rfl)
  have one : ∀ (G : Over (Sp Ω)) [GrpObj G], (1 : 𝟙_ (Over (Sp Ω)) ⟶ G) = η[G] := fun G _ => by
    rw [Hom.one_def]; simp
  have hom : IsMonHom f := hL.rigidity _ _ _ hA hB f (by
    rw [← one, ← one]
    exact σ.injective (by rw [hψ, map_one, map_one, map_one]))
  have lin : Lin f := fun a => GlobalTheory.HeckePoint.hom_ext_pts hA.smooth fun u => σ.injective (by
    rw [← Category.assoc, ← Category.assoc, hψ, s₂, hψ, e₂, hact])
  have hkill : ∀ u : 𝟙_ (Over (Sp Ω)) ⟶ Fib Xo y.x, u ≫ f = 1 → u ^ p ^ 2 = 1 := fun u hu => by
    have hx : ρ u ∈ C.1 := by rw [← hker, MonoidHom.mem_ker, ← hψ, hu, map_one]
    refine ρ.injective ?_
    rw [map_pow, map_one]
    refine (GlobalTheory.HeckeKerModel.mem_tors_span Xo.univ.t _ (p ^ 2)).1 fun a ha => C.2.2.2.1 hx a ?_
    refine (Ideal.span_singleton_le_iff_mem _).2 ?_ ha
    rw [sq, Nat.cast_mul]
    refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_
    have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hpP
    rwa [map_natCast] at this
  have hpow : ∀ m : ℕ, IsMonHom (𝟙 (Fib Xo y.x) ^ m) := fun m => by
    induction m with
    | zero => rw [pow_zero]; exact inferInstanceAs (IsMonHom (toUnit _ ≫ η[Fib Xo y.x]))
    | succ m ih =>
      rw [pow_succ]
      exact inferInstanceAs (IsMonHom (lift (𝟙 (Fib Xo y.x) ^ m) (𝟙 _) ≫ μ[Fib Xo y.x]))
  have := hpow (p ^ 2)
  have : IsFinite f.left := hfin
  have : Etale f.left := het
  have : Surjective f.left := hsur
  obtain ⟨π, hπ⟩ := GlobalTheory.HeckePoint.exists_fac hA.smooth f (𝟙 (Fib Xo y.x) ^ p ^ 2) fun u hu => by
    rw [MonObj.comp_pow, Category.comp_id, hkill u hu]
  have homπ : IsMonHom π := hL.rigidity _ _ _ hB hA π (by
    rw [← IsMonHom.one_hom f, Category.assoc, hπ, IsMonHom.one_hom])
  have : Epi f.left := Flat.epi_of_flat_of_surjective _
  have : Epi f := Over.epi_of_epi_left f
  refine ⟨f, π, ⟨hom, homπ, hπ, ?_, lin, fun a => ?_⟩, hLie, hTr⟩
  · rw [← cancel_epi f, ← Category.assoc, hπ, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  · have := Xo.univ.t.act.hom a
    rw [← cancel_epi f, ← Category.assoc, ← lin a, Category.assoc, hπ, ← Category.assoc, hπ, MonObj.pow_comp,
      MonObj.comp_pow, Category.id_comp, Category.comp_id]

end GlobalTheory.HkIntegral
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_heckeIsogeny_inverse_up_to_p_sq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime H l P p → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (y : FrPt Xo c Ω) (C : hkKer (Xo := Xo) P p i Ω y) (z : FrPt Xo c Ω), hkRelFr P p i (hkTr Xo c p) Ω y C z → ∃ f f', HkWith p y z f f' := by
  first | exact @GlobalTheory.HkIntegral.exists_hkWith_of_hkRelFr | exact GlobalTheory.HkIntegral.exists_hkWith_of_hkRelFr | (intros; apply GlobalTheory.HkIntegral.exists_hkWith_of_hkRelFr <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isRigIso_of_baseChange' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X) (f : Fib Xo x ⟶ Fib Xo x') (g : Fib Xo w ⟶ Fib Xo w') (k : ℤ), IsBC φ f g → IsMonHom f → (∃ β, IsRigIso Xo.univ.t.G Xo.univ.t.PP (conj w w' g.left) k β) → ∃ β, IsRigIso Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) k β := by
  first | exact @GlobalTheory.RigIsoDescent.exists_isRigIso_of_baseChange | exact GlobalTheory.RigIsoDescent.exists_isRigIso_of_baseChange | (intros; apply GlobalTheory.RigIsoDescent.exists_isRigIso_of_baseChange <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {K : Type} [CommRing K]

theorem conj_pullback_map (x : Sp K ⟶ Xo.X) (g : Xo.univ.t.G ⟶ Xo.univ.t.G) :
    conj x x ((Over.pullback x).map g).left =
      (lift (fst (Over.mk x) Xo.univ.t.G) (snd (Over.mk x) Xo.univ.t.G ≫ g)).left := by
  refine gx_ext ?_ ?_
  · rw [lift_l_fst]
    exact (over_iff _).2 (pullback.lift_snd _ _ _)
  · rw [lift_l_snd, conj_apply, Category.assoc, Category.assoc, swap_inv_snd, Over.comp_left, ← swap_hom_fst,
      Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)

theorem conj_comp_left {x x' x'' : Sp K ⟶ Xo.X} (f : Fib Xo x ⟶ Fib Xo x') (g : Fib Xo x' ⟶ Fib Xo x'') :
    conj x x'' (f ≫ g).left = conj x x' f.left ≫ conj x' x'' g.left := by
  simp only [conj_apply, Category.assoc, Iso.inv_hom_id_assoc]
  rw [Over.comp_left]
  simp only [Category.assoc]

theorem conj_id_pow (x : Sp K ⟶ Xo.X) (n : ℕ) :
    conj x x (𝟙 (Fib Xo x) ^ n).left = (mulT Xo.univ.t.G (Over.mk x) n).left := by
  have e : (Over.pullback x).map (𝟙 Xo.univ.t.G ^ n) = 𝟙 (Fib Xo x) ^ n := by
    have := map_pow (Over.pullback x).homMonoidHom (𝟙 Xo.univ.t.G) n
    rw [← (Over.pullback x).map_id]
    exact this
  rw [← e, conj_pullback_map, MonObj.comp_pow, Category.comp_id, mulT]

theorem conj_id_inv (x : Sp K ⟶ Xo.X) :
    conj x x (𝟙 (Fib Xo x))⁻¹.left = (negT Xo.univ.t.G (Over.mk x)).left := by
  have e : (Over.pullback x).map (𝟙 Xo.univ.t.G)⁻¹ = (𝟙 (Fib Xo x))⁻¹ := by
    rw [Functor.map_inv', CategoryTheory.Functor.map_id]
  rw [← e, conj_pullback_map, GrpObj.comp_inv, Category.comp_id, negT]
  rfl

theorem negT_comm_conj {x x' : Sp K ⟶ Xo.X} (f : Fib Xo x ⟶ Fib Xo x') [IsMonHom f] :
    (negT Xo.univ.t.G (Over.mk x)).left ≫ conj x x' f.left =
      conj x x' f.left ≫ (negT Xo.univ.t.G (Over.mk x')).left := by
  rw [← conj_id_inv, ← conj_id_inv, ← conj_comp_left, ← conj_comp_left, GrpObj.inv_comp, GrpObj.comp_inv,
    Category.id_comp, Category.comp_id]

theorem pow_eq_one_of_mem_transKer_conj {x x' : Sp K ⟶ Xo.X} {f : Fib Xo x ⟶ Fib Xo x'} {f' : Fib Xo x' ⟶ Fib Xo x}
    {n : ℕ} (h : f ≫ f' = 𝟙 _ ^ n) {c : Over.mk x ⟶ Xo.univ.t.G} (hc : c ∈ transKer Xo.univ.t.G (conj x x' f.left)) :
    c ^ n = 1 := by
  rw [← mem_transKer_mulT, mem_transKer, ← conj_id_pow, ← h, conj_comp_left, ← Category.assoc, mem_transKer.1 hc]

theorem thetaTrace_isTranslSum (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x x' : Sp K ⟶ Xo.X) (f : Fib Xo x ⟶ Fib Xo x')
    (f' : Fib Xo x' ⟶ Fib Xo x) (p : ℕ) (s : LB.Sec (PPx x)) (s₀ s' : LB.Sec (PPx x')) (a : K)
    (hf : IsPair (p ^ 2) f f') (hs' : ∀ i, s'.f i = scal x' a i * s₀.f i)
    (h : IsThetaTrace Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) p s s') :
    ∃ t, IsPullOf p f a s₀ t ∧ IsTranslSum p s t := by
  obtain ⟨β, s₁, t, n, U, F, hβ, hs, ht, hr, hU, hF, hsum⟩ := h
  have := hf.1
  refine ⟨t, ⟨β, s', hβ, hs', ht⟩, n, F, fun i => ?_, hsum⟩
  have hk : (U i).pt ^ (p ^ 2) = 1 := pow_eq_one_of_mem_transKer_conj hf.2.2.1 (hU i).1
  obtain ⟨α₀, α, h₁, h₂, h₃, h₄⟩ := hs
  exact ⟨_, (U i).pt, α₀, α, s₁, U i, rfl, hk, h₁, h₂, h₃, h₄,
    (hU i).symLift hβ.2.1 Xo.univ.t.sym (negT_comm_conj f) hk, hF i⟩

end GlobalTheory.HkIntegral
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pull_isTranslSum_of_isThetaTrace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x x' : Sp K ⟶ Xo.X) (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x) (p : ℕ) (s : LB.Sec (PPx x)) (s₀ s' : LB.Sec (PPx x')) (a : K), IsPair (p ^ 2) f f' → (∀ i, s'.f i = scal x' a i * s₀.f i) → IsThetaTrace Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) p s s' → ∃ t, IsPullOf p f a s₀ t ∧ IsTranslSum p s t := by
  atlas_forward_decl GlobalTheory.HkIntegral.thetaTrace_isTranslSum
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral

open GlobalTheory.Spread

theorem fibre_transition {G X : Scheme.{0}} (p : G ⟶ X) {K L : Type} [Field K] [Field L] [Algebra K L]
    (M : IntermediateField K L) (x : Sp K ⟶ X)
    (π : pullback p (spMap (algebraMap K L) ≫ x) ⟶ pullback p (spMap (algebraMap K M) ≫ x))
    (h₁ : π ≫ pullback.fst _ _ = pullback.fst _ _)
    (h₂ : π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap M.val.toRingHom) :
    (pullbackLeftPullbackSndIso p x (spMap (algebraMap K L))).hom ≫ π =
      bcMap (pullback.snd p x) M.val ≫ (pullbackLeftPullbackSndIso p x (spMap (algebraMap K M))).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, h₁, Category.assoc, pullbackLeftPullbackSndIso_hom_fst,
      pullbackLeftPullbackSndIso_hom_fst, bcMap_fst_assoc]
  · rw [Category.assoc, h₂, Category.assoc, pullbackLeftPullbackSndIso_hom_snd,
      pullbackLeftPullbackSndIso_hom_snd_assoc, bcMap_snd]

theorem exists_descend_fibre {G X : Scheme.{0}} (p : G ⟶ X) [QuasiCompact p] [QuasiSeparated p]
    [LocallyOfFinitePresentation p] {K L : Type} [Field K] [Field L] [Algebra K L] (x x' : Sp K ⟶ X)
    (g : pullback p (spMap (algebraMap K L) ≫ x) ⟶ pullback p (spMap (algebraMap K L) ≫ x'))
    (hg : g ≫ pullback.snd _ _ = pullback.snd _ _) :
    ∃ s : Finset L, ∀ M : IntermediateField K L, (s : Set L) ⊆ M →
      ∃ f : pullback p (spMap (algebraMap K M) ≫ x) ⟶ pullback p (spMap (algebraMap K M) ≫ x'),
        f ≫ pullback.snd _ _ = pullback.snd _ _ ∧
        ∀ (π : pullback p (spMap (algebraMap K L) ≫ x) ⟶ pullback p (spMap (algebraMap K M) ≫ x))
          (π' : pullback p (spMap (algebraMap K L) ≫ x') ⟶ pullback p (spMap (algebraMap K M) ≫ x')),
          π ≫ pullback.fst _ _ = pullback.fst _ _ →
          π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap M.val.toRingHom →
          π' ≫ pullback.fst _ _ = pullback.fst _ _ →
          π' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap M.val.toRingHom →
          g ≫ π' = π ≫ f := by
  let A : Over (Sp K) := Over.mk (pullback.snd p x)
  let B : Over (Sp K) := Over.mk (pullback.snd p x')
  have : QuasiCompact A.hom := inferInstanceAs (QuasiCompact (pullback.snd p x))
  have : QuasiSeparated A.hom := inferInstanceAs (QuasiSeparated (pullback.snd p x))
  have : LocallyOfFinitePresentation B.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd p x'))
  let g₀ : pullback (pullback.snd p x) (spMap (algebraMap K L)) ⟶
      pullback (pullback.snd p x') (spMap (algebraMap K L)) :=
    (pullbackLeftPullbackSndIso p x (spMap (algebraMap K L))).hom ≫ g ≫
      (pullbackLeftPullbackSndIso p x' (spMap (algebraMap K L))).inv
  have hg₀ : g₀ ≫ pullback.snd _ _ = pullback.snd _ _ := by
    simp only [g₀, Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd, hg, pullbackLeftPullbackSndIso_hom_snd]
  obtain ⟨s, hs⟩ := HomPairDescent.exists_descend (Ω := L) A B (Over.homMk g₀ hg₀)
  refine ⟨s, fun M hM => ?_⟩
  obtain ⟨f, hf⟩ := hs M hM
  let f₀ : pullback (pullback.snd p x) (spMap (algebraMap K M)) ⟶
      pullback (pullback.snd p x') (spMap (algebraMap K M)) := f.left
  have hf₀ : f₀ ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w f
  have hf₁ : bcMap (pullback.snd p x) M.val ≫ f₀ = g₀ ≫ bcMap (pullback.snd p x') M.val := hf
  refine ⟨(pullbackLeftPullbackSndIso p x (spMap (algebraMap K M))).inv ≫ f₀ ≫
      (pullbackLeftPullbackSndIso p x' (spMap (algebraMap K M))).hom, ?_, fun π π' h₁ h₂ h₃ h₄ => ?_⟩
  · simp only [Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd, hf₀, pullbackLeftPullbackSndIso_hom_snd]
  · have e := fibre_transition p M x π h₁ h₂
    have e' := fibre_transition p M x' π' h₃ h₄
    rw [← cancel_epi (pullbackLeftPullbackSndIso p x (spMap (algebraMap K L))).hom, reassoc_of% e,
      Iso.hom_inv_id_assoc, reassoc_of% hf₁, ← e']
    simp only [g₀, Category.assoc, Iso.inv_hom_id_assoc]

theorem pair_defined_over_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X) (g : Fib Xo w ⟶ Fib Xo w') (g' : Fib Xo w' ⟶ Fib Xo w), φ.IsIntegral → w = spMap φ ≫ x → w' = spMap φ ≫ x' → IsMonHom g → IsMonHom g' → ∃ (M : Type) (_ : Field M) (i : K →+* M) (j : M →+* L), j.comp i = φ ∧ i.Finite ∧ ∀ v v' : Sp M ⟶ Xo.X, v = spMap i ≫ x → v' = spMap i ≫ x' → ∃ (f : Fib Xo v ⟶ Fib Xo v') (f' : Fib Xo v' ⟶ Fib Xo v), IsBC j f g ∧ IsBC j f' g' := by
  classical
  intro E _ _ _ H Dw l Xo K L _ _ φ x x' w w' g g' hφ hw hw' _ _
  let _ : Algebra K L := φ.toAlgebra
  have hint : Algebra.IsIntegral K L := ⟨hφ⟩
  subst hw hw'
  have hA := ObjDim.isAbelianScheme Xo.univ
  have := hA.proper
  have := hA.smooth
  obtain ⟨s, hs⟩ := exists_descend_fibre Xo.univ.t.G.hom (L := L) x x' g.left (Over.w g)
  obtain ⟨t, ht⟩ := exists_descend_fibre Xo.univ.t.G.hom (L := L) x' x g'.left (Over.w g')
  let M : IntermediateField K L := IntermediateField.adjoin K ((s ∪ t : Finset L) : Set L)
  have hM : ((s ∪ t : Finset L) : Set L) ⊆ M := IntermediateField.subset_adjoin _ _
  obtain ⟨f, hf, hf'⟩ := hs M ((Finset.coe_subset.2 Finset.subset_union_left).trans hM)
  obtain ⟨r, hr, hr'⟩ := ht M ((Finset.coe_subset.2 Finset.subset_union_right).trans hM)
  have hfin : FiniteDimensional K M :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine ⟨M, inferInstance, algebraMap K M, M.val.toRingHom, RingHom.ext fun _ => rfl,
    RingHom.finite_algebraMap.2 hfin, ?_⟩
  rintro v v' rfl rfl
  have e : ∀ y : Sp K ⟶ Xo.X, spMap φ ≫ y = spMap M.val.toRingHom ≫ spMap (algebraMap K M) ≫ y := fun y => by
    rw [← Category.assoc, spMap_algHom_comp]
  exact ⟨Over.homMk f hf, Over.homMk r hr, ⟨e x, e x', hf'⟩, ⟨e x', e x, hr'⟩⟩

end GlobalTheory.HkIntegral
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreIsogenyPair_defined_over_finite_subextension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X) (g : Fib Xo w ⟶ Fib Xo w') (g' : Fib Xo w' ⟶ Fib Xo w), φ.IsIntegral → w = spMap φ ≫ x → w' = spMap φ ≫ x' → IsMonHom g → IsMonHom g' → ∃ (M : Type) (_ : Field M) (i : K →+* M) (j : M →+* L), j.comp i = φ ∧ i.Finite ∧ ∀ v v' : Sp M ⟶ Xo.X, v = spMap i ≫ x → v' = spMap i ≫ x' → ∃ (f : Fib Xo v ⟶ Fib Xo v') (f' : Fib Xo v' ⟶ Fib Xo v), IsBC j f g ∧ IsBC j f' g' := by
  atlas_forward_decl GlobalTheory.HkIntegral.pair_defined_over_finite
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral.PairBC

section General

variable {S S' : Scheme.{0}} {j : S' ⟶ S}

theorem exists_proj {X : Scheme.{0}} (G : Over X) [GrpObj G] (x : S ⟶ X) (w : S' ⟶ X) (h : w = j ≫ x) :
    ∃ π : pullback G.hom w ⟶ pullback G.hom x, π ≫ pullback.fst _ _ = pullback.fst _ _ ∧
      π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ j ∧
      IsGrpPullback ((Over.pullback w).obj G) ((Over.pullback x).obj G) j π := by
  have e : pullback.fst G.hom w ≫ G.hom = (pullback.snd _ _ ≫ j) ≫ x := by
    rw [Category.assoc, ← h, pullback.condition]
  exact ⟨pullback.lift _ _ e, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, (isGrpPullback_pullback G _).cancel
    ((isGrpPullback_pullback G _).congr h (pullback.lift_fst _ _ e).symm) (pullback.lift_snd _ _ _)⟩

theorem id_pow_left {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {π : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G j π) (N : ℕ) : (𝟙 G' ^ N).left ≫ π = π ≫ (𝟙 G ^ N).left := by
  let U : Over.mk (G'.hom ≫ j) ⟶ G := Over.homMk π h.1.w
  have e : pushHom h G' (𝟙 G') = U := Over.OverMorphism.ext (Category.id_comp π)
  have e' : pushHom h G' (𝟙 G' ^ N) = U ≫ 𝟙 G ^ N := by
    rw [map_pow, e, MonObj.comp_pow, Category.comp_id]
  exact congrArg (fun u => u.left) e'

theorem eq_iff [Flat j] [Surjective j] {A B : Over S} {A' B' : Over S'} {α : A'.left ⟶ A.left}
    {β : B'.left ⟶ B.left} (hα : IsPullback α A'.hom A.hom j) (hβ : IsPullback β B'.hom B.hom j)
    {u v : A ⟶ B} {u' v' : A' ⟶ B'} (hu : u'.left ≫ β = α ≫ u.left) (hv : v'.left ≫ β = α ≫ v.left) :
    u = v ↔ u' = v' := by
  have : Flat α := MorphismProperty.of_isPullback (P := @Flat) hα.flip ‹_›
  have : Surjective α := MorphismProperty.of_isPullback (P := @Surjective) hα.flip ‹_›
  have : Epi α := Flat.epi_of_flat_of_surjective α
  constructor
  · rintro rfl
    exact Over.OverMorphism.ext (hβ.hom_ext (hu.trans hv.symm) (by rw [Over.w, Over.w]))
  · rintro rfl
    exact Over.OverMorphism.ext ((cancel_epi α).1 (hu.symm.trans hv))

theorem comp_sq {A B C : Over S} {A' B' C' : Over S'} {α : A'.left ⟶ A.left} {β : B'.left ⟶ B.left}
    {δ : C'.left ⟶ C.left} {u : A ⟶ B} {v : B ⟶ C} {u' : A' ⟶ B'} {v' : B' ⟶ C'}
    (hu : u'.left ≫ β = α ≫ u.left) (hv : v'.left ≫ δ = β ≫ v.left) :
    (u' ≫ v').left ≫ δ = α ≫ (u ≫ v).left := by
  rw [Over.comp_left, Over.comp_left, Category.assoc, hv, reassoc_of% hu]

theorem map_sq {X : Scheme.{0}} {G : Over X} {x : S ⟶ X} {w : S' ⟶ X} (π : pullback G.hom w ⟶ pullback G.hom x)
    (h₁ : π ≫ pullback.fst _ _ = pullback.fst _ _) (h₂ : π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ j) (a : G ⟶ G) :
    ((Over.pullback w).map a).left ≫ π = π ≫ ((Over.pullback x).map a).left := by
  apply pullback.hom_ext <;>
    simp [h₁, h₂, reassoc_of% h₁, pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc]

end General

theorem exists_isBC_and_isPair_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X), (w = spMap φ ≫ x → w' = spMap φ ≫ x' → ∀ f : Fib Xo x ⟶ Fib Xo x', ∃ g : Fib Xo w ⟶ Fib Xo w', IsBC φ f g) ∧ ∀ (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x) (g : Fib Xo w ⟶ Fib Xo w') (g' : Fib Xo w' ⟶ Fib Xo w) (N : ℕ), IsBC φ f g → IsBC φ f' g' → (IsPair N f f' ↔ IsPair N g g') := by
  intro E _ _ _ H Dw l Xo K L _ _ φ x x' w w'
  refine ⟨fun hw hw' f => ?_, fun f f' g g' N hf hf' => ?_⟩
  · obtain ⟨π, p₁, p₂, hπ⟩ := exists_proj Xo.univ.t.G x w hw
    obtain ⟨π', p₁', p₂', hπ'⟩ := exists_proj Xo.univ.t.G x' w' hw'
    have e : (π ≫ f.left) ≫ (Fib Xo x').hom = (Fib Xo w).hom ≫ spMap φ :=
      (Category.assoc _ _ _).trans ((congrArg (π ≫ ·) (Over.w f)).trans hπ.1.w)
    refine ⟨Over.homMk (hπ'.1.lift _ _ e) (hπ'.1.lift_snd _ _ e), hw, hw', fun ρ ρ' q₁ q₂ q₁' q₂' => ?_⟩
    obtain rfl : ρ = π := pullback.hom_ext (q₁.trans p₁.symm) (q₂.trans p₂.symm)
    obtain rfl : ρ' = π' := pullback.hom_ext (q₁'.trans p₁'.symm) (q₂'.trans p₂'.symm)
    exact hπ'.1.lift_fst _ _ e
  · have := FieldBaseChange.flat_spMap φ
    have := FieldBaseChange.surjective_spMap φ
    obtain ⟨π, p₁, p₂, hπ⟩ := exists_proj Xo.univ.t.G x w hf.1
    obtain ⟨π', p₁', p₂', hπ'⟩ := exists_proj Xo.univ.t.G x' w' hf.2.1
    have e := hf.2.2 π π' p₁ p₂ p₁' p₂'
    have e' := hf'.2.2 π' π p₁' p₂' p₁ p₂
    refine and_congr (FieldBaseChange.isMonHom_iff_of_isGrpPullback hπ hπ' g f e.symm).symm
      (and_congr (FieldBaseChange.isMonHom_iff_of_isGrpPullback hπ' hπ g' f' e'.symm).symm
      (and_congr (eq_iff hπ.1 hπ.1 (comp_sq e e') (id_pow_left hπ N))
      (and_congr (eq_iff hπ'.1 hπ'.1 (comp_sq e' e) (id_pow_left hπ' N))
      (and_congr (forall_congr' fun a => ?_) (forall_congr' fun a => ?_)))))
    · exact eq_iff hπ.1 hπ'.1 (comp_sq (map_sq π p₁ p₂ _) e)
        (comp_sq (u := f) (u' := g) (v := (Over.pullback x').map _) (v' := (Over.pullback w').map _) e
          (map_sq π' p₁' p₂' _))
    · exact eq_iff hπ'.1 hπ.1 (comp_sq (map_sq π' p₁' p₂' _) e')
        (comp_sq (u := f') (u' := g') (v := (Over.pullback x).map _) (v' := (Over.pullback w).map _) e'
          (map_sq π p₁ p₂ _))

end GlobalTheory.HkIntegral.PairBC
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fibreMap_baseChange_and_isogenyPair_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X), (w = spMap φ ≫ x → w' = spMap φ ≫ x' → ∀ f : Fib Xo x ⟶ Fib Xo x', ∃ g : Fib Xo w ⟶ Fib Xo w', IsBC φ f g) ∧ ∀ (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x) (g : Fib Xo w ⟶ Fib Xo w') (g' : Fib Xo w' ⟶ Fib Xo w) (N : ℕ), IsBC φ f g → IsBC φ f' g' → (IsPair N f f' ↔ IsPair N g g') := by
  first | exact @GlobalTheory.HkIntegral.PairBC.exists_isBC_and_isPair_iff | exact GlobalTheory.HkIntegral.PairBC.exists_isBC_and_isPair_iff | (intros; apply GlobalTheory.HkIntegral.PairBC.exists_isBC_and_isPair_iff <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringHom_finite_and_isIntegral_of_valuation_scaled : ∀ (T T' : CDVR) (i : T.Fr →+* T'.Fr) (r : ℕ), 0 < r → (∀ a : T.Fr, vV T'.V (i a) = (r : ℤ) * vV T.V a) → T'.FinRes → i.Finite ∧ ∀ b : T'.V, (i.comp (algebraMap T.V T.Fr)).IsIntegralElem (algebraMap T'.V T'.Fr b) := by
  first | exact @GlobalTheory.CompleteValExt.finite_and_integral | exact GlobalTheory.CompleteValExt.finite_and_integral | (intros; apply GlobalTheory.CompleteValExt.finite_and_integral <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralFrameExtension_of_rank_zero_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), Dw.p + Dw.q = 0 → IntFrExt Xo c := by
  first | exact @GlobalTheory.RankZeroFrames.intFrExt_of_rank_zero | exact GlobalTheory.RankZeroFrames.intFrExt_of_rank_zero | (intros; apply GlobalTheory.RankZeroFrames.intFrExt_of_rank_zero <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral

theorem isProper_of_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : CDVR) (x x' : Sp T.Fr ⟶ Xo.X) (G G' : SAB H (Sp T.V)) (t t' : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr))) (n₁ : SABMap t' Xo.univ.t x') (n₂ : SABMap t' G' (spMap (algebraMap T.V T.Fr))) (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x) (F : G.G ⟶ G'.G) (N : ℕ), Ext m₁ m₂ n₁ n₂ f F → f' ≫ f = 𝟙 _ ^ N → 0 < N → IsProper G.G.hom → IsProper G'.G.hom := by
  intro E _ _ _ H Dw l Xo T x x' G G' t t' m₁ m₂ n₁ n₂ f f' F N ⟨ψ, _, hψ, hc⟩ hN hpos hG
  have hU : IsAbelianScheme Xo.univ.t.G :=
    ⟨Xo.univ.t.semi.comm, Xo.univ.t.semi.smooth, Xo.univ.proper, Xo.univ.t.semi.geomConnected⟩
  have hA : IsAbelianScheme (Fib Xo x') := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback x' _ hU
  have hB : IsAbelianScheme G.G := ⟨G.semi.comm, G.semi.smooth, hG, G.semi.geomConnected⟩
  have hch : CharZero T.Fr := charZero_of_injective_ringHom (IsFractionRing.injective T.V T.Fr)
  have hu : IsUnit (N : Γ(Sp T.Fr, ⊤)) := by
    have h0 : IsUnit (N : T.Fr) := IsUnit.mk0 _ (Nat.cast_ne_zero.mpr hpos.ne')
    have := h0.map (Scheme.ΓSpecIso (CommRingCat.of T.Fr)).inv.hom
    rwa [map_natCast] at this
  obtain ⟨-, -, -, hs⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective _ (Fib Xo x') N hA hu
  have hl : f'.left ≫ f.left = (𝟙 (Fib Xo x') ^ N).left := congrArg (·.left) hN
  have hf : Function.Surjective f.left := by
    intro y
    obtain ⟨z, hz⟩ := hs.1 y
    refine ⟨f'.left z, ?_⟩
    rw [← Scheme.Hom.comp_apply, hl, hz]
  have p₁ : IsPullback m₁.φ t.G.hom Xo.univ.t.G.hom x := m₁.cart.1
  have q₁ : IsPullback n₁.φ t'.G.hom Xo.univ.t.G.hom x' := n₁.cart.1
  have q₂ : IsPullback n₂.φ t'.G.hom G'.G.hom (spMap (algebraMap T.V T.Fr)) := n₂.cart.1
  have hsq := hc p₁.isoPullback.hom q₁.isoPullback.hom (by simp) (by simp) (by simp) (by simp)
  have hψs : Function.Surjective ψ.left := by
    intro y
    obtain ⟨z, hz⟩ := hf (q₁.isoPullback.hom y)
    obtain ⟨w, rfl⟩ := (inferInstance : Surjective p₁.isoPullback.hom).1 z
    refine ⟨w, q₁.isoPullback.hom.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hsq, Scheme.Hom.comp_apply]
    exact hz
  refine (GlobalTheory.isAbelianScheme_of_generically_surjective T.V T.Fr G.G G'.G hB G'.semi F ?_).proper
  rintro y ⟨s, hs⟩
  obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback q₂ y s hs.symm
  obtain ⟨w, rfl⟩ := hψs z
  refine ⟨m₂.φ w, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← hψ, Scheme.Hom.comp_apply, hz]

end GlobalTheory.HkIntegral
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_model_of_extends_fibreIsogeny : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : CDVR) (x x' : Sp T.Fr ⟶ Xo.X) (G G' : SAB H (Sp T.V)) (t t' : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr))) (n₁ : SABMap t' Xo.univ.t x') (n₂ : SABMap t' G' (spMap (algebraMap T.V T.Fr))) (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x) (F : G.G ⟶ G'.G) (N : ℕ), Ext m₁ m₂ n₁ n₂ f F → f' ≫ f = 𝟙 _ ^ N → 0 < N → IsProper G.G.hom → IsProper G'.G.hom := by
  atlas_forward_decl GlobalTheory.HkIntegral.isProper_of_ext
end

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral

theorem exists_finite_factor {F R K L : Type} [Field F] [CommRing R] [Field K] [Field L] [Algebra F R]
    [Algebra F K] [Algebra F L] [Algebra.FiniteType F R] (φ : K →ₐ[F] L) (hφ : φ.toRingHom.IsIntegral)
    (ψ : R →ₐ[F] L) :
    ∃ (M : Type) (_ : Field M) (_ : Algebra F M) (i : K →ₐ[F] M) (j : M →ₐ[F] L) (χ : R →ₐ[F] M),
      j.comp i = φ ∧ i.toRingHom.Finite ∧ j.comp χ = ψ := by
  classical
  letI : Algebra K L := φ.toRingHom.toAlgebra
  haveI : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType F R).out
  let M : IntermediateField K L := IntermediateField.adjoin K ((s.image ψ : Finset L) : Set L)
  haveI hM : FiniteDimensional K M :=
    IntermediateField.finiteDimensional_adjoin fun x _ => hφ x
  have hmem : ∀ r : R, ψ r ∈ M.toSubalgebra.restrictScalars F := by
    intro r
    have hr : r ∈ Algebra.adjoin F (s : Set R) := hs ▸ Algebra.mem_top
    have : Algebra.adjoin F (s : Set R) ≤ (M.toSubalgebra.restrictScalars F).comap ψ := by
      refine Algebra.adjoin_le fun x hx => ?_
      exact IntermediateField.subset_adjoin K _ (by simpa using ⟨x, hx, rfl⟩)
    exact this hr
  refine ⟨M, inferInstance, inferInstance, IsScalarTower.toAlgHom F K M, M.val.restrictScalars F,
    ψ.codRestrict (M.toSubalgebra.restrictScalars F) hmem, ?_, ?_, ?_⟩
  · ext a; rfl
  · exact RingHom.finite_algebraMap.2 hM
  · ext a; rfl

theorem frPt_descends_finite :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K L : Type) [Field K] [Field L] [Algebra c.F K] [Algebra c.F L] (φ : K →ₐ[c.F] L) (z : FrPt Xo c L), φ.toRingHom.IsIntegral → ∃ (M : Type) (_ : Field M) (_ : Algebra c.F M) (i : K →ₐ[c.F] M) (j : M →ₐ[c.F] L) (z₁ : FrPt Xo c M), j.comp i = φ ∧ i.toRingHom.Finite ∧ FrMap j z₁ z := by
  intro E _ _ _ H Dw l Xo c K L _ _ _ _ φ z hφ
  obtain ⟨p, ψ, u, hu⟩ := GlobalTheory.FlagTan.fromTest_of_isLocalRing z
  haveI : Algebra.FiniteType c.F p.R := inferInstance
  obtain ⟨M, _, _, i, j, χ, h1, h2, h3⟩ := exists_finite_factor φ hφ ψ
  obtain ⟨z₁, hz⟩ := GlobalTheory.FlagTan.exists_frMap χ u
  exact ⟨M, inferInstance, inferInstance, i, j, z₁, h1, h2,
    GlobalTheory.FlagTan.frMap_of_comp hz hu fun a => DFunLike.congr_fun h3 a⟩

end GlobalTheory.HkIntegral
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framedPoint_descends_finite_subextension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K L : Type) [Field K] [Field L] [Algebra c.F K] [Algebra c.F L] (φ : K →ₐ[c.F] L) (z : FrPt Xo c L), φ.toRingHom.IsIntegral → ∃ (M : Type) (_ : Field M) (_ : Algebra c.F M) (i : K →ₐ[c.F] M) (j : M →ₐ[c.F] L) (z₁ : FrPt Xo c M), j.comp i = φ ∧ i.toRingHom.Finite ∧ FrMap j z₁ z := by
  atlas_forward_decl GlobalTheory.HkIntegral.frPt_descends_finite
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.GoodBaseChange

theorem good_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T T' : CDVR) (io : c.F →+* T.Fr) (io' : c.F →+* T'.Fr) (y : IntFr Xo c T io) (y' : IntFr Xo c T' io') (i : T.Fr →+* T'.Fr) (r : ℕ), 0 < r → (∀ a : T.Fr, vV T'.V (i a) = (r : ℤ) * vV T.V a) → xOf y' = spMap i ≫ xOf y → GlobalTheory.GoodPts.Good y → GlobalTheory.GoodPts.Good y' := by
  intro E _ _ _ H Dw l Xo c T T' io io' y y' i r _ hv hx hy
  obtain ⟨G, t, m1, m2, hp⟩ := hy
  obtain ⟨φ, hφ⟩ := GlobalTheory.IntFrBaseChange.exists_restrict T T' i r hv
  obtain ⟨G', mG⟩ : ∃ G' : SAB H (Sp T'.V), Nonempty (SABMap G' G (spMap φ)) := by
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull (spMap φ) G
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨t', mt⟩ : ∃ t' : SAB H (Sp T'.Fr), Nonempty (SABMap t' t (spMap i)) := by
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull (spMap i) t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨mG⟩ := mG
  obtain ⟨mt⟩ := mt
  obtain ⟨n1, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m1 mt
  obtain ⟨n2, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m2 mt
  have hsq : spMap i ≫ spMap (algebraMap T.V T.Fr) = spMap (algebraMap T'.V T'.Fr) ≫ spMap φ := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => (hφ a).symm))
  rw [hsq] at n2
  obtain ⟨n3, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ mG n2
  have n4 : SABMap t' Xo.univ.t (xOf y') := by
    rw [hx]
    exact n1
  exact ⟨G', t', n4, n3, MorphismProperty.of_isPullback (P := @IsProper) mG.cart.1 hp⟩

end GlobalTheory.GoodBaseChange
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodReduction_stable_valuationRing_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T T' : CDVR) (io : c.F →+* T.Fr) (io' : c.F →+* T'.Fr) (y : IntFr Xo c T io) (y' : IntFr Xo c T' io') (i : T.Fr →+* T'.Fr) (r : ℕ), 0 < r → (∀ a : T.Fr, vV T'.V (i a) = (r : ℤ) * vV T.V a) → xOf y' = spMap i ≫ xOf y → GlobalTheory.GoodPts.Good y → GlobalTheory.GoodPts.Good y' := by
  atlas_forward_decl GlobalTheory.GoodBaseChange.good_baseChange
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HkIntegral

open GlobalTheory.FlagTan GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39

theorem exists_lift {L L' Ω : Type} [Field L] [Field L'] [Field Ω] [IsAlgClosed Ω] (j : L →+* Ω) (i : L →+* L')
    (hi : i.Finite) : ∃ j' : L' →+* Ω, j'.comp i = j := by
  letI := j.toAlgebra
  letI := i.toAlgebra
  haveI : Module.Finite L L' := hi
  let τ : L' →ₐ[L] Ω := IsAlgClosed.lift
  exact ⟨τ.toRingHom, RingHom.ext fun a => τ.commutes a⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem hkWith_iff {K L : Type} [Field K] [Field L] [Algebra c.F K] [Algebra c.F L] (φ : K →ₐ[c.F] L) {p : ℕ}
    (hp : 0 < p) {y z : FrPt Xo c K} {y' z' : FrPt Xo c L} (hy : FrMap φ y y') (hz : FrMap φ z z')
    {f : Fib Xo y.x ⟶ Fib Xo z.x} {f' : Fib Xo z.x ⟶ Fib Xo y.x} {g : Fib Xo y'.x ⟶ Fib Xo z'.x}
    {g' : Fib Xo z'.x ⟶ Fib Xo y'.x} (h : IsBC φ.toRingHom f g) (h' : IsBC φ.toRingHom f' g')
    (hR : AllRat Xo y.x (p ^ 2)) : HkWith p y z f f' ↔ HkWith p y' z' g g' := by
  have e₁ := (GlobalTheory.T.exists_fibreMap_baseChange_and_isogenyPair_iff E H Dw l Xo K L φ.toRingHom y.x z.x y'.x z'.x).2 f f' g g' (p ^ 2) h h'
  have e₂ : ∀ τ j, IsLieImageH p f.left (y.u τ j) (z.u τ j) ↔ IsLieImageH p g.left (y'.u τ j) (z'.u τ j) :=
    fun τ j => by
      rw [hy.2.1, hz.2.1]
      exact GlobalTheory.T.lie_image_compatible_with_base_change E H Dw l Xo K L φ.toRingHom y.x z.x y'.x z'.x f g p _ _ h (y.tan τ j)
  have e₃ := fun a b => GlobalTheory.T.isThetaTrace_conj_iff_of_rigIso E H Dw l Xo c K L φ y z y' z' f f' g p hp hy hz a h hR b
  constructor
  · rintro ⟨a, b, d⟩
    have ⟨β, _, _, _, _, _, hβ, _⟩ := d
    exact ⟨e₁.1 a, fun τ j => (e₂ τ j).1 (b τ j), (e₃ a ⟨β, hβ⟩).1 d⟩
  · rintro ⟨a, b, d⟩
    have ⟨β, _, _, _, _, _, hβ, _⟩ := d
    have a' := e₁.2 a
    exact ⟨a', fun τ j => (e₂ τ j).2 (b τ j),
      (e₃ a' (GlobalTheory.T.exists_isRigIso_of_baseChange' E H Dw l Xo K L φ.toRingHom y.x z.x y'.x z'.x f g _ h a'.1 ⟨β, hβ⟩)).2 d⟩

theorem allRat_up {K L : Type} [Field K] [Field L] (φ : K →+* L) {x : Sp K ⟶ Xo.X} {w : Sp L ⟶ Xo.X} {M : ℕ}
    (hM : 0 < M) (hw : w = spMap φ ≫ x) (h : AllRat Xo x M) : AllRat Xo w M :=
  hw ▸ ((torsion_rational_over_finite_extension E H Dw l Xo K x M hM).2 h).1 L φ

theorem HkOver.up {K L : Type} [Field K] [Field L] [Algebra c.F K] [Algebra c.F L] (φ : K →ₐ[c.F] L) {p : ℕ}
    (hp : 0 < p) {y z : FrPt Xo c K} {y' z' : FrPt Xo c L} (hy : FrMap φ y y') (hz : FrMap φ z z')
    (h : HkOver p y z) : HkOver p y' z' := by
  obtain ⟨h₁, h₂, f, f', h⟩ := h
  obtain ⟨g, hg⟩ := (GlobalTheory.T.exists_fibreMap_baseChange_and_isogenyPair_iff E H Dw l Xo K L φ.toRingHom y.x z.x y'.x z'.x).1 hy.1 hz.1 f
  obtain ⟨g', hg'⟩ := (GlobalTheory.T.exists_fibreMap_baseChange_and_isogenyPair_iff E H Dw l Xo K L φ.toRingHom z.x y.x z'.x y'.x).1 hz.1 hy.1 f'
  exact ⟨allRat_up _ (pow_pos hp _) hy.1 h₁, allRat_up _ (pow_pos hp _) hz.1 h₂, g, g',
    (hkWith_iff φ hp hy hz hg hg' h₁).1 h⟩

theorem exists_hkOver {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed Ω] [Algebra c.F K] [Algebra c.F Ω]
    (k : K →ₐ[c.F] Ω) (hk : k.toRingHom.IsIntegral) {p : ℕ} (hp : 0 < p) {y : FrPt Xo c K} {w z : FrPt Xo c Ω}
    (hw : FrMap k y w) (h : ∃ g g', HkWith p w z g g') :
    ∃ (L : Type) (_ : Field L) (_ : Algebra c.F L) (i : K →ₐ[c.F] L) (j : L →ₐ[c.F] Ω) (y' z' : FrPt Xo c L),
      j.comp i = k ∧ i.toRingHom.Finite ∧ FrMap i y y' ∧ FrMap j z' z ∧ HkOver p y' z' := by
  obtain ⟨g, g', h⟩ := h
  obtain ⟨L₁, _, _, i₁, j₁, z₁, e₁, f₁, hz₁⟩ := GlobalTheory.T.framedPoint_descends_finite_subextension E H Dw l Xo c K Ω k z hk
  obtain ⟨y₁, hy₁⟩ := exists_frMap i₁ y
  have hw₁ : FrMap j₁ y₁ w := frMap_of_comp hy₁ hw fun a => DFunLike.congr_fun e₁ a
  obtain ⟨L₂, _, _, f₂, r₂⟩ := (torsion_rational_over_finite_extension E H Dw l Xo L₁ y₁.x _ (pow_pos hp 2)).1
  obtain ⟨L₃, _, _, f₃, r₃⟩ := (torsion_rational_over_finite_extension E H Dw l Xo L₂
    (spMap (algebraMap L₁ L₂) ≫ z₁.x) _ (pow_pos hp 3)).1
  let a : L₁ →+* L₃ := (algebraMap L₂ L₃).comp (algebraMap L₁ L₂)
  have fa : a.Finite := (RingHom.finite_algebraMap.2 f₃).comp (RingHom.finite_algebraMap.2 f₂)
  obtain ⟨j₃, e₃⟩ := exists_lift j₁.toRingHom a fa
  have hint : j₃.IsIntegral := by
    refine RingHom.IsIntegral.tower_top (a.comp i₁.toRingHom) j₃ ?_
    rw [← RingHom.comp_assoc, e₃]
    subst e₁
    exact hk
  have sq : ∀ x : Sp L₁ ⟶ Xo.X, spMap j₁.toRingHom ≫ x = spMap j₃ ≫ spMap a ≫ x := fun x => by
    rw [← Category.assoc, TorsionRat.sp_comp, e₃]
  obtain ⟨M, _, i₄, j₄, e₄, f₄, hM⟩ := GlobalTheory.T.fibreIsogenyPair_defined_over_finite_subextension E H Dw l Xo L₃ Ω j₃ (spMap a ≫ y₁.x) (spMap a ≫ z₁.x) w.x z.x g g'
    hint (hw₁.1.trans (sq _)) (hz₁.1.trans (sq _)) h.1.1 h.1.2.1
  letI : Algebra c.F M := ((i₄.comp a).comp (algebraMap c.F L₁)).toAlgebra
  let b : L₁ →ₐ[c.F] M := ⟨i₄.comp a, fun _ => rfl⟩
  have eb : ∀ u, j₄ (b u) = j₁ u := fun u =>
    (DFunLike.congr_fun e₄ (a u)).trans (DFunLike.congr_fun e₃ u)
  let j : M →ₐ[c.F] Ω := ⟨j₄, fun u => (eb _).trans (j₁.commutes u)⟩
  obtain ⟨y', hy'⟩ := exists_frMap b y₁
  obtain ⟨z', hz'⟩ := exists_frMap b z₁
  have sq' : ∀ x : Sp L₁ ⟶ Xo.X, spMap b.toRingHom ≫ x = spMap i₄ ≫ spMap a ≫ x := fun x => by
    rw [← Category.assoc, TorsionRat.sp_comp]
  obtain ⟨f, f', hf, hf'⟩ := hM y'.x z'.x (hy'.1.trans (sq' _)) (hz'.1.trans (sq' _))
  have hyw : FrMap j y' w := frMap_of_comp hy' hw₁ eb
  have hzz : FrMap j z' z := frMap_of_comp hz' hz₁ eb
  have R₁ : AllRat Xo y'.x (p ^ 2) := allRat_up (i₄.comp (algebraMap L₂ L₃)) (pow_pos hp _)
    (hy'.1.trans (by rw [← Category.assoc, TorsionRat.sp_comp])) r₂
  have R₂ : AllRat Xo z'.x (p ^ 3) := allRat_up i₄ (pow_pos hp _)
    (hz'.1.trans (by rw [← Category.assoc, ← Category.assoc, TorsionRat.sp_comp, TorsionRat.sp_comp])) r₃
  refine ⟨M, inferInstance, inferInstance, b.comp i₁, j, y', z', AlgHom.ext fun u => (eb _).trans
    (DFunLike.congr_fun e₁ u), (f₄.comp fa).comp f₁, frMap_comp hy₁ hy' fun _ => rfl, hzz, R₁, R₂, f, f',
    (hkWith_iff j hp hyw hzz hf hf' R₁).2 h⟩

theorem frBor_reduce {S : Type} [CommRing S] [Algebra c.F S] {y z : FrPt Xo c S} {t : Ix Dw → Sˣ}
    (hb : FrBor t y z) : ∃ u tan eig basis s gen, z = ⟨y.x, y.x_over, u, tan, eig, basis, s, gen⟩ ∧
      ∀ i, s.f i = scal y.x (t none : S) i * y.s.f i := by
  obtain ⟨x, xo, u, tan, eig, basis, s, gen⟩ := z
  obtain ⟨hx, -, pm, h₁, h₂, h₃⟩ := hb
  dsimp only at hx
  subst hx
  obtain rfl : pm = 𝟙 _ := gx_ext (h₂.trans (Category.id_comp _).symm) (h₁.trans (Category.id_comp _).symm)
  refine ⟨u, tan, eig, basis, s, gen, rfl, fun i => ?_⟩
  have e : Scheme.Hom.appLE (𝟙 (Gx y.x)) ((PPx y.x).U i) ((PPx y.x).U i) le_rfl = 𝟙 _ := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact (Category.id_comp _).trans (CategoryTheory.Functor.map_id _ _)
  have := h₃ i le_rfl
  rw [e] at this
  exact this.symm

theorem frBor_map {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S} {z z' : FrPt Xo c T} (h : FrBor t y y')
    (hz : FrMap φ y z) (hz' : FrMap φ y' z') : FrBor (fun i => Units.map (φ : S →* T) (t i)) z z' := by
  obtain ⟨g, hg2, hg1, hg⟩ := (GlobalTheory.Frames.frBor_iff_frChg y y' t).1 h
  have hc := (frMap_iff_frChg hg hz).1 hz'
  exact (GlobalTheory.Frames.frBor_iff_frChg z z' _).2
    ⟨fun τ => (g τ).map φ, fun τ i j hij => by simp [hg2 τ i j hij], fun τ i => by simp [hg1], hc⟩

section Theta

variable {T : CDVR} {io : c.F →+* T.Fr} {p : ℕ}

theorem theta_low (hp : IsUnit (p : T.V)) (y y' : IntFr Xo c T io)
    (hU : ∀ I : IntData Xo c T io y.1, ∃ P : PELUnif (IsLocalRing.maximalIdeal T.V) I.G, P.TorsionIso) :
    letI := io.toAlgebra
    ∀ (z : FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), HkOver p y.1 z → FrBor t y'.1 z →
      (t none : T.Fr) ∈ Set.range (algebraMap T.V T.Fr) := by
  letI := io.toAlgebra
  intro z t h hb
  obtain ⟨u, tan, eig, basis, s, gen, rfl, hs⟩ := frBor_reduce hb
  obtain ⟨-, -, f, f', hP, -, hT⟩ := h
  obtain ⟨I⟩ := (GlobalTheory.IntegralData.integralIff E H Dw l Xo c T io y.1).1 y.2.2
  obtain ⟨I'⟩ := (GlobalTheory.IntegralData.integralIff E H Dw l Xo c T io y'.1).1 y'.2.2
  obtain ⟨F, F', a₁, a₂, a₃, -, -, a₄, -⟩ :=
    GlobalTheory.T.exists_ext_pair_alt E H Dw l Xo T _ _ I.G I'.G I.t' I'.t' I.m1 I.m2 I'.m1 I'.m2 f f' hP.1 hP.2.1
  obtain ⟨w, w₁, w₂⟩ := GlobalTheory.T.exists_pull_isTranslSum_of_isThetaTrace E H Dw l Xo T.Fr _ _ f f' p y.1.s y'.1.s s _ hP hs hT
  exact GlobalTheory.T.integral_scalar_of_pulledBack_generator_extends_model E H Dw l Xo c T io y y' I I' f F F' (p ^ 2) p _ w a₁ a₂ a₃ (a₄ _ hP.2.2.2.1)
    (by rw [Nat.cast_pow]; exact hp.pow 2) w₁ (GlobalTheory.T.sum_symmetricTranslates_thetaPullback_extends E H Dw l Xo c T io y I p w (hU I) hp w₂)

theorem theta_high (hpp : p.Prime) (hp : IsUnit (p : T.V)) (y y' : IntFr Xo c T io)
    (hU : ∀ I : IntData Xo c T io y'.1, ∃ P : PELUnif (IsLocalRing.maximalIdeal T.V) I.G, P.TorsionIso) :
    letI := io.toAlgebra
    ∀ (z : FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), HkOver p y.1 z → FrBor t y'.1 z →
      vV T.V (t none : T.Fr) ≤ 0 := by
  letI := io.toAlgebra
  intro z t h hb
  obtain ⟨u, tan, eig, basis, s, gen, rfl, hs⟩ := frBor_reduce hb
  obtain ⟨-, hR, f, f', hP, -, hT⟩ := h
  obtain ⟨I⟩ := (GlobalTheory.IntegralData.integralIff E H Dw l Xo c T io y.1).1 y.2.2
  obtain ⟨I'⟩ := (GlobalTheory.IntegralData.integralIff E H Dw l Xo c T io y'.1).1 y'.2.2
  obtain ⟨b, ζ, m, hζ, hab, f₂, hf₂, hff, w, w₁, w₂⟩ :=
    GlobalTheory.T.exists_orth_pull_isTranslSum_of_isThetaTrace E H Dw l Xo T.Fr _ _ f f' p y.1.s y'.1.s s _ hpp hP hR (t none).ne_zero hs hT
  obtain ⟨F, F', a₁, a₂, -, a₃, a₄, -⟩ :=
    GlobalTheory.T.exists_ext_pair_alt E H Dw l Xo T _ _ I.G I'.G I.t' I'.t' I.m1 I.m2 I'.m1 I'.m2 f f₂ hP.1 hf₂
  obtain ⟨b₀, rfl⟩ := GlobalTheory.T.integral_scalar_of_pulledBack_generator_extends_model E H Dw l Xo c T io y' y I' I f₂ F' F (p ^ 3) (p ^ 2) b w a₂ a₁ a₃ (a₄ _ hff)
    (by rw [Nat.cast_pow]; exact hp.pow 3) w₁
    (GlobalTheory.T.sum_symmetricTranslates_thetaPullback_extends E H Dw l Xo c T io y' I' (p ^ 2) w (hU I') (by rw [Nat.cast_pow]; exact hp.pow 2) w₂)
  have hζ0 : ζ ≠ 0 := fun h => by simp [h, hpp.ne_zero] at hζ
  have hp0 : (p : T.Fr) ≠ 0 := by simpa using (hp.map (algebraMap T.V T.Fr)).ne_zero
  have vp : vV T.V (p : T.Fr) = 0 := by
    simpa using GlobalTheory.IntegralFrameCheck.vV_map_unit (V := T.V) (V' := T.V) (RingHom.id T.Fr) (fun a => ⟨a, rfl⟩) hp.unit
  have vζ : vV T.V ζ = 0 := by
    have := GlobalTheory.IntegralFrameCheck.vV_pow (V := T.V) hζ0 p
    rw [hζ, GlobalTheory.IntegralFrameCheck.vV_one] at this
    exact (mul_eq_zero.1 this.symm).resolve_left (by exact_mod_cast hpp.ne_zero)
  have hb0 : algebraMap T.V T.Fr b₀ ≠ 0 := fun h => by
    rw [h, mul_zero] at hab
    exact mul_ne_zero (pow_ne_zero _ hp0) hζ0 hab.symm
  have e := congrArg (vV T.V) hab
  rw [vV_mul (t none).ne_zero hb0, vV_mul (pow_ne_zero _ hp0) hζ0, GlobalTheory.IntegralFrameCheck.vV_pow hp0, vp, vζ] at e
  have := GlobalTheory.IntegralFrameCheck.vV_algebraMap_nonneg (K' := T.Fr) b₀
  omega

theorem isUnit_natCast_up {T' : CDVR} (hp : IsUnit (p : T.V)) (i : T.Fr →+* T'.Fr) {r : ℕ}
    (hi : ∀ a : T.Fr, a ≠ 0 → vV T'.V (i a) = (r : ℤ) * vV T.V a) : IsUnit (p : T'.V) := by
  have hu : (algebraMap T.V T.Fr (hp.unit⁻¹ : T.Vˣ)) ≠ 0 := ((hp.unit⁻¹).isUnit.map _).ne_zero
  obtain ⟨b, hb⟩ := Formalism.L2.PjFree.mem_range_of_vV_nonneg (V := T'.V) (x := i (algebraMap T.V T.Fr (hp.unit⁻¹ : T.Vˣ)))
    (by rw [hi _ hu]; exact mul_nonneg (Int.natCast_nonneg _) (GlobalTheory.IntegralFrameCheck.vV_algebraMap_nonneg _))
  refine IsUnit.of_mul_eq_one b (IsFractionRing.injective T'.V T'.Fr ?_)
  rw [map_mul, hb, map_natCast, ← map_natCast (i.comp (algebraMap T.V T.Fr)), RingHom.comp_apply, ← map_mul,
    ← map_mul, hp.mul_val_inv, map_one, map_one, map_one]

theorem exists_intFr_up {T' : CDVR} {io' : c.F →+* T'.Fr} {e : ℕ} (he : 0 < e) :
    letI := io.toAlgebra; letI := io'.toAlgebra
    ∀ (φ : T.Fr →ₐ[c.F] T'.Fr), (∀ a : T.Fr, a ≠ 0 → vV T'.V (φ a) = (e : ℤ) * vV T.V a) →
      ∀ w : IntFr Xo c T io, ∃ w' : IntFr Xo c T' io', FrMap φ w.1 w'.1 := by
  letI := io.toAlgebra
  have key : ∀ (i : T.Fr →+* T'.Fr), io' = i.comp io → letI := io'.toAlgebra
      ∀ (φ : T.Fr →ₐ[c.F] T'.Fr), φ.toRingHom = i → (∀ a : T.Fr, a ≠ 0 → vV T'.V (i a) = (e : ℤ) * vV T.V a) →
      ∀ w : IntFr Xo c T io, ∃ w' : IntFr Xo c T' io', FrMap φ w.1 w'.1 := by
    rintro i rfl φ hφ hv w
    obtain ⟨w', ψ, hψ, hm⟩ := GlobalTheory.IntFrBaseChange.exists_intFr_baseChange E H Dw l Xo c T T' io w i e he hv
    letI := (i.comp io).toAlgebra
    obtain rfl : ψ = φ := AlgHom.coe_ringHom_injective (hψ.trans hφ.symm)
    exact ⟨w', hm⟩
  letI := io'.toAlgebra
  exact fun φ hφ => key φ.toRingHom (RingHom.ext fun a => (φ.commutes a).symm) φ rfl hφ

theorem theta_unit (hpp : p.Prime) (hp : IsUnit (p : T.V)) (hT : T.FinRes) (y y' : IntFr Xo c T io) :
    letI := io.toAlgebra
    ∀ (z : FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), HkOver p y.1 z → FrBor t y'.1 z →
      vV T.V (t none : T.Fr) = 0 := by
  letI := io.toAlgebra
  intro z t h hb
  apply le_antisymm
  · obtain ⟨T', io', y₁', e, -, he, hU, φ, hφ, hm'⟩ :=
      GlobalTheory.IntegralPull.exists_ext_all_models_uniformised E H Dw l Xo c T io y' hT
    letI := io'.toAlgebra
    obtain ⟨y₁, hm⟩ := exists_intFr_up he φ hφ y
    obtain ⟨z₁, hz⟩ := exists_frMap φ z
    have := theta_high hpp (isUnit_natCast_up hp φ.toRingHom hφ) y₁ y₁' hU z₁ _ (h.up φ hpp.pos hm hz)
      (frBor_map φ hb hm' hz)
    have e₁ : vV T'.V (φ (t none)) ≤ 0 := this
    rw [hφ _ (t none).ne_zero] at e₁
    exact nonpos_of_mul_nonpos_right e₁ (by exact_mod_cast he)
  · obtain ⟨T', io', y₁, e, -, he, hU, φ, hφ, hm⟩ :=
      GlobalTheory.IntegralPull.exists_ext_all_models_uniformised E H Dw l Xo c T io y hT
    letI := io'.toAlgebra
    obtain ⟨y₁', hm'⟩ := exists_intFr_up he φ hφ y'
    obtain ⟨z₁, hz⟩ := exists_frMap φ z
    obtain ⟨b, hb'⟩ := theta_low (isUnit_natCast_up hp φ.toRingHom hφ) y₁ y₁' hU z₁ _ (h.up φ hpp.pos hm hz)
      (frBor_map φ hb hm' hz)
    have e₁ : 0 ≤ vV T'.V (φ (t none)) := by
      have := GlobalTheory.IntegralFrameCheck.vV_algebraMap_nonneg (K' := T'.Fr) b
      rwa [hb'] at this
    rw [hφ _ (t none).ne_zero] at e₁
    exact nonneg_of_mul_nonneg_right e₁ (by exact_mod_cast he)

end Theta

section Frame

variable {T : CDVR} {io : c.F →+* T.Fr} {p : ℕ}

theorem exists_unit_of_vV {a : T.Frˣ} (h : vV T.V (a : T.Fr) = 0) : ∃ u : T.Vˣ, algebraMap T.V T.Fr u = a := by
  obtain ⟨b, hb⟩ := Formalism.L2.PjFree.mem_range_of_vV_nonneg h.ge
  have h' := vV_mul (V := T.V) a.ne_zero a⁻¹.ne_zero
  rw [Units.mul_inv, GlobalTheory.IntegralFrameCheck.vV_one, h, zero_add] at h'
  obtain ⟨b', hb'⟩ := Formalism.L2.PjFree.mem_range_of_vV_nonneg h'.le
  have e : b * b' = 1 := IsFractionRing.injective T.V T.Fr (by rw [map_mul, hb, hb', Units.mul_inv, map_one])
  exact ⟨Units.mkOfMulEqOne b b' e, hb⟩

theorem exists_frBor_unit (hpp : p.Prime) (hp : IsUnit (p : T.V)) (hT : T.FinRes) (y y₀ : IntFr Xo c T io) :
    letI := io.toAlgebra
    ∀ z : FrPt Xo c T.Fr, z.x = y₀.1.x → HkOver p y.1 z →
      ∃ (y' : IntFr Xo c T io) (u : Ix Dw → T.Vˣ), (GlobalTheory.GoodPts.Good y → GlobalTheory.GoodPts.Good y') ∧
        FrBor (fun a => Units.map (algebraMap T.V T.Fr).toMonoidHom (u a)) y'.1 z := by
  letI := io.toAlgebra
  intro z hx h
  obtain ⟨x, xo, u, tan, eig, basis, s, gen⟩ := z
  dsimp only at hx
  subst hx
  have ⟨_, _, f, f', hP, hL, _⟩ := h
  obtain ⟨I⟩ := (GlobalTheory.IntegralData.integralIff E H Dw l Xo c T io y.1).1 y.2.2
  obtain ⟨I'⟩ := (GlobalTheory.IntegralData.integralIff E H Dw l Xo c T io y₀.1).1 y₀.2.2
  obtain ⟨F, F', a₁, a₂, a₃, -, a₄, a₅, a₆, a₇⟩ :=
    GlobalTheory.T.exists_ext_pair_alt E H Dw l Xo T _ _ I.G I'.G I.t' I'.t' I.m1 I.m2 I'.m1 I'.m2 f f' hP.1 hP.2.1
  obtain ⟨k, hk, hc⟩ := GlobalTheory.T.lieLattice_onto_of_monHom_pair_pow_p_sq E H Dw l Xo c T io y y₀ I I' f F F' p u hp a₁ a₂ a₃ (a₄ _ hP.2.2.1) (a₅ _ hP.2.2.2.1)
    (a₆ hP.2.2.2.2.1) (a₇ hP.2.2.2.2.2) hL
  obtain ⟨y', -, hx, hu, -⟩ := GlobalTheory.IntRebase.intRebase GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c T io y₀
    ⟨_, xo, u, tan, eig, basis, s, gen⟩ rfl k hk
  have hu' : ∀ τ i, u τ i = y'.1.u τ i := fun τ i => Formalism.L2.PjFree.isCombAt_unique (hc τ i) (hu τ i)
  have hs : ∀ τ i, IsCombAt y'.1.x (y'.1.u τ) (Pi.single i 1) (u τ i) := fun τ i =>
    hu' τ i ▸ Formalism.L2.PjFree.isCombAt_single (y'.1.tan τ) i
  obtain ⟨t, ht⟩ := (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c T.Fr y'.1 ⟨_, xo, u, tan, eig, basis, s, gen⟩ y'.1).2.1
    hx.symm fun τ i => ⟨Pi.single i 1, by simp, fun j hj => Pi.single_eq_of_ne hj.ne' _,
      hs τ i⟩
  obtain ⟨u₀, hu₀⟩ := exists_unit_of_vV (theta_unit hpp hp hT y y' _ t h ht)
  refine ⟨y', fun a => Option.elim a u₀ fun _ => 1, ?_, ht.1, fun τ i => ⟨Pi.single i 1, by simp,
    fun j hj => Pi.single_eq_of_ne hj.ne' _, hs τ i⟩, ?_⟩
  · rintro ⟨G, t₁, m₁, m₂, hG⟩
    obtain ⟨F₁, -, -, -, b₁, -⟩ := GlobalTheory.T.exists_ext_pair_alt E H Dw l Xo T _ _ G I'.G t₁ I'.t' m₁ m₂ I'.m1 I'.m2 f f' hP.1 hP.2.1
    exact ⟨I'.G, I'.t', hx ▸ I'.m1, I'.m2, GlobalTheory.T.isProper_model_of_extends_fibreIsogeny E H Dw l Xo T _ _ G I'.G t₁ I'.t' m₁ m₂ I'.m1 I'.m2 f f' F₁ _ b₁
      hP.2.2.2.1 (pow_pos hpp.pos 2) hG⟩
  · have := ht.2.2
    rw [← hu₀] at this
    exact this

end Frame

theorem intFrExt (Xo : Moduli Dw l) (c : Coeff l) : IntFrExt Xo c :=
  (Nat.eq_zero_or_pos (Dw.p + Dw.q)).elim (GlobalTheory.T.integralFrameExtension_of_rank_zero_signature E H Dw l Xo c) (GlobalTheory.T.moduliPoint_integralFrame_after_finiteExtension E H Dw l Xo c)

theorem heckeFrameInt (cls : PtClass Xo c)
    (hcls : ∀ T io y T' io' y', cls T io y → (GlobalTheory.GoodPts.Good y → GlobalTheory.GoodPts.Good y') → cls T' io' y') :
    HeckeFrameInt Xo c cls := by
  intro la P p n hP hla T io e ho y hy hc Ω _ _ _
  letI := io.toAlgebra
  intro k hk w hw C z hz
  have hpp : p.Prime := hP.2.2.1
  have hk' : k.toRingHom.IsIntegral := by
    letI := k.toRingHom.toAlgebra
    haveI := hk
    exact fun a => Algebra.IsIntegral.isIntegral (R := T.Fr) a
  obtain ⟨L, _, _, i₁, j₁, y₁, z₁, e₁, f₁, hy₁, hz₁, h₁⟩ :=
    exists_hkOver k hk' hpp.pos hw (GlobalTheory.T.exists_linear_heckeIsogeny_inverse_up_to_p_sq E H Dw l Xo c P p n hP Ω w C z hz)
  obtain ⟨T₁, iT, r₁, ψ, hr₁, hv₁, hψ, hT₁⟩ : ∃ (T₁ : CDVR) (iT : T.Fr →+* T₁.Fr) (r : ℕ) (ψ : L ≃+* T₁.Fr), 0 < r ∧
      (∀ a : T.Fr, vV T₁.V (iT a) = (r : ℤ) * vV T.V a) ∧ (∀ a, ψ (i₁ a) = iT a) ∧ T₁.FinRes := by
    letI := i₁.toRingHom.toAlgebra
    haveI : FiniteDimensional T.Fr L := f₁
    obtain ⟨T₁, iT, r, ψ, -, a, b, d, -, g⟩ := GlobalTheory.PlaceExtField.exists_cdvr_finite_extension T L
    exact ⟨T₁, iT, r, ψ, a, b, d, g hy⟩
  obtain ⟨T₂, i₂, r₂, hr₂, hv₂, hT₂, y₀, hx₀⟩ := intFrExt Xo c T₁ (iT.comp io) hT₁ (spMap ψ.toRingHom ≫ z₁.x) (by
    rw [Category.assoc, z₁.x_over, sOf, sOf, TorsionRat.sp_comp]
    congr 1
    refine RingHom.ext fun a => ?_
    exact (congrArg ψ (i₁.commutes _).symm).trans (hψ _))
  let i : T.Fr →+* T₂.Fr := i₂.comp iT
  have hv : ∀ a, vV T₂.V (i a) = ((r₂ * r₁ : ℕ) : ℤ) * vV T.V a := fun a => by
    rw [RingHom.comp_apply, hv₂, hv₁, Nat.cast_mul, _root_.mul_assoc]
  have hr : 0 < r₂ * r₁ := Nat.mul_pos hr₂ hr₁
  obtain ⟨j, hj⟩ := exists_lift (j₁.toRingHom.comp ψ.symm.toRingHom) i₂ (GlobalTheory.T.ringHom_finite_and_isIntegral_of_valuation_scaled T₁ T₂ i₂ r₂ hr₂ hv₂ hT₂).1
  have hj' : ∀ a : L, j (i₂ (ψ a)) = j₁ a := fun a => by simpa using DFunLike.congr_fun hj (ψ a)
  letI := (i.comp io).toAlgebra
  let b : L →ₐ[c.F] T₂.Fr := ⟨i₂.comp ψ.toRingHom, fun a =>
    congrArg i₂ ((congrArg ψ (i₁.commutes a).symm).trans (hψ _))⟩
  let φ : T.Fr →ₐ[c.F] T₂.Fr := ⟨i, fun _ => rfl⟩
  have hφ : ∀ a, b (i₁ a) = φ a := fun a => congrArg i₂ (hψ a)
  have hjk : ∀ a, j (i a) = k a := fun a =>
    (congrArg j (hφ a).symm).trans ((hj' _).trans (DFunLike.congr_fun e₁ a))
  let J : T₂.Fr →ₐ[c.F] Ω := ⟨j, fun a => (hjk _).trans (k.commutes a)⟩
  obtain ⟨y₂, hy₂⟩ := exists_intFr_up (io' := i.comp io) hr φ (fun a _ => hv a) y
  obtain ⟨z₂, hz₂⟩ := exists_frMap b z₁
  obtain ⟨y', u, hg, hb⟩ := exists_frBor_unit (io := i.comp io) hpp
    (isUnit_natCast_up (PullbackSections.isUnit_natCast_of_overLa T ho hla) i fun a _ => hv a) hT₂ y₂ y₀ z₂
    (hz₂.1.trans (hx₀.trans (by rw [← Category.assoc, TorsionRat.sp_comp])).symm)
    (h₁.up b hpp.pos (frMap_of_comp hy₁ hy₂ hφ) hz₂)
  obtain ⟨w', hw'⟩ := exists_frMap J y'.1
  refine ⟨T₂, i, ⟨(GlobalTheory.T.ringHom_finite_and_isIntegral_of_valuation_scaled T T₂ i _ hr hv hT₂).1, _, hr, hv⟩, J, RingHom.ext hjk, y', hT₂,
    hcls T io y T₂ _ y' hc fun h => hg (GlobalTheory.T.goodReduction_stable_valuationRing_extension E H Dw l Xo c T T₂ io _ y y₂ i _ hr hv hy₂.1 h), w', u, hw', ?_⟩
  exact frBor_map J hb hw' (frMap_of_comp hz₂ hz₁ hj')

theorem heckeValueInt (cls : PtClass Xo c) (h : HeckeFrameInt Xo c cls) : HeckeValueInt Xo c cls := by
  intro la P p n hP hla T io e ho y hy hc Ω _ _ _
  letI := io.toAlgebra
  intro k hk w hw C z hz
  refine ⟨fromTest_of_isLocalRing z, fun a m f hf hv => ?_⟩
  obtain ⟨T', i, ⟨-, r, hr, hi⟩, j, hj, y', hy', -, w', u, hw', hb⟩ :=
    h la P p n hP hla T io e ho y hy hc Ω k hk w hw C z hz
  letI := (i.comp io).toAlgebra
  have h0 : 0 ≤ nval T'.V (r * e) (evI y' f) := hv _ ⟨PtV.mk la (ho.bc i hr hi) y' hy' () trivial, rfl⟩
  obtain ⟨b, hb'⟩ : evI y' f ∈ Set.range (algebraMap T'.V T'.Fr) := by
    by_cases hx : evI y' f = 0
    · exact ⟨0, by rw [hx, map_zero]⟩
    refine Formalism.L2.PjFree.mem_range_of_vV_nonneg ?_
    rw [nval_of_ne hx, EReal.coe_nonneg, le_div_iff₀ (by exact_mod_cast Nat.mul_pos hr ho.1), zero_mul] at h0
    exact_mod_cast h0
  have e₁ := (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 Ω inferInstance
    a m f hf _ w' z hb
  have e₂ : evR Xo c f w' = j (algebraMap T'.V T'.Fr b) := (evR_frMap hf.1 hw').trans (congrArg j hb'.symm)
  have e₃ : evR Xo c f z = j (algebraMap T'.V T'.Fr (wchar (ex Dw a m) u * b)) := by
    rw [e₁, e₂, map_mul, map_mul]
    congr 1
    simp [wchar]
  obtain ⟨q, hq, hq'⟩ := (GlobalTheory.T.ringHom_finite_and_isIntegral_of_valuation_scaled T T' i r hr hi hy').2 (wchar (ex Dw a m) u * b)
  refine ⟨q, hq, ?_⟩
  rw [e₃, ← hj, RingHom.comp_assoc]
  exact (Polynomial.hom_eval₂ q _ j.toRingHom _).symm.trans ((congrArg j.toRingHom hq').trans (map_zero _))

theorem heckeInt : HeckeInt := fun _ _ _ _ _ _ _ Xo c =>
  have g : HeckeFrameInt Xo c (goodCls Xo c) := heckeFrameInt _ fun _ _ _ _ _ _ a b => b a
  have a : HeckeFrameInt Xo c (GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.trivialClassCondition Xo c) := heckeFrameInt _ fun _ _ _ _ _ _ _ _ => trivial
  ⟨⟨g, heckeValueInt _ g⟩, a, heckeValueInt _ a⟩

end GlobalTheory.HkIntegral
end
end
