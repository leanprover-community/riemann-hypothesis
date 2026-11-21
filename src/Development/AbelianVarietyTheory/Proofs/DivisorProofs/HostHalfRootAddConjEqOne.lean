import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasWitness
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnFibLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrMoveValues
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolPairA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreUnitFrameUniformisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApplyPvNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsObjMapPhi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnFibFrEqOfExLeftEq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MarkedLatticeIsometryDoubleCosetMove
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.OrthonormalBaseFrameNeg
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsTestRingInjective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecValuesComplexFibreAbelianScheme
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.VtFrRdA
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EpsPtScaleZero
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.InputExistsOfMemberExists
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FramedPointGeneratorIsThetaLevelOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CastFrMemDom
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelOneThetaEqSmulOfSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaMultiplierUnitary
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NegBaseElementImNegBaseEmbedding

section
open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000

namespace GlobalTheory.AnMove

open GlobalTheory.Dict.Lift
open scoped MonObj

theorem exists_push_frame {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {Y : Scheme.{0}} {L : LB Y}
    (hL : L.IsLB) (φ : Y ⟶ Y) (O : L.ι → L.ι → Y.Opens) (ω : ∀ i j, Γ(Y, O i j))
    (hO : ∀ i j (p : Sp ℂ ⟶ Y), ⊤ ≤ p ⁻¹ᵁ O i j ↔ (⊤ ≤ (p ≫ φ) ⁻¹ᵁ L.U i ∧ ⊤ ≤ p ⁻¹ᵁ L.U j))
    (hne : ∀ i j (p : Sp ℂ ⟶ Y), ⊤ ≤ p ⁻¹ᵁ O i j → valAt' p (O i j) (ω i j) ≠ 0)
    (hg : ∀ i j i' j' (p : Sp ℂ ⟶ Y), ⊤ ≤ p ⁻¹ᵁ O i j → ⊤ ≤ p ⁻¹ᵁ O i' j' →
      valAt' p (O i j) (ω i j) * valAt' p (L.U j ⊓ L.U j') (L.g j j').val =
        valAt' (p ≫ φ) (L.U i ⊓ L.U i') (L.g i i').val * valAt' p (O i' j') (ω i' j'))
    (e : V → (Sp ℂ ⟶ Y)) (hol : IsHolTo Set.univ e) (fr : L.ι → V → ℂ)
    (fr_hol : ∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ e z ⁻¹ᵁ L.U j})
    (fr_ne : ∀ j z, ⊤ ≤ e z ⁻¹ᵁ L.U j → fr j z ≠ 0)
    (fr_g : ∀ j j' z, ⊤ ≤ e z ⁻¹ᵁ (L.U j ⊓ L.U j') →
      fr j z = valAt' (e z) (L.U j ⊓ L.U j') (L.g j j').val * fr j' z) :
    ∃ fr' : L.ι → V → ℂ, (∀ i, DifferentiableOn ℂ (fr' i) {z | ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U i}) ∧
      (∀ i z, ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U i → fr' i z ≠ 0) ∧
      (∀ i i' z, ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ (L.U i ⊓ L.U i') →
        fr' i z = valAt' (e z ≫ φ) (L.U i ⊓ L.U i') (L.g i i').val * fr' i' z) ∧
      ∀ i j z, ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U i → ⊤ ≤ e z ⁻¹ᵁ L.U j →
        fr' i z = valAt' (e z) (O i j) (ω i j) * fr j z := by
  choose ch hch using fun z => exists_chart (e z) L hL
  have key : ∀ i j z, ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U i → ⊤ ≤ e z ⁻¹ᵁ L.U j →
      valAt' (e z) (O i (ch z)) (ω i (ch z)) * fr (ch z) z = valAt' (e z) (O i j) (ω i j) * fr j z := by
    intro i j z hi hj
    have h1 := hg i (ch z) i j (e z) ((hO _ _ _).2 ⟨hi, hch z⟩) ((hO _ _ _).2 ⟨hi, hj⟩)
    rw [val_g_self _ L hL i hi, _root_.one_mul] at h1
    rw [fr_g (ch z) j z ((top_le_preimage_inf _ _ _).2 ⟨hch z, hj⟩), ← mul_assoc, h1]
  refine ⟨fun i z => valAt' (e z) (O i (ch z)) (ω i (ch z)) * fr (ch z) z, fun i z₀ hz₀ => ?_, fun i z hi => ?_,
    fun i i' z h => ?_, key⟩
  · have hN := hol (O i (ch z₀)) (ω i (ch z₀))
    have hm := hN.1.mem_nhds (x := z₀) ⟨trivial, (hO _ _ _).2 ⟨hz₀, hch z₀⟩⟩
    have d1 : DifferentiableAt ℂ (fr (ch z₀)) z₀ :=
      (fr_hol (ch z₀)).differentiableAt (Filter.mem_of_superset hm fun z hz => ((hO _ _ _).1 hz.2).2)
    have d2 : DifferentiableAt ℂ (fun z => valAt' (e z) (O i (ch z₀)) (ω i (ch z₀))) z₀ := hN.2.differentiableAt hm
    refine ((d2.mul d1).congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hm] with z hz
    exact key i (ch z₀) z ((hO _ _ _).1 hz.2).1 ((hO _ _ _).1 hz.2).2
  · exact mul_ne_zero (hne _ _ _ ((hO _ _ _).2 ⟨hi, hch z⟩)) (fr_ne _ z (hch z))
  · obtain ⟨hi, hi'⟩ := (top_le_preimage_inf _ _ _).1 h
    have h1 := hg i (ch z) i' (ch z) (e z) ((hO _ _ _).2 ⟨hi, hch z⟩) ((hO _ _ _).2 ⟨hi', hch z⟩)
    rw [val_g_self _ L hL _ (hch z), _root_.mul_one] at h1
    simp only []
    rw [h1, mul_assoc]

theorem anFib_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y y' : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ gM gA : Dw.La →ₗ[𝓞 E] Dw.La, levR (gM, gA) y y' → ∃ A' : AnFib X bas idx e x L y', (∀ θ, A.Reads 1 y.s θ → A'.Reads 1 y'.s θ) ∧ ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), A.Marked mk → A'.Marked (mk ∘ₗ gM) := by
  intro E _ _ _ H Dw l Xo c inst r g X bas idx e x L y y' A hsym hx hL gM gA hR
  obtain ⟨σ, rfl⟩ : ∃ σ : c.F →+* ℂ, inst = σ.toAlgebra :=
    ⟨algebraMap c.F ℂ, Algebra.algebra_ext _ _ fun _ => rfl⟩
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨ρ, ν, -, ⟨-, heta, -⟩, hmv⟩ := hR
  obtain ⟨O, ω, hO, hne, hg, hrig, hs⟩ := GlobalTheory.MoveValues.frMove_values E H Dw l Xo c σ ρ ν y y' hmv
  obtain ⟨hb, hu, -⟩ := hmv
  obtain ⟨Φ, hΦ⟩ := exists_mulEquiv ν.cart y.x y'.x hb.symm
  let ex : (Fin g → ℂ) → (ptO Xo y'.x ⟶ Xo.univ.t.G) := fun z => Φ (A.ex z)
  have hex : ∀ z, (ex z).left = (A.ex z).left ≫ ν.φ := fun z => hΦ _
  have hexf : (fun z => (ex z).left) = fun z => (A.ex z).left ≫ ν.φ := funext hex
  obtain ⟨fr, fr_hol, fr_ne, fr_g, key⟩ := exists_push_frame Xo.univ.t.PP.isLB ν.φ O ω hO hne hg
    (fun z => (A.ex z).left) A.hol A.fr A.fr_hol A.fr_ne A.fr_g
  have hch : ∀ z, ∃ a, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U a :=
    fun z => exists_chart _ _ Xo.univ.t.PP.isLB
  have hex0 : (A.ex 0).left = y.x ≫ eSec Xo.univ.t.G := by
    have h0 : A.ex 0 = 1 := by
      have := A.ex_add 0 0
      rw [add_zero] at this
      exact left_eq_mul.1 this
    rw [h0]
    exact one_left _
  let A' : AnFib X bas idx e x L y' :=
    { ex := ex
      ex_add := fun z z' => by simp only [ex, A.ex_add, map_mul]
      ex_onto := Φ.surjective.comp A.ex_onto
      ex_ker := fun z => by
        rw [← A.ex_ker]
        exact Φ.map_eq_one_iff
      ex_lin := fun a z => by
        apply Over.OverMorphism.ext
        rw [hex, A.ex_lin, Over.comp_left, Over.comp_left, Category.assoc, ν.act, ← Category.assoc, hex]
      hol := hexf ▸ ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp A.hol ν.φ
      der := fun ℓ => by
        rw [hexf, hu]
        exact FibreDeriv.isDerivAt0_comp (A.der ℓ) ν.φ
      fr := fr
      fr_hol := by simpa only [hex] using fr_hol
      fr_ne := by simpa only [hex] using fr_ne
      fr_g := by simpa only [hex] using fr_g
      fr_0 := fun i hi => by
        obtain ⟨j, hj⟩ := hch 0
        rw [hex] at hi
        rw [key i j 0 hi hj, A.fr_0 j hj, hb]
        exact (hrig i j y.x _ hex0 ((hO _ _ _).2 ⟨hi, hj⟩)).symm
      χ := A.χ
      χ_norm := A.χ_norm
      fr_per := fun v hv i z hi => by
        obtain ⟨j, hj⟩ := hch z
        rw [hex] at hi
        have hz : A.ex (z + pv X idx x v) = A.ex z := by
          rw [A.ex_add, (A.ex_ker _).2 ⟨v, hv, rfl⟩, _root_.mul_one]
        have h2 := key i j (z + pv X idx x v) (hz ▸ hi) (hz ▸ hj)
        simp only [hz] at h2
        rw [key i j z hi hj, h2, A.fr_per v hv j z hj]
        ring }
  refine ⟨A', fun θ hθ i z pt' hp1 hp2 hi => ?_, fun mk hmk a ha => ?_⟩
  · obtain ⟨j, hj⟩ := hch z
    have hi' : ⊤ ≤ ((A.ex z).left ≫ ν.φ) ⁻¹ᵁ Xo.univ.t.PP.L.U i := hex z ▸ hi
    let pt : Sp ℂ ⟶ Gx y.x := (CartesianMonoidalCategory.lift (𝟙 (Over.mk y.x)) (A.ex z)).left
    have hq1 : pt ≫ Formalism.L2.PjFree.gxFst y.x = (A.ex z).left :=
      congrArg (·.left) (CartesianMonoidalCategory.lift_snd (𝟙 (Over.mk y.x)) (A.ex z))
    have hq2 : pt ≫ Formalism.L2.PjFree.gxSnd y.x = 𝟙 _ :=
      congrArg (·.left) (CartesianMonoidalCategory.lift_fst (𝟙 (Over.mk y.x)) (A.ex z))
    have h1 := hθ j z pt hq1 hq2 hj
    have h2 := hs i j pt pt' _ hq1 hq2 (hp1.trans (hex z)) hp2 ((hO _ _ _).2 ⟨hi', hj⟩)
    refine h2.trans ((congrArg (_ * ·) h1).trans ?_)
    change _ = θ z * fr i z ^ (1 : ℤ)
    rw [zpow_one, zpow_one, key i j z hi' hj]
    ring
  · have ha' : gM a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La) := by
      have := Submodule.mem_map_of_mem (f := gM) ha
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    change _ = Φ (A.ex (pv X idx x (((l.M : E)⁻¹) • mk (gM a))))
    rw [← hmk _ ha']
    apply Over.OverMorphism.ext
    rw [hΦ, levPt, levPt, Over.comp_left, Over.comp_left, Category.assoc, heta, toUnit_left, toUnit_left, hb]
    exact Category.assoc _ _ _

end GlobalTheory.AnMove
end

section
open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameEquiv

set_option maxHeartbeats 1000000 in

theorem canTheta_anFib : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ (Wt : UW U) (k : U.Comp) (bas : (Fin Wt.g ⊕ Fin Wt.g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin Wt.g ≃ (U.X k).Ψ × Fin r), IsSympl (U.X k) bas → (∀ x v j, pv (U.X k) idx x v j = perFr (U.X k) x v (relab c σ (Wt.e j).1) (Wt.e j).2) → (∀ j, rowType (U.X k) (idx j) = relab c σ (Wt.e j).1) → ∀ x : (U.X k).dom, IsUnitFr (U.X k) x.1 → ∀ Pm : (Wt.F.Di (Wt.ik k)).La →+ (Fin Wt.g → ℂ), (∀ a j, Pm a j = perFr (U.X k) x.1 (Wt.φ k a : Fin r → E) (relab c σ (Wt.e j).1) (Wt.e j).2) → (∃ Hm θ, GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws.IsCanTheta Wt.F (Wt.ik k) Pm (U.un k x) Hm θ) ∧ ∀ Hm θ, GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws.IsCanTheta Wt.F (Wt.ik k) Pm (U.un k x) Hm θ → letI : Algebra c.F ℂ := σ.toAlgebra; ∃ A : AnFib (U.X k) bas idx Wt.e x.1 (U.X k).Λ (unC U k x), A.Marked (Wt.mark k) ∧ A.Reads 1 (unC U k x).s θ ∧ MeanOne (U.X k) bas idx x.1 (U.X k).Λ θ ∧ ∀ z w, hermForm Hm z w = hx (U.X k) bas idx x.1 z w := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hr W k bas idx hb hper hty x hx1 Pm' hPm'
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨-, -, -, -, -, hspan, hEF⟩ := GlobalTheory.Dict.uw_lattice E H Dw l Xo c σ r U hσ hU hr W k
  obtain ⟨-, -, -, -, hsm, -, huniq, -⟩ := GlobalTheory.Dict.hx_laws E r (U.X k) W.g bas idx 0 hb (by simp) x.1 x.2
  obtain ⟨Pm, hPm, hP, hu, hder, hrest⟩ := W.pt k x
  obtain rfl : Pm' = Pm := AddMonoidHom.ext fun a => funext fun j => (hPm' a j).trans (hPm a j).symm
  obtain ⟨Hm, χl, fr, θ, Fd, hH, hpos, hIm, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hrest hx1
  have hcan : GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws.IsCanTheta W.F (W.ik k) Pm' (U.un k x) Hm θ :=
    ⟨hH, hpos, hIm, χl, fr, h1, h2, h3, h4, h5, h6⟩
  refine ⟨⟨Hm, θ, hcan⟩, fun Hm' θ' hcan' => ?_⟩
  obtain ⟨rfl, rfl⟩ : Hm = Hm' ∧ θ = θ' :=
    GlobalTheory.TwistFactorCompare.isCanTheta_unique (F := W.F) (k := W.ik k) (Pm := Pm') (y := U.un k x)
      ⟨hP, hu, hcan⟩ ⟨hP, hu, hcan'⟩
  obtain ⟨ex, hl, e1, e2, e3, e4, e5⟩ := exists_ex_transport W.F (W.ik k) Pm' hP (unC U k x).x hu
  have hpv : ∀ a, Pm' a = pv (U.X k) idx x.1 (W.emb k a) := fun a => by
    funext j
    rw [hPm, hper]
    rfl
  have hsurj : ∀ v ∈ (U.X k).Λ, ∃ a, W.emb k a = v := fun v hv =>
    ⟨(W.φ k).symm ⟨v, hv⟩, by simp [UW.emb]⟩
  have hmem : ∀ a, W.emb k a ∈ (U.X k).Λ := fun a => (W.φ k a).2
  have hrange : ∀ z, z ∈ Pm'.range ↔ ∃ v ∈ (U.X k).Λ, z = pv (U.X k) idx x.1 v := fun z => by
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨_, hmem a, hpv a⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨a, rfl⟩ := hsurj v hv
      exact ⟨a, hpv a⟩
  have hspan' : Submodule.span E ((U.X k).Λ : Set (Fin r → E)) = ⊤ := by
    rw [eq_top_iff, ← hspan]
    apply Submodule.span_mono
    rintro _ ⟨a, rfl⟩
    exact hmem a
  have hhx : ∀ z w, hermForm Hm z w = hx (U.X k) bas idx x.1 z w := by
    refine (huniq _ hspan').2 Hm hH ?_
    intro u hu v hv
    obtain ⟨a, rfl⟩ := hsurj u hu
    obtain ⟨b, rfl⟩ := hsurj v hv
    rw [← hpv, ← hpv, hIm, ← hEF]
    simp
  have hl' : (fun z => (ex z).left) = fun z => (W.F.ex (W.ik k) Pm' z).left := funext hl
  refine ⟨{ ex := ex
            ex_add := e1
            ex_onto := e2
            ex_ker := fun z => (e3 z).trans (hrange z)
            ex_lin := fun a z => by simp only [hty]; exact e4 a z
            hol := ?_
            der := fun ℓ => by rw [hl']; exact hder ℓ.1 ℓ.2
            fr := fr
            fr_hol := fun j => by simp only [hl]; exact h1 j
            fr_ne := fun j z => by rw [hl]; exact h2 j z
            fr_g := fun j j' z => by rw [hl]; exact h3 j j' z
            fr_0 := fun j => by rw [hl]; exact h4 j
            χ := fun v => χl (pv (U.X k) idx x.1 v)
            χ_norm := ?_
            fr_per := ?_ }, ?_, ?_, ⟨Pm'.range, Fd, hrange, h7, ?_⟩, hhx⟩
  · rw [hl']
    intro V f
    have := ReciprocityTheory.ChartRestriction.G.TB.ValAt.famHol W.F (W.ik k) Pm' hP V f
    simpa only [Set.mem_univ, true_and] using this
  · intro v hv
    obtain ⟨a, rfl⟩ := hsurj v hv
    rw [← hpv]
    obtain ⟨j, -⟩ := TopologicalSpace.Opens.mem_iSup.1
      (Xo.univ.t.PP.isLB.cover.ge (Set.mem_univ ((ex 0).left (IsLocalRing.closedPoint ℂ))))
    exact (h5 a j 0).1
  · intro v hv j z
    obtain ⟨a, rfl⟩ := hsurj v hv
    rw [hl, ← hpv, ← hhx, ← hhx]
    exact (h5 a j z).2
  · intro a ha
    show levPt Xo (unC U k x).x a = ex _
    rw [e5 a ha, hsm, hpv]
    congr 1
    funext j
    simp [UW.mark]
  · intro j z pt
    show _ = (ex z).left → _ → ⊤ ≤ (ex z).left ⁻¹ᵁ _ → _ = θ z * fr j z ^ (1 : ℤ)
    rw [hl, zpow_one]
    exact h6 j z pt
  · simp only [← hhx]
    exact h8

end GlobalTheory.FrameEquiv
end

section
open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameEquiv.LatMove

theorem rational_matrix_isRatOf {D : D7} (V : HSp D) (δ : GA D V) (hδ : δ ∈ GQ V) (τ : D.host.E →+* ℂ)
    (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (hθ : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ)
    (δ₁ : GL (Fin V.rank) D.host.E) (h₁ : archM V θ δ = δ₁.1.map τ) : GlobalTheory.Ker.IsRatOf V δ₁ δ := by
  obtain ⟨δ₀, -, he⟩ := hδ
  have he' : ∀ i j, (matHom V δ).1 i j = (1 : AF D.host.F) ⊗ₜ δ₀.1 i j := fun i j =>
    (congrArg (fun x : GL (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E) => x.1 i j) he).symm
  ext i j
  have h₀ : archM V θ δ i j = τ (δ₀.1 i j) := by
    change θ (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom V δ).1 i j)) = _
    rw [he', Algebra.TensorProduct.map_tmul, map_one]
    exact hθ.1 _
  have e : δ₀.1 i j = δ₁.1 i j := τ.injective (by rw [← h₀, h₁]; rfl)
  exact (he' i j).trans (congrArg (fun x => (1 : AF D.host.F) ⊗ₜ[D.host.F] x) e)

theorem kappa_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X X' : Data E r) (τ : E →+* ℂ)
    (h : τ ∈ X.Ψ) (h' : τ ∈ X'.Ψ) (hξ : X.ξ0 = X'.ξ0) : X.κ0 = X'.κ0 := by
  have s1 : (τ X.κ0).im < 0 := X.κ0_sign ⟨τ, h⟩
  have s2 : (τ X'.κ0).im < 0 := X'.κ0_sign ⟨τ, h'⟩
  rcases X.κ0_xi with e | e <;> rcases X'.κ0_xi with e' | e'
  · rw [e, e', hξ]
  · rw [e, hξ] at s1
    rw [e', map_neg, Complex.neg_im] at s2
    linarith
  · rw [e, hξ, map_neg, Complex.neg_im] at s1
    rw [e'] at s2
    linarith
  · rw [e, e', hξ]

theorem flip_congr {A : Type} [AddCommGroup A] {a b y : A} {N : ℕ} (h : a - b = N • y) : b = a + N • (-y) := by
  rw [smul_neg, ← h]
  abel

set_option maxHeartbeats 1000000 in

theorem lattice_move : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (W : HSp D) (U : Unf Xo c σ W.rank) (dict : GA D W → Σ k, Frame (U.X k).Ψ W.rank) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin W.rank) (Fin W.rank) ℂ), GeoSet W U dict x₀ → LatEmb W ι → ∀ d : GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws.DictDat U, d.Is W rfl dict ι x₀ → ∀ (κ : GA D W) (lev : Dw.La →ₗ[𝓞 D.host.E] Dw.La), GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.StabLat W κ → GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.LevAgrees W ι l.M (Mfr l) κ lev → ∀ h γ γ' : GA D W, d.At W rfl dict ι x₀ h γ → d.At W rfl dict ι x₀ (h * κ) γ' → ∃ (ga : GL (Fin W.rank) D.host.E) (hs : SameSp (U.X (dict h).1) (U.X (dict (h * κ)).1)), GlobalTheory.Ker.IsRatOf W ga (γ' * γ⁻¹) ∧ IsUn (U.X (dict (h * κ)).1) ga ∧ mapL ga (U.X (dict h).1).Λ = (U.X (dict (h * κ)).1).Λ ∧ lact ga (castFr hs.psi (dict h).2) = (dict (h * κ)).2 ∧ ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ u ∈ (U.X (dict (h * κ)).1).Λ, (ga : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *ᵥ (d.φ (dict h).1 (d.F.t (d.ik (dict h).1) (lev a)) : Fin W.rank → D.host.E) = (d.φ (dict (h * κ)).1 (d.F.t (d.ik (dict (h * κ)).1) a) : Fin W.rank → D.host.E) + l.M • u := by
  intro D H Dw l Xo c σ W U dict ι x₀ hG _ d hd κ lev hκ hlev h γ γ' hat hat'
  obtain ⟨-, hU, -, -, hW, -⟩ := hG
  obtain ⟨⟨hγ, hΛ, hm⟩, hfr⟩ := hat
  obtain ⟨⟨hγ', hΛ', hm'⟩, hfr'⟩ := hat'
  have hδ : γ' * γ⁻¹ ∈ GQ W := mul_mem hγ' (inv_mem hγ)
  obtain ⟨δ, hδu, hδf, hδa⟩ := GlobalTheory.MarkCoset.rational_matrix W _ hδ
  have hprod : γ' * γ⁻¹ * (γ * h) * κ = γ' * (h * κ) := by group
  have hκ1 : latGHat W κ = latGHat W 1 := by
    unfold latGHat
    rw [hκ.2, (GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.stabLat_one W).2]
  have hpsi : ∀ k k', (U.X k).Ψ = (U.X k').Ψ := fun k k' =>
    Finset.ext fun τ => ((hU.2.1 k).2 τ).trans ((hU.2.1 k').2 τ).symm
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ, τ ∈ (U.X (dict h).1).Ψ := by
    by_cases h0 : D.host.φ₀ ∈ (U.X (dict h).1).Ψ
    · exact ⟨_, h0⟩
    · exact ⟨_, not_not.1 (mt ((U.X (dict h).1).cmType _).2 h0)⟩
  have hξ : (U.X (dict h).1).ξ0 = (U.X (dict (h * κ)).1).ξ0 := (hW _).2.trans (hW _).2.symm
  have hs : SameSp (U.X (dict h).1) (U.X (dict (h * κ)).1) :=
    ⟨hpsi _ _, (hW _).1.trans (hW _).1.symm, (hU.2.1 _).1.trans (hU.2.1 _).1.symm, hξ,
      kappa_eq _ _ τ₀ hτ₀ (hpsi _ _ ▸ hτ₀) hξ⟩
  obtain ⟨ht1, ht2⟩ := GlobalTheory.ShortMoveIso.transport (finHom W) (latGHat W)
    (fun g => (GlobalTheory.MarkCoset.latG_spec D W g).2) l.M (γ' * γ⁻¹) (γ * h) κ hκ1
  rw [hprod] at ht1 ht2
  have hmem : ∀ v, v ∈ (U.X (dict h).1).Λ ↔ finVec W v ∈ latGHat W (γ * h) := fun v => by
    rw [← (GlobalTheory.MarkCoset.latG_spec D W _).1, ← SetLike.mem_coe, hΛ]
    exact Set.ext_iff.1 (Set.image_id _) v
  have hmem' : ∀ v, v ∈ (U.X (dict (h * κ)).1).Λ ↔ finVec W v ∈ latGHat W (γ' * (h * κ)) := fun v => by
    rw [← (GlobalTheory.MarkCoset.latG_spec D W _).1, ← SetLike.mem_coe, hΛ']
    exact Set.ext_iff.1 (Set.image_id _) v
  have hlat : ∀ v, v ∈ (U.X (dict h).1).Λ ↔ δ.1 *ᵥ v ∈ (U.X (dict (h * κ)).1).Λ := fun v => by
    rw [hmem, hmem', ht1, hδf]
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  have hG' : (U.X (dict (h * κ)).1).Gm = -W.gram.transpose := (hW _).1
  refine ⟨δ, hs, rational_matrix_isRatOf W _ hδ τ₀ _ (hd.1 _ ⟨τ₀, hτ₀⟩) δ (hδa _ _ (hd.1 _ ⟨τ₀, hτ₀⟩)),
    fun u v => by rw [hG']; exact hδu u v, ?_, ?_, fun a ha => ?_⟩
  · ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (hlat u).1 hu
    · intro hv
      have hri : δ.1 *ᵥ ((δ⁻¹).1 *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      exact ⟨(δ⁻¹).1 *ᵥ v, (hlat _).2 (by rw [hri]; exact hv), hri⟩
  · funext τ
    have hτ : τ.1 ∈ (U.X (dict h).1).Ψ := by rw [hs.psi]; exact τ.2
    have e1 := hfr ⟨τ.1, hτ⟩
    have e2 := hfr' τ
    have hth := hd.1 _ τ
    rw [GlobalTheory.LettersCheck.isInfEmb_unique τ.1 _ _ (hd.1 _ ⟨τ.1, hτ⟩) hth] at e1
    have hmul : ∀ a b : GA D W, archM W (d.th _ τ) (a * b) = archM W (d.th _ τ) a * archM W (d.th _ τ) b := by
      intro a b
      rw [archM, archM, archM, map_mul, Units.val_mul, Matrix.map_mul]
    have hone : archM W (d.th _ τ) κ = 1 := by
      rw [archM, show infHom W κ = 1 from hκ.1, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [← hprod, hmul, hmul, hone, Matrix.mul_one, hδa _ _ hth] at e2
    change δ.1.map τ.1 * mat (dict h).2 ⟨τ.1, hτ⟩ = mat (dict (h * κ)).2 τ
    rw [e1, e2, ← Matrix.mul_assoc]
    rfl
  · obtain ⟨y, hy, ey⟩ := hlev a ha
    obtain ⟨z, hz, e⟩ := ht2 (finVec W (d.φ (dict h).1 (d.F.t (d.ik (dict h).1) (lev a)) : Fin W.rank → D.host.E))
      (finVec W (d.φ (dict (h * κ)).1 (d.F.t (d.ik (dict (h * κ)).1) a) : Fin W.rank → D.host.E)) _ _
      ⟨-y, neg_mem hy, flip_congr ey⟩
      (hm _ (GlobalTheory.ShortMoveIso.map_mem_half _ lev a ha)) (hm' a ha)
    obtain ⟨w, hw, e'⟩ := GlobalTheory.MarkCoset.finVec_div W l.M hM0
      (δ.1 *ᵥ (d.φ (dict h).1 (d.F.t (d.ik (dict h).1) (lev a)) : Fin W.rank → D.host.E) -
        (d.φ (dict (h * κ)).1 (d.F.t (d.ik (dict (h * κ)).1) a) : Fin W.rank → D.host.E)) z (by
        rw [← e, hδf]
        funext i
        exact TensorProduct.tmul_sub _ _ _)
    exact ⟨w, (hmem' w).2 (hw ▸ hz), sub_eq_iff_eq_add'.1 e'⟩

end GlobalTheory.FrameEquiv.LatMove
end

section
open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameEquiv

theorem frBor_genDiag {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (s' : LB.Sec (PPx y.x)) (hs' : GlobalTheory.Frames.SecGen y.x s') (a : Sˣ)
    (h : ∀ i, s'.f i = scal y.x (a : S) i * y.s.f i) :
    FrBor (GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.genDiag Dw a) y { y with s := s', gen := hs' } := by
  refine ⟨rfl, fun τ i => ⟨(1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) i, Matrix.one_apply_eq i,
    fun j hij => Matrix.one_apply_ne hij.ne, (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c S y y y).1.2.1 τ i⟩,
    𝟙 _, Category.id_comp _, Category.id_comp _, fun i hi => ?_⟩
  refine Eq.trans ?_ (h i).symm
  exact congrArg (fun m => CommRingCat.Hom.hom m (scal y.x (a : S) i * y.s.f i))
    ((Gx y.x).presheaf.map_id (Opposite.op ((PPx y.x).U i)))

set_option maxHeartbeats 1000000 in

theorem evR_eq_of_reads_smul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y y' : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y) (A' : AnFib X bas idx e x L y'), IsSympl X bas → x ∈ X.dom → SelfD X L → (∀ z, (A'.ex z).left = (A.ex z).left) → (∀ j z, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → A'.fr j z = A.fr j z) → ∀ (θ : (Fin g → ℂ) → ℂ) (t : ℂ), A.Reads 1 y.s θ → A'.Reads 1 y'.s (t • θ) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, evR Xo c f y' = t ^ n * evR Xo c f y := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y y' A A' _ _ _ hex hfr θ t hR hR' a n f hf
  have hx : y'.x = y.x := (Over.w (A'.ex 0)).symm.trans
    ((congrArg (· ≫ Xo.univ.t.G.hom) (hex 0)).trans (Over.w (A.ex 0)))
  have hu : y'.u = y.u := funext fun τ => funext fun i =>
    GlobalTheory.PointUnif.deriv_unique (by simpa only [hex] using A'.der ⟨τ, i⟩) (A.der ⟨τ, i⟩)
  obtain ⟨x', ho', u', tan', eig', bas', s', gen'⟩ := y'
  dsimp only at hx hu
  subst hx hu
  have hT : Out.SecTwistSt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have V := GlobalTheory.sec_values_complex_fibre hT E H Dw l Xo y.x
  have key : ∀ i (pt : Sp ℂ ⟶ Gx y.x), pt ≫ Formalism.L2.PjFree.gxSnd y.x = 𝟙 _ →
      valAt' pt ((PPx y.x).U i) (s'.f i) = t * valAt' pt ((PPx y.x).U i) (y.s.f i) := by
    intro i pt hp
    by_cases hi : ⊤ ≤ pt ⁻¹ᵁ (PPx y.x).U i
    · have hw : (pt ≫ Formalism.L2.PjFree.gxFst y.x) ≫ Xo.univ.t.G.hom = y.x := by
        have h1 := Over.w (CartesianMonoidalCategory.snd (Over.mk y.x) Xo.univ.t.G)
        have h2 := Over.w (CartesianMonoidalCategory.fst (Over.mk y.x) Xo.univ.t.G)
        refine (Category.assoc _ _ _).trans ((congrArg (pt ≫ ·) (h1.trans h2.symm)).trans ?_)
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ y.x) hp).trans (Category.id_comp _))
      obtain ⟨z, hz⟩ := A.ex_onto (Over.homMk (pt ≫ Formalism.L2.PjFree.gxFst y.x) hw)
      have hz' : pt ≫ Formalism.L2.PjFree.gxFst y.x = (A.ex z).left := (congrArg (·.left) hz).symm
      obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨i 0, funext fun q => congrArg i (Fin.fin_one_eq_zero q)⟩
      have hj : ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by
        rw [← hz']
        exact fun q hq => Set.mem_iInter.1 (hi hq) 0
      have e1 := hR j z pt hz' hp hj
      have e2 := hR' j z pt (hz'.trans (hex z).symm) hp (by rw [hex]; exact hj)
      rw [hfr j z hj, Pi.smul_apply, smul_eq_mul, mul_assoc] at e2
      exact e2.trans (congrArg (t * ·) e1.symm)
    · rw [ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_of_not _ _ hi, ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_of_not _ _ hi, mul_zero]
  have ht : t ≠ 0 := by
    obtain ⟨i, pt, hp, hv⟩ := (V s').2.1.1 gen'
    exact fun h0 => hv (by rw [key i pt hp, h0, zero_mul])
  obtain ⟨b, hb, -⟩ := y.gen s'
  have hbt : b = t := by
    obtain ⟨i, pt, hp, hv⟩ := (V y.s).2.1.1 y.gen
    refine mul_right_cancel₀ hv ?_
    rw [← key i pt hp, hb i, (V y.s).1 b i pt hp]
  subst hbt
  have hA : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c
  have hw := (GlobalTheory.borDesc_and_wtField E H Dw l Xo c).2 a n f hf ℂ _ y _ (hA ℂ y) (hA ℂ _)
    (frBor_genDiag y s' gen' (Units.mk0 b ht) hb)
  refine hw.trans (congrArg (· * evR Xo c f y) ?_)
  unfold wchar
  rw [Fintype.prod_option]
  simp [GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.genDiag, ex]

end GlobalTheory.FrameEquiv
end

section
open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameEquiv.Reindex

attribute [local instance] Over.cartesianMonoidalCategory

variable {g g' : ℕ}

noncomputable def rho (ε : Fin g' ≃ Fin g) : (Fin g → ℂ) →L[ℂ] (Fin g' → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (ε i)

theorem rho_apply (ε : Fin g' ≃ Fin g) (z : Fin g → ℂ) : rho ε z = z ∘ ε := rfl

theorem rho_single (ε : Fin g' ≃ Fin g) (m : Fin g) : rho ε (Pi.single m 1) = Pi.single (ε.symm m) 1 := by
  funext i
  rw [rho_apply, Function.comp_apply, Pi.single_apply, Pi.single_apply]
  simp only [Equiv.eq_symm_apply]

theorem rho_injective (ε : Fin g' ≃ Fin g) : Function.Injective (rho ε) := fun z w h => by
  funext i
  simpa [rho_apply] using congrFun h (ε.symm i)

theorem hermForm_reindex (ε : Fin g' ≃ Fin g) (Hm : Matrix (Fin g') (Fin g') ℂ) (z w : Fin g → ℂ) :
    hermForm (Hm.submatrix ε.symm ε.symm) z w = hermForm Hm (rho ε z) (rho ε w) := by
  unfold hermForm
  rw [Matrix.submatrix_mulVec_equiv, Equiv.symm_symm, dotProduct_comp_equiv_symm]
  rfl

noncomputable def rhoM (ε : Fin g' ≃ Fin g) : (Fin g → ℂ) ≃ᵐ (Fin g' → ℂ) :=
  (MeasurableEquiv.piCongrLeft (fun _ => ℂ) ε).symm


theorem rho_mp (ε : Fin g' ≃ Fin g) : MeasurePreserving (rhoM ε) volume volume :=
  (volume_measurePreserving_piCongrLeft (fun _ => ℂ) ε).symm _

theorem fund_reindex (ε : Fin g' ≃ Fin g) {A A' : Type} [AddCommGroup A] [AddCommGroup A'] (ψ : A ≃ A')
    (P : A →+ (Fin g → ℂ)) (P' : A' →+ (Fin g' → ℂ)) (h : ∀ a, P' (ψ a) = rho ε (P a)) {Fd : Set (Fin g' → ℂ)}
    (hF : IsAddFundamentalDomain P'.range Fd volume) : IsAddFundamentalDomain P.range (rho ε ⁻¹' Fd) volume := by
  have key : ∀ v : P'.range, rho ε.symm v.1 ∈ P.range := by
    rintro ⟨_, b, rfl⟩
    refine ⟨ψ.symm b, rho_injective ε ?_⟩
    rw [← h, Equiv.apply_symm_apply]
    funext i
    simp [rho_apply]
  refine hF.preimage_of_equiv (f := rho ε) (rho_mp ε).quasiMeasurePreserving
    (e := fun v => ⟨rho ε.symm v.1, key v⟩) ⟨fun v w hvw => ?_, ?_⟩ fun v z => ?_
  · exact Subtype.ext (rho_injective _ (congrArg Subtype.val hvw))
  · rintro ⟨_, a, rfl⟩
    refine ⟨⟨P' (ψ a), ψ a, rfl⟩, Subtype.ext ?_⟩
    funext i
    simp [h, rho_apply]
  · funext i
    change v.1 (ε.symm (ε i)) + z (ε i) = v.1 i + z (ε i)
    rw [Equiv.symm_apply_apply]

open MonObj in
theorem left_eq {S : Scheme.{0}} {G : Over S} [GrpObj G] {y y' : Sp ℂ ⟶ S} (hy : y = y')
    (ρ : (Fin g → ℂ) →L[ℂ] (Fin g' → ℂ))
    {e : (Fin g → ℂ) → (Over.mk y ⟶ G)} {e' : (Fin g' → ℂ) → (Over.mk y' ⟶ G)}
    (he : ∀ z w, e (z + w) = e z * e w) (he' : ∀ z w, e' (z + w) = e' z * e' w)
    (hol : IsHolTo Set.univ (fun z => (e z).left)) (hol' : IsHolTo Set.univ (fun z => (e' z).left))
    (u : Fin g → (Sp (DualNumber ℂ) ⟶ G.left)) (hd : ∀ i, IsDerivAt0 (fun z => (e z).left) (Pi.single i 1) (u i))
    (hd' : ∀ i, IsDerivAt0 (fun z => (e' z).left) (ρ (Pi.single i 1)) (u i)) (z : Fin g → ℂ) :
    (e z).left = (e' (ρ z)).left := by
  subst hy
  have E : e = fun z => e' (ρ z) :=
    GlobalTheory.CuspFamilyCompare.exp_unique he (fun z w => by rw [map_add, he']) hol
      (HolHom.isHolTo_of_holAt isOpen_univ fun z _ =>
        (HolHom.holAt_of_isHolTo hol' (Set.mem_univ (ρ z))).precomp ρ.differentiableAt)
      u hd (fun m => GlobalTheory.CuspFamilyCompare.isDerivAt0_comp hol' ρ (hd' m))
  rw [E]

end GlobalTheory.FrameEquiv.Reindex

namespace GlobalTheory.FrameEquiv

open Reindex

set_option maxHeartbeats 1000000 in

theorem hasWitness_of_is : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → ∀ (W : HSp D) (hr : W.rank = r) (dict : GA D W → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (d : GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws.DictDat U), d.Is W hr dict ι x₀ → HasWitness d := by
  intro D H Dw l Xo c σ r U _ hU _ W hr dict ι x₀ d hd
  obtain ⟨W₀⟩ := nonempty_uw ((Formalism.L2.PjFree.isUnf_ofPj U).2 hU)
  obtain ⟨-, ⟨hiso, hpt⟩, -⟩ := hd
  refine ⟨⟨d.g, d.e, d.F, d.ik, d.φ, hiso, fun k x => ?_⟩, rfl⟩
  obtain ⟨Pm, h1, h2, h3, h4⟩ := hpt k x
  refine ⟨Pm, h1, h2, h3, h4, fun hun => ?_⟩
  obtain ⟨Pm', b1, b2, b3, b4, b5⟩ := W₀.pt k x
  obtain ⟨Hm, χl, fr, θ, Fd, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11⟩ := b5 hun
  let ε : Fin W₀.g ≃ Fin d.g := W₀.e.trans d.e.symm
  let ψ : (d.F.Di (d.ik k)).La ≃ (W₀.F.Di (W₀.ik k)).La := ((d.φ k).trans (W₀.φ k).symm).toEquiv
  have hψ : ∀ a, W₀.φ k (ψ a) = d.φ k a := fun a => (W₀.φ k).apply_symm_apply _
  have hP : ∀ a, Pm' (ψ a) = rho ε (Pm a) := fun a => by
    funext j
    have hj : d.e (ε j) = W₀.e j := d.e.apply_symm_apply _
    rw [rho_apply, Function.comp_apply, h1, b1, hψ, hj]
    rfl
  have hE : ∀ z, (d.F.ex (d.ik k) Pm z).left = (W₀.F.ex (W₀.ik k) Pm' (rho ε z)).left :=
    left_eq (h3.symm.trans b3) (rho ε) (d.F.ex_add _ _ h2) (W₀.F.ex_add _ _ b2)
      (GlobalTheory.CuspFamilyCompare.isHolTo_ex _ _ h2) (GlobalTheory.CuspFamilyCompare.isHolTo_ex _ _ b2)
      (fun m => (U.un k x).u (d.e m).1 (d.e m).2)
      (fun m => by simpa using h4 (d.e m).1 (d.e m).2)
      (fun m => by rw [rho_single]; exact b4 (d.e m).1 (d.e m).2)
  refine ⟨Hm.submatrix ε.symm ε.symm, fun z => χl (rho ε z), fun j z => fr j (rho ε z), fun z => θ (rho ε z),
    rho ε ⁻¹' Fd, c1.submatrix _, fun z hz => ?_, fun a b => ?_, fun j => ?_, fun j z hz => ?_, fun j j' z hz => ?_,
    fun j hz => ?_, fun a j z => ?_, fun j z pt p1 p2 hz => ?_, fund_reindex ε ψ Pm Pm' hP c10, ?_⟩
  · rw [hermForm_reindex]
    exact c2 _ fun h0 => hz (rho_injective ε (h0.trans (map_zero _).symm))
  · rw [hermForm_reindex, ← hP, ← hP, c3]
    have := (W₀.isom k (ψ a) (ψ b))
    rw [hψ, hψ] at this
    exact_mod_cast this.trans (hiso k a b).symm
  · refine (c4 j).comp (rho ε).differentiable.differentiableOn fun z hz => ?_
    rw [Set.mem_ofPred_eq, hE] at hz
    exact hz
  · rw [hE] at hz
    exact c5 _ _ hz
  · rw [hE] at hz ⊢
    exact c6 _ _ _ hz
  · rw [hE, map_zero] at hz
    simp only [map_zero]
    exact c7 _ hz
  · simp only [hermForm_reindex, map_add, ← hP, hE]
    exact c8 _ _ _
  · rw [hE] at hz p1
    exact c9 _ _ _ p1 p2 hz
  · simp only [hermForm_reindex]
    have m1 : volume (rho ε ⁻¹' Fd) = volume Fd := (rho_mp ε).measure_preimage_equiv Fd
    have m2 := (rho_mp ε).setIntegral_preimage_emb (rhoM ε).measurableEmbedding
      (fun z => ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) Fd
    rw [m1]
    exact (congrArg (· / _) m2).trans c11

end GlobalTheory.FrameEquiv
end

section
open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000

namespace GlobalTheory.FrameEquiv.GenMove

section Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem perFr_cast {r : ℕ} {X' X : Data E r} (h : SameSp X' X)
    (x : Frame X'.Ψ r) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    perFr X' x v τ i = perFr X (castFr h.psi x) v τ i := by
  obtain ⟨h1, h2, h3, -, -⟩ := h
  cases X
  cases X'
  dsimp only at h1 h2 h3
  subst h1 h2 h3
  rfl

theorem hostHalfRoot_add_conj_eq_one (H : Geo.Tor.Host E) : (H.w0 : E) + cc (H.w0 : E) = 1 := by
  have := congrArg (algebraMap (𝓞 E) E) (PullbackSections.CVA.cmHostUnit_add_conj_eq_one H)
  rw [map_add, map_one] at this
  exact (congrArg _ (H.bar_eq _).symm).trans this

variable {H : Geo.Tor.Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ]
  {r g : ℕ}

open MonObj in

theorem marked_congr {X : Data E r}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r}
    {L : Lt E r} {y : FrPt Xo c ℂ} (A : AnFib X bas idx e x L y) {mk mk' : Dw.La →ₗ[𝓞 E] (Fin r → E)}
    (h : A.Marked mk) (hc : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ u ∈ L, mk a = mk' a + l.M • u) :
    A.Marked mk' := by
  intro a ha
  obtain ⟨u, hu, e'⟩ := hc a ha
  have hM : (l.M : E) ≠ 0 := by have := l.three_le; exact_mod_cast (by omega : l.M ≠ 0)
  have hadd : ∀ u v, pv X idx x (u + v) = pv X idx x u + pv X idx x v := fun u v => by
    unfold pv; rw [per_add]; rfl
  rw [h a ha, e', smul_add, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hM, hadd, A.ex_add,
    (A.ex_ker _).2 ⟨u, hu, rfl⟩, _root_.mul_one]

theorem ne_zero_of_meanOne {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r}
    {x : Frame X.Ψ r} {L : Lt E r} {θ : (Fin g → ℂ) → ℂ} (h : MeanOne X bas idx x L θ) : θ ≠ 0 := by
  rintro rfl
  obtain ⟨_, _, _, _, h⟩ := h
  simp at h

theorem values_of_move {X' X : Data E r} (h : SameSp X' X)
    {bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X'.Λ} {idx' : Fin g ≃ X'.Ψ × Fin r}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw}
    {x' : Frame X'.Ψ r} {x : Frame X.Ψ r} {y y' y₂ : FrPt Xo c ℂ} (A : AnFib X' bas' idx' e x' X'.Λ y)
    (A₂ : AnFib X bas idx e x X.Λ y₂) (ga : GL (Fin r) E) (hs' : IsSympl X' bas') (hs : IsSympl X bas)
    (hx' : x' ∈ X'.dom) (hL' : SelfD X' X'.Λ) (hun : IsUn X ga)
    (hpv : ∀ v, pv X' idx' x' v = pv X idx (castFr h.psi x') v)
    (hty : ∀ j, rowType X' (idx' j) = rowType X (idx j)) (hA : l.A = 1)
    (e1 : mapL ga X'.Λ = X.Λ) (e2 : lact ga (castFr h.psi x') = x)
    {gM gA : Dw.La →ₗ[𝓞 E] Dw.La} (hlev : levR (gM, gA) y y')
    {mk' mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} (hmk : IsMark l X.Λ mk) (hm' : A.Marked mk') (hm : A₂.Marked mk)
    (hc : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ u ∈ X.Λ,
      (ga : Matrix (Fin r) (Fin r) E) *ᵥ mk' (gM a) = mk a + l.M • u)
    {θ θ₂ : (Fin g → ℂ) → ℂ} (hθ : A.Reads 1 y.s θ) (hθ₂ : A₂.Reads 1 y₂.s θ₂)
    (h1 : MeanOne X' bas' idx' x' X'.Λ θ) :
    ∃ t : ℂ, θ₂ = t • θ ∧ (∃ v, θ (pv X' idx' x' v) ≠ 0) ∧
      (∀ v, pv X idx x ((ga : Matrix (Fin r) (Fin r) E) *ᵥ v) = pv X' idx' x' v) ∧
      (∀ z w, hx X bas idx x z w = hx X' bas' idx' x' z w) ∧
      ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, evR Xo c f y₂ = t ^ n * evR Xo c f y' := by
  obtain ⟨A', hR', hM'⟩ := GlobalTheory.AnMove.anFib_move E H Dw l Xo c r g X' bas' idx' e x' _ y y' A hs' hx' hL' gM gA hlev
  obtain ⟨hd, -, hsd, A'', hR'', -, hM''⟩ := GlobalTheory.Dict.anFib_move E H Dw l Xo c r g X' X h bas' idx' bas idx e x' _ y' A' ga
    hs' hs hx' hL' hun hpv hty
  have hR := hR'' _ (hR' _ hθ)
  have hM := hM'' _ (hM' _ hm')
  have hx1 := h.castFr_mem_dom hx'
  obtain ⟨-, -, him', -⟩ := hx_laws E r X' g bas' idx' 0 hs' Even.zero x' hx'
  obtain ⟨-, -, -, -, -, -, huniq, hinv⟩ := hx_laws E r X g bas idx 0 hs Even.zero _ hx1
  obtain ⟨-, hpv2, -, hhx2⟩ := hinv ga hun
  have hhx (z w) : hx X bas idx (lact ga (castFr h.psi x')) z w = hx X' bas' idx' x' z w := by
    rw [hhx2, hx_eq_hermForm idx']
    refine ((huniq X.Λ X.Λ_span).2 _ (Hm_isHermitian idx' hs' hx') (fun u _ v _ => ?_) z w).symm
    rw [← hpv, ← hpv, ← hx_eq_hermForm, him', h.EF_eq]
  clear hR'' hM''
  revert A'' hd hsd
  rw [e1]
  subst e2
  intro hd hsd A'' hR hM
  have hM2 : A''.Marked mk := marked_congr A'' hM hc
  have hex := GlobalTheory.Dict.anFib_ex_eq E H Dw l Xo c r g X bas idx e _ _ y' y₂ A'' A₂ hs hd hsd hA mk hmk hM2 hm
  have hfr := GlobalTheory.FrameEquiv.anFib_fr_eq_of_ex_left_eq E H Dw l Xo c r g X bas idx e _ _ y' y₂ A'' A₂ hs hd hsd hex
  have t1 := isTheta1_of_reads_generator E H Dw l Xo c r g X bas idx e _ _ y' A'' hs hd hsd θ hR
  have t2 := isTheta1_of_reads_generator E H Dw l Xo c r g X bas idx e _ _ y₂ A₂ hs hd hsd θ₂ hθ₂
  have hne := ne_zero_of_meanOne h1
  obtain ⟨t, ht⟩ := ThetaOne.exists_eq_smul_of_isTheta1 E r X g bas idx 0 hs Even.zero (H.w0 : E) H.w0.2
    (hostHalfRoot_add_conj_eq_one H) _ hsd _ hd θ₂ θ t2 t1 hne
  refine ⟨t, ht, exists_apply_pv_ne_zero E r X' g bas' idx' hs' x' hx' θ t1.1.continuous hne,
    fun v => (hpv2 v).trans (hpv v).symm, hhx, ?_⟩
  exact GlobalTheory.FrameEquiv.evR_eq_of_reads_smul E H Dw l Xo c r g X bas idx e _ _ y' y₂ A'' A₂ hs hd hsd hex hfr θ t hR (ht ▸ hθ₂)

end Classical

section Adelic

open GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws

theorem map_mul_zero {A B m n : Type} [CommRing A] [CommRing B] [Fintype m] (π : A →+* B) (P : Matrix m m A)
    (w : Matrix m n A) (h : ∀ a b, π (w a b) = 0) (a : m) (b : n) : π ((P * w) a b) = 0 := by
  rw [Matrix.mul_apply, map_sum]
  exact Finset.sum_eq_zero fun i _ => by rw [map_mul, h, mul_zero]

theorem map_mul_congr {A B K m n : Type} [CommRing A] [CommRing B] [CommRing K] [Fintype m] (π : A →+* B)
    (j : K →+* A) (P : Matrix m m K) (w : Matrix m n A) (X : Matrix m n K) (h : ∀ a b, π (w a b) = π (j (X a b)))
    (a : m) (b : n) : π ((P.map j * w) a b) = π (j ((P * X) a b)) := by
  rw [Matrix.mul_apply, Matrix.mul_apply, map_sum, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul, map_mul, map_mul, h]; rfl

variable {D : D7}

theorem isRealPt_actO (V W : HSp D) {ga : GL (Fin W.rank) D.host.E} {δ : GA D W} (hδ : GlobalTheory.Ker.IsRatOf W ga δ)
    {X : Matrix (Fin W.rank) (Fin V.rank) D.host.E} {w : WO V W} (hw : IsRealPt V W X w) :
    IsRealPt V W ((ga : Matrix (Fin W.rank) (Fin W.rank) D.host.E) * X) (actO V W 1 δ w) := by
  rw [GlobalTheory.OneMapRef.RatPt.actO_one, hδ]
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · exact map_mul_zero (finPart D) _ _ hw.1 a b
  · exact map_mul_congr (infPart D) (incA D) _ _ _ hw.2 a b

theorem eFrame_move {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ}
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hψ : IsStdChar D ψ (-1))
    (hom : GlobalTheory.Ker.IsWeak ψ V W om) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) {δ κ : GA D W} (hδ : δ ∈ GQ W)
    {m : ℂ} (hκ : om (1, κ) f = m • f) (g : GA D W) (w : WO V W) :
    eFrame ψ V W om f (δ * g * κ) (actO V W 1 δ w) = m * eFrame ψ V W om f g w := by
  have e : ((1, δ * g * κ) : GA D V × GA D W) = (1, δ) * (1, g) * (1, κ) := by simp
  have hg := hom.om_pres (1, g) f hf
  have h1 := hom.om_aut 1 (one_mem _) δ hδ _ (GlobalTheory.OneMapRef.RatPt.isTheta_heisO hψ hg w)
  rw [hom.om_heis 1 δ w _ hg] at h1
  unfold eFrame
  rw [← h1, e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hκ, map_smul, map_smul]
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem isUnitFr_of_archM (W : HSp D) (X : Data D.host.E W.rank) (hX : ModelW W rfl X)
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin W.rank) (Fin W.rank) ℂ} (h0 : IsOrthogonalFrame X x₀)
    {th : X.Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hth : ∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th τ))
    (g : GA D W) (x : Frame X.Ψ W.rank)
    (hx : ∀ τ : X.Ψ, mat x τ = Matrix.reindex (finCongr rfl) (finCongr rfl) (archM W (th τ) g) * x₀ τ.1) :
    IsUnitFr X x := by
  refine ((GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular _ _ X.p0 X.Ψ X.Gm X.Gm_herm).2.1 x
    fun τ => ?_).2
  rw [← h0 τ.1 τ.2, hx τ, GlobalTheory.RecDictModel.gram_eq, GlobalTheory.RecDictModel.gram_eq, hX.1]
  have hu := GlobalTheory.RecDictModel.archM_unitary W (hth τ) g
  have e1 : ∀ A : Matrix (Fin W.rank) (Fin W.rank) ℂ, Matrix.reindex (finCongr rfl) (finCongr rfl) A = A :=
    fun A => rfl
  have e2 : ((-(Matrix.reindex (finCongr rfl) (finCongr rfl) W.gram).transpose).map τ.1).transpose =
      -(W.gram.map τ.1) := by
    ext a b; simp
  rw [e1, e2, Matrix.conjTranspose_mul]
  congr 1
  conv_rhs => rw [← hu]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

end Adelic

end GlobalTheory.FrameEquiv.GenMove

open GlobalTheory.FrameEquiv.GenMove GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws in

theorem GlobalTheory.FrameEquiv.frameConst_levelMove : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (W : HSp D) (U : Unf Xo c σ W.rank) (dict : GA D W → Σ k, Frame (U.X k).Ψ W.rank) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin W.rank) (Fin W.rank) ℂ), GeoSet W U dict x₀ → LatEmb W ι → ∀ (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (L : Lt D.host.E W.rank) (f₀ : WO V W → ℂ) (mu : GA D W → ℂ), AdSet V W ψ θ om s L f₀ mu → ∀ cc : U.Comp → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws.IsFrameConst W rfl dict ι x₀ ψ V om f₀ mu cc → ∀ (κ : GA D W) (lev levA : Dw.La →ₗ[𝓞 D.host.E] Dw.La), GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.StabLat W κ → GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.LevAgrees W ι l.M (Mfr l) κ lev → ∀ (h : GA D W) (hx : (dict h).2 ∈ (U.X (dict h).1).dom) (y' : FrPt Xo c (CAt σ)), levR (lev, levA) (U.un (dict h).1 ⟨(dict h).2, hx⟩) y' → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), ∀ f ∈ sec Xo c a V.rank, cc (dict h).1 * toC (evR Xo c f y') = cc (dict (h * κ)).1 * rdU U f (dict (h * κ)).1 (dict (h * κ)).2 := by
  intro D H Dw l Xo c σ W U dict ι x₀ hG hι V ψ θ om s L f₀ mu hAd cc hcc κ lev levA hκ hlev h hx y' hy' a f hf
  obtain ⟨⟨d, hd⟩, hall⟩ := hcc
  obtain ⟨_, ⟨γ, hγ⟩, hA⟩ := hall d hd h
  obtain ⟨hx₂, ⟨γ', hγ'⟩, hA'⟩ := hall d hd (h * κ)
  obtain ⟨⟨Pm, hPm⟩, hB⟩ := hA γ hγ
  obtain ⟨⟨Pm', hPm'⟩, hB'⟩ := hA' γ' hγ'
  obtain ⟨⟨⟨Hm, ϑ⟩, hp⟩, hC⟩ := hB Pm hPm
  obtain ⟨⟨⟨Hm', ϑ'⟩, hp'⟩, hC'⟩ := hB' Pm' hPm'
  replace hC := hC _ hp
  replace hC' := hC' _ hp'
  clear hA hA' hB hB' hall
  obtain ⟨ga, hs, hrat, hun, e1, e2, hcong⟩ :=
    GlobalTheory.FrameEquiv.LatMove.lattice_move D H Dw l Xo c σ W U dict ι x₀ hG hι d hd κ lev hκ hlev h γ γ' hγ hγ'
  obtain ⟨hσ, hU, h1, hA1, hmod, -, -, -, hor, -⟩ := hG
  obtain ⟨-, -, hom, -, -, ⟨hψ, hvac⟩, hmul, hnorm, -, hstab, -⟩ := hAd
  have hu := isUnitFr_of_archM W _ (hmod _) (hor _) (hd.1 _) _ _ hγ.2
  have hu' := isUnitFr_of_archM W _ (hmod _) (hor _) (hd.1 _) _ _ hγ'.2
  obtain ⟨Wt, hWt⟩ := GlobalTheory.FrameEquiv.hasWitness_of_is D H Dw l Xo c σ _ U hσ hU h1 W rfl dict ι x₀ d hd
  obtain ⟨g, e, F, ik, φ, th⟩ := d
  cases hWt
  have hU' := (Formalism.L2.PjFree.isUnf_ofPj U).2 hU
  have key : ∀ k : U.Comp, SelfD (U.X k) (U.X k).Λ ∧ IsMark l (U.X k).Λ (Wt.mark k) ∧
      ∃ (bas : (Fin Wt.g ⊕ Fin Wt.g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin Wt.g ≃ (U.X k).Ψ × Fin W.rank),
      IsSympl (U.X k) bas ∧
      (∀ x v j, pv (U.X k) idx x v j = perFr (U.X k) x v (relab c σ (Wt.e j).1) (Wt.e j).2) ∧
      (∀ j, rowType (U.X k) (idx j) = relab c σ (Wt.e j).1) := fun k => by
    obtain ⟨-, hsd, hmk, -⟩ := uw_lattice _ H Dw l Xo c σ _ _ hσ hU' h1 Wt k
    obtain ⟨Dc, hDc, -⟩ := exists_dic _ H Dw l c σ _ Wt.g 0 (U.X k) 0 Wt.e hσ hU.1 (hU.2.1 k).1 (hU.2.1 k).2 hsd
      ⟨fun _ => antitone_const, Even.zero⟩
    have hper := Dc.per_eq
    have hty := Dc.ty_eq
    rw [hDc] at hper hty
    exact ⟨hsd, hmk, Dc.bas, Dc.idx, Dc.sympl, hper, hty⟩
  obtain ⟨hsd, -, bas, idx, hsy, hper, hty⟩ := key (dict h).1
  obtain ⟨-, hmk', bas', idx', hsy', hper', hty'⟩ := key (dict (h * κ)).1
  let _ : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨A, hM, hR, hm1, hH⟩ := (GlobalTheory.FrameEquiv.canTheta_anFib _ H Dw l Xo c σ _ _ hσ hU' h1 Wt (dict h).1 bas idx hsy hper hty
    ⟨_, hx⟩ hu Pm (fun a j => congrFun (hPm a) j)).2 Hm ϑ hp
  obtain ⟨A₂, hM₂, hR₂, -, hH₂⟩ := (GlobalTheory.FrameEquiv.canTheta_anFib _ H Dw l Xo c σ _ _ hσ hU' h1 Wt (dict (h * κ)).1 bas' idx' hsy'
    hper' hty' ⟨_, hx₂⟩ hu' Pm' (fun a j => congrFun (hPm' a) j)).2 Hm' ϑ' hp'
  obtain ⟨t, ht, ⟨v, hv⟩, hpv, hhx, hval⟩ := values_of_move (y' := y') hs A A₂ ga hsy hsy' hx hsd hun
    (fun v => funext fun j => (hper _ v j).trans ((perFr_cast hs _ _ _ _).trans (hper' _ v j).symm))
    (fun j => (hty j).trans (hty' j).symm) hA1 e1 e2 hy' hmk' hM hM₂ hcong hR hR₂ hm1
  have hf₂ : rdU U f (dict (h * κ)).1 (dict (h * κ)).2 = t ^ V.rank * toC (evR Xo c f y') :=
    (dif_pos hx₂).trans (hval a V.rank f hf)
  obtain ⟨⟨w, hw⟩, hE⟩ := hC (Matrix.of fun i _ => v i)
  have hE1 := hE w hw
  have hE2 := (hC' _).2 _ (isRealPt_actO V W hrat hw)
  have hz : ∀ u, DictDat.coord W dict ⟨Wt.g, Wt.e, Wt.F, Wt.ik, Wt.φ, th⟩ h u = pv _ idx (dict h).2 u :=
    fun u => funext fun j => (hper _ u j).symm
  have hz' : ∀ u, DictDat.coord W dict ⟨Wt.g, Wt.e, Wt.F, Wt.ik, Wt.φ, th⟩ (h * κ) u =
      pv _ idx' (dict (h * κ)).2 u := fun u => funext fun j => (hper' _ u j).symm
  have hcol : ∀ b : Fin V.rank, (fun i => ((ga : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *
      (Matrix.of fun i _ => v i : Matrix (Fin W.rank) (Fin V.rank) D.host.E)) (Fin.cast rfl i) b) =
      (ga : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *ᵥ v := fun b => rfl
  have hcol0 : ∀ b : Fin V.rank, (fun i =>
      (Matrix.of fun i _ => v i : Matrix (Fin W.rank) (Fin V.rank) D.host.E) (Fin.cast rfl i) b) = v := fun b => rfl
  have hmove := eFrame_move hψ hom hvac.theta (mul_mem hγ'.1.1 (inv_mem hγ.1.1)) (hstab κ hκ) (γ * h) w
  have eg : γ' * γ⁻¹ * (γ * h) * κ = γ' * (h * κ) := by group
  rw [eg] at hmove
  have hHH : ∀ z z', hermForm Hm' z z' = hermForm Hm z z' :=
    fun z z' => (hH₂ z z').trans ((hhx z z').trans (hH z z').symm)
  replace hpv : ∀ u, pv (U.X (dict (h * κ)).1) idx' (dict (h * κ)).2
      ((ga : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *ᵥ u) = pv (U.X (dict h).1) idx (dict h).2 u := hpv
  replace hv : ϑ (pv (U.X (dict h).1) idx (dict h).2 v) ≠ 0 := hv
  simp only [hz, hz', hcol, hcol0, hpv, hHH, hmove, hmul, ht, Pi.smul_apply, smul_eq_mul, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, mul_pow] at hE1 hE2
  have n1 : mu h ≠ 0 := norm_ne_zero_iff.1 (by rw [hnorm]; exact one_ne_zero)
  have n2 : mu κ ≠ 0 := norm_ne_zero_iff.1 (by rw [hnorm]; exact one_ne_zero)
  have hc : cc (dict h).1 = cc (dict (h * κ)).1 * t ^ V.rank := by
    apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero n1 n2) (pow_ne_zero V.rank hv))
    linear_combination hE2 - mu κ * hE1
  rw [hf₂, hc, mul_assoc]
end
