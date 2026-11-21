import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteOnCompactsOrbitMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureGLRightScaling
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LawOfOrbitMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureUnitaryGroupInvariant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureIntegralPointsNonzero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainProperty
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatAdelicMatrixContinuousLeMajorant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbscissaConvergenceIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinedBlockFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralShiftHerm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBoundFiniteInfinite
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IkedaPartialFourierIntegralMemAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactAverageSchwartzProjectionMemAdelicSchwartStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstTermExistenceOfUniversal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableThetaKernelProduct

section
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ColumnSplitting

variable {D : D7}

theorem continuous_adjM {a b : ℕ} : Continuous (adj : Mx D a b → Mx D b a) := by
  have hc : Continuous (cA D) := GlobalTheory.FockCompare.ThetaCont.continuous_conj
  exact (continuous_id.matrix_map hc).matrix_transpose

theorem continuous_ipM {X : Type} [TopologicalSpace X] (V : HSp D) {a b : ℕ} {f : X → Mx D V.rank a}
    {g : X → Mx D V.rank b} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => ip V (f x) (g x) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact (continuous_adjM.comp hf).matrix_mul (continuous_const.matrix_mul hg)

theorem continuous_qvM (V : HSp D) {r t : ℕ} (b₀ : HermE D r) :
    Continuous (qv (t := t) V b₀) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hT := (top_mx (D := D) t t).1
  have hy : Continuous (yv (t := t) V b₀) :=
    continuous_const.matrix_mul (continuous_ipM V continuous_fst continuous_snd)
  have h2 : Continuous fun z : Mx D V.rank r × Mx D V.rank t => ip V z.2 z.2 :=
    continuous_ipM V continuous_snd continuous_snd
  have h3 : Continuous fun z : Mx D V.rank r × Mx D V.rank t =>
      pr b₀ (yv V b₀ z) (yv V b₀ z) :=
    (continuous_adjM.comp hy).matrix_mul (continuous_const.matrix_mul hy)
  have hs : ContinuousSub (Mx D t t) := @IsTopologicalAddGroup.to_continuousSub _ _ _ hT
  exact h2.sub h3

theorem nuT_supp : ZpEq → AcEq → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ (b₀ : HermE D W.rank), b₀.1.det ≠ 0 → ∀ x₀, gramQ W x₀ = b₀.1 → nuT hn I μ x₀ {z | ¬ ((1 : AE D) • z.1 = z.1 ∧ (1 : AE D) • z.2 = z.2 ∧ ip B z.1 z.1 = (1 : AE D) • rat b₀.1 ∧ qv B b₀ z = 0)} = 0 := by
  intro hZ hA D n t B W d hn I μ _ b₀ hb x₀ hx
  obtain ⟨g1, -⟩ := top_pair (D := D) B.rank W.rank t
  have o1 : OpensMeasurableSpace (Mx D B.rank W.rank × Mx D B.rank t) := g1.opensMeasurable
  have t1 := (top_mx (D := D) W.rank W.rank).2.2.2.1
  have t2 := (top_mx (D := D) t t).2.2.2.1
  have hcl : IsClosed {z : Mx D B.rank W.rank × Mx D B.rank t |
      ip B z.1 z.1 = rat b₀.1 ∧ qv B b₀ z = 0} :=
    (isClosed_eq (continuous_ipM B continuous_fst continuous_fst)
      continuous_const).inter (isClosed_eq (continuous_qvM B b₀) continuous_const)
  have hS : {z : Mx D B.rank W.rank × Mx D B.rank t | ¬ ((1 : AE D) • z.1 = z.1 ∧ (1 : AE D) • z.2 = z.2 ∧
      ip B z.1 z.1 = (1 : AE D) • rat b₀.1 ∧ qv B b₀ z = 0)} =
      {z | ip B z.1 z.1 = rat b₀.1 ∧ qv B b₀ z = 0}ᶜ := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, one_smul, true_and]
  rw [hS]
  unfold nuT
  rw [Measure.map_apply (measurable_pi hn I x₀) hcl.measurableSet.compl]
  have hE : (fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)) ⁻¹'
      {z | ip B z.1 z.1 = rat b₀.1 ∧ qv B b₀ z = 0}ᶜ = ∅ := by
    ext p
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    obtain ⟨a1, -, a3⟩ := hA D W.rank t B b₀ ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)
    obtain ⟨z1, -, z3⟩ := hZ D n t B W d hn b₀ hb x₀ hx p.2
    exact ⟨a1.trans z1, a3.trans z3⟩
  rw [hE, measure_empty]

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_measure_concentrated_on_quadric : ZpEq → AcEq → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ (b₀ : HermE D W.rank), b₀.1.det ≠ 0 → ∀ x₀, gramQ W x₀ = b₀.1 → nuT hn I μ x₀ {z | ¬ ((1 : AE D) • z.1 = z.1 ∧ (1 : AE D) • z.2 = z.2 ∧ ip B z.1 z.1 = (1 : AE D) • rat b₀.1 ∧ qv B b₀ z = 0)} = 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ColumnSplitting.nuT_supp
end

section
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem nuT_shear_invariant : ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n)
    (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ x₀ (y : Mx D W.rank t),
    (nuT hn I μ x₀).map (fun z => (z.1, z.2 + mm z.1 y)) = nuT hn I μ x₀ := by
  intro D n t B W d hn I μ hμ x₀ y
  have hring := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨i1, i2, i3, i4, i5⟩ := top_mx (D := D) W.rank t
  obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) t n
  obtain ⟨k1, -, -, -, -⟩ := top_mx (D := D) B.rank t
  obtain ⟨-, g2, g3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have : BorelSpace (GA D W) := ⟨rfl⟩
  obtain ⟨hc, 𝓕, hf⟩ := I.cov₁
  have := hf.1
  have := I.haar
  have := I.probK
  have hQ := sigmaFinite_parameter_product_measure I μ hμ
  obtain ⟨p1, p2⟩ := top_pair (D := D) B.rank W.rank t
  have o1 : OpensMeasurableSpace (Mx D B.rank W.rank × Mx D B.rank t) := p1.opensMeasurable
  have hS : Measurable fun z : Mx D B.rank W.rank × Mx D B.rank t => (z.1, z.2 + mm z.1 y) :=
    (continuous_fst.prodMk (continuous_snd.add (continuous_fst.matrix_mul continuous_const))).measurable
  have hτ : MeasurePreserving (fun p : I.l.K × Par D n t W => (p.1, p.2.1, p.2.2.1, p.2.2.2 + y))
      (I.νK.prod (Q0 I μ)) (I.νK.prod (Q0 I μ)) := by
    unfold Q0
    exact (MeasurePreserving.id _).prod ((MeasurePreserving.id _).prod
      ((MeasurePreserving.id _).prod (measurePreserving_add_right μ y)))
  have hπ := measurable_pi (d := d) hn I x₀
  have hcomp : (fun z : Mx D B.rank W.rank × Mx D B.rank t => (z.1, z.2 + mm z.1 y)) ∘
        (fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)) =
      (fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)) ∘
        (fun p : I.l.K × Par D n t W => (p.1, p.2.1, p.2.2.1, p.2.2.2 + y)) := by
    funext p
    refine Prod.ext rfl ?_
    have key : ∀ {a b c : ℕ} (g : Mx D a a) (ξ : Mx D a b) (u : Mx D a c) (y' y : Mx D b c),
        mm g (mm ξ y' + u) + mm (mm g ξ) y = mm g (mm ξ (y' + y) + u) := by
      intro a b c g ξ u y' y
      simp only [mm, Matrix.mul_add, Matrix.mul_assoc]
      abel
    exact key _ _ _ _ _
  unfold nuT
  rw [Measure.map_map hS hπ, hcomp, ← Measure.map_map hπ hτ.measurable, hτ.map_eq]

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_measure_translation_invariant : ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ x₀ (y : Mx D W.rank t), (nuT hn I μ x₀).map (fun z => (z.1, z.2 + mm z.1 y)) = nuT hn I μ x₀ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ColumnSplitting.nuT_shear_invariant
end

section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_measure_integral_points_nonzero : ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ x₀, ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → nuT hn I μ x₀ {z | IntOff S z.1 ∧ IntOff S z.2} ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.nuT_intOff_ne_zero | exact GlobalTheory.CompanionTheory.ColumnSplitting.nuT_intOff_ne_zero | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.nuT_intOff_ne_zero <;> assumption)
end

section
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem orbFin_of_latBound : LatBound → OrbFin := by
  intro hL D θ hθ W m hm x₀ hx N hN
  obtain ⟨C, hC⟩ := hL D θ hθ W W.rank N hN
  have hB : BorelSpace (GA D W) := ⟨rfl⟩
  obtain ⟨-, g2, g3, -, h5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hfd : IsFundamentalDomain (GQ W) (stdDom (GQ W)) m := isFundamentalDomain_stdDom _ m
  have hfin := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol W m _ hm hfd
  have hcnt : Countable (GQ W) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig W.gram
  have hNc : Continuous N :=
    (GlobalTheory.SchwartzMaj.continuous_and_le_maj D θ hθ W.rank W.rank N
      (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ W.rank W.rank N hN)).1
  have hfm : Measurable fun h : GA D W => ‖N (ww W x₀ h)‖ₑ :=
    (hNc.comp (continuous_ww x₀)).enorm.measurable

  classical
  have hu : ∀ γ : GQ W, ∃ u : GL (Fin W.rank) D.host.E, mt W γ.1 = rat u.1 := fun γ => by
    obtain ⟨u, -, hu⟩ := γ.2
    exact ⟨u, (congrArg Units.val hu).symm⟩
  choose u hu using hu
  have hxu : IsUnit x₀.det := isUnit_iff_ne_zero.2 hx
  have hrk : ∀ γ : GQ W, ((u γ).1 * x₀).rank = W.rank := fun γ => by
    have h1 : IsUnit ((u γ).1 * x₀) := by
      refine (Matrix.isUnit_iff_isUnit_det _).2 ?_
      rw [Matrix.det_mul]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 (u γ).isUnit).mul hxu
    simpa using Matrix.rank_of_isUnit _ h1
  let e : GQ W → {x : Matrix (Fin W.rank) (Fin W.rank) D.host.E // x.rank = W.rank} :=
    fun γ => ⟨(u γ).1 * x₀, hrk γ⟩
  have he : Function.Injective e := fun γ γ' h => by
    have h1 : (u γ).1 * x₀ = (u γ').1 * x₀ := congrArg Subtype.val h
    have h2 : (u γ).1 = (u γ').1 := by
      have hxi : x₀ * x₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hxu
      calc (u γ).1 = (u γ).1 * x₀ * x₀⁻¹ := by rw [Matrix.mul_assoc, hxi, Matrix.mul_one]
        _ = (u γ').1 * x₀ * x₀⁻¹ := by rw [h1]
        _ = (u γ').1 := by rw [Matrix.mul_assoc, hxi, Matrix.mul_one]
    exact Subtype.ext (GlobalTheory.MixModel.mt_injective W (by rw [hu, hu, h2]))
  have hterm : ∀ (γ : GQ W) (h : GA D W), ‖N (ww W x₀ (γ⁻¹ • h))‖ₑ = ‖N (mm (mt W h⁻¹) (rat (e γ).1))‖ₑ := fun γ h => by
    have h1 : (γ⁻¹ • h)⁻¹ = h⁻¹ * γ.1 := by
      change ((γ.1)⁻¹ * h)⁻¹ = _
      rw [mul_inv_rev, inv_inv]
    have h2 : mt W (h⁻¹ * γ.1) = mt W h⁻¹ * mt W γ.1 := rfl
    have h3 : ww W x₀ (γ⁻¹ • h) = mm (mt W h⁻¹) (rat (e γ).1) := by
      simp only [ww, e]
      rw [h1, h2, hu, rat_mul]
      exact Matrix.mul_assoc _ _ _
    rw [h3]
  rw [hfd.lintegral_eq_tsum']
  rw [← lintegral_tsum fun γ => ?_]
  · calc ∫⁻ h in stdDom (GQ W), ∑' γ : GQ W, ‖N (ww W x₀ (γ⁻¹ • h))‖ₑ ∂m
        ≤ ∫⁻ _ in stdDom (GQ W), (C : ℝ≥0∞) ∂m := lintegral_mono fun h => by
          simp only [hterm]
          exact (ENNReal.tsum_comp_le_tsum_of_injective he
            (fun x => ‖N (mm (mt W h⁻¹) (rat x.1))‖ₑ)).trans (hC h)
      _ = C * m (stdDom (GQ W)) := by simp
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top hfin
  · exact (hfm.comp (measurable_const_smul γ⁻¹)).aemeasurable

end GlobalTheory.CompanionTheory.ColumnSplitting
end
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_finiteness_of_lattice_bound : LatBound → OrbFin := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ColumnSplitting.orbFin_of_latBound
end

section
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ColumnSplitting

variable {D : D7} {n t : ℕ} {B W : HSp D}

theorem sand {k l a b c : ℕ} (G : Mx D k k) (x : Mx D k l) (u : Mx D l a) (y : Mx D k b) (v : Mx D b c) :
    adj (x ⬝ u) ⬝ (G ⬝ (y ⬝ v)) = adj u ⬝ ((adj x ⬝ (G ⬝ y)) ⬝ v) := by
  simp only [adj_mul, Matrix.mul_assoc]

theorem gram_ww (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h : GA D W) :
    adj (ww W x₀ h) ⬝ (gA W ⬝ ww W x₀ h) = rat (gramQ W x₀) := by
  have hu := mt_unitary W h⁻¹
  have hr : adj (rat x₀) ⬝ (gA W ⬝ rat x₀) = rat (gramQ W x₀) :=
    gram_rat W (a := x₀) (b := x₀) (c := gramQ W x₀) (by
      show x₀ᴴ * W.gram * x₀ = x₀ᴴ * (W.gram * x₀)
      rw [Matrix.mul_assoc])
  have e : adj (ww W x₀ h) ⬝ (gA W ⬝ ww W x₀ h)
      = adj (rat x₀) ⬝ ((adj (mt W h⁻¹) ⬝ (gA W ⬝ mt W h⁻¹)) ⬝ rat x₀) :=
    sand (gA W) (mt W h⁻¹) (rat x₀) (mt W h⁻¹) (rat x₀)
  rw [e, hu, hr]

theorem frame_perp (d : HypDec B W t) {a c : ℕ} (u : Mx D t a) (w : Mx D W.rank a) (v : Mx D t c) :
    adj (d.jX ⬝ u + d.j0 ⬝ w) ⬝ (gA B ⬝ (d.jX ⬝ v)) = 0 := by
  rw [adj_add, Matrix.add_mul, sand, sand, d.gram_XX, d.gram_0X]
  simp

theorem frame_gram (d : HypDec B W t) {a : ℕ} (u : Mx D t a) (w : Mx D W.rank a) :
    adj (d.jX ⬝ u + d.j0 ⬝ w) ⬝ (gA B ⬝ (d.jX ⬝ u + d.j0 ⬝ w)) = adj w ⬝ (gA W ⬝ w) := by
  have h1 := frame_perp d u w u
  have h2 : adj (d.jX ⬝ u + d.j0 ⬝ w) ⬝ (gA B ⬝ (d.j0 ⬝ w)) = adj w ⬝ (gA W ⬝ w) := by
    rw [adj_add, Matrix.add_mul, sand, sand, d.wittDecomp_gram_X_anisotropic, d.gram_00]
    simp
  rw [Matrix.mul_add, Matrix.mul_add, h1, h2, zero_add]

theorem pair_gram (d : HypDec B W t) (b₀ : HermE D W.rank) (hdet : b₀.1.det ≠ 0) (ξ : Mx D B.rank W.rank) (v : Mx D t t)
    (y : Mx D W.rank t) (hg : adj ξ ⬝ (gA B ⬝ ξ) = rat b₀.1) (hp : adj ξ ⬝ (gA B ⬝ (d.jX ⬝ v)) = 0) :
    yv B b₀ (ξ, ξ ⬝ y + d.jX ⬝ v) = y ∧ qv B b₀ (ξ, ξ ⬝ y + d.jX ⬝ v) = 0 := by
  have h2 : adj ξ ⬝ (gA B ⬝ (ξ ⬝ y + d.jX ⬝ v)) = rat b₀.1 ⬝ y := by
    rw [Matrix.mul_add, Matrix.mul_add, hp, add_zero, ← Matrix.mul_assoc (gA B), ← Matrix.mul_assoc (adj ξ), hg]
  have hinv : rat b₀.1⁻¹ ⬝ rat b₀.1 = (1 : Mx D W.rank W.rank) := by
    rw [← rat_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet), rat_one]
  have h3 : yv B b₀ (ξ, ξ ⬝ y + d.jX ⬝ v) = y := by
    show rat b₀.1⁻¹ ⬝ (adj ξ ⬝ (gA B ⬝ (ξ ⬝ y + d.jX ⬝ v))) = y
    rw [h2, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  have hxξ : adj (d.jX ⬝ v) ⬝ (gA B ⬝ ξ) = 0 := by
    have := gram_swap B hp
    rwa [adj_zero] at this
  have hxx : adj (d.jX ⬝ v) ⬝ (gA B ⬝ (d.jX ⬝ v)) = 0 := by
    rw [sand, d.gram_XX]
    simp
  have hq : adj (d.jX ⬝ v) ⬝ (gA B ⬝ (ξ ⬝ y + d.jX ⬝ v)) = 0 := by
    rw [Matrix.mul_add, Matrix.mul_add, hxx, add_zero, ← Matrix.mul_assoc (gA B), ← Matrix.mul_assoc (adj (d.jX ⬝ v)),
      hxξ, Matrix.zero_mul]
  have h4 : ip B (ξ ⬝ y + d.jX ⬝ v) (ξ ⬝ y + d.jX ⬝ v) = adj y ⬝ (rat b₀.1 ⬝ y) := by
    show adj (ξ ⬝ y + d.jX ⬝ v) ⬝ (gA B ⬝ (ξ ⬝ y + d.jX ⬝ v)) = _
    rw [adj_add, Matrix.add_mul, hq, add_zero, adj_mul ξ y, Matrix.mul_assoc, h2]
  refine ⟨h3, ?_⟩
  show ip B (ξ ⬝ y + d.jX ⬝ v) (ξ ⬝ y + d.jX ⬝ v)
    - pr b₀ (yv B b₀ (ξ, ξ ⬝ y + d.jX ⬝ v)) (yv B b₀ (ξ, ξ ⬝ y + d.jX ⬝ v)) = 0
  rw [h3, h4]
  exact sub_eq_zero.2 rfl

theorem zp_eq : ZpEq := by
  intro D n t B W d hn b₀ hdet x₀ hx p
  have hg : adj (d.jX ⬝ c1 hn p.2.1 + d.j0 ⬝ ww W x₀ p.1) ⬝ (gA B ⬝ (d.jX ⬝ c1 hn p.2.1 + d.j0 ⬝ ww W x₀ p.1)) = rat b₀.1 := by
    rw [frame_gram, gram_ww, hx]
  have hp := frame_perp d (c1 hn p.2.1) (ww W x₀ p.1) (c2 hn p.2.1)
  obtain ⟨h3, h5⟩ := pair_gram d b₀ hdet _ (c2 hn p.2.1) p.2.2 hg hp
  exact ⟨hg, h3, h5⟩

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zeta_polynomial_identity : ZpEq := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ColumnSplitting.zp_eq
end

section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abscissa_convergence_identity : AcEq := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.GramAct.acEq | exact GlobalTheory.CompanionTheory.ColumnSplitting.GramAct.acEq | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.GramAct.acEq <;> assumption)
end

section
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.CompanionTheory.ColumnSplitting.JnM

variable {D : D7} {a b r t n : ℕ}

theorem fromCols_mul_shear {R : Type} [Ring R] (w : Matrix (Fin a) (Fin r) R) (v : Matrix (Fin a) (Fin t) R)
    (y : Matrix (Fin r) (Fin t) R) :
    (Matrix.fromCols w v : Matrix (Fin a) (Fin r ⊕ Fin t) R) *
        (Matrix.fromBlocks 1 y 0 1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R) =
      Matrix.fromCols w (w * y + v) := by
  ext i (k | k) <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem mm_jn (hn : r + t = n) (A : Mx D b a) (x : Mx D a r) (v : Mx D a t) :
    mm A (jn hn x v) = jn hn (mm A x) (mm A v) := by
  ext i j
  simp only [jn, mm, Matrix.submatrix_apply, id, Matrix.mul_apply]
  rcases h : (finSumFinEquiv.trans (finCongr hn)).symm j with k | k <;>
    simp [Matrix.mul_apply]

theorem jn_add (hn : r + t = n) (x x' : Mx D a r) (v v' : Mx D a t) :
    jn hn x v + jn hn x' v' = jn hn (x + x') (v + v') := by
  ext i j
  simp only [jn, Matrix.add_apply, Matrix.submatrix_apply, id]
  rcases h : (finSumFinEquiv.trans (finCongr hn)).symm j with k | k <;> simp

theorem jn_c {W : HSp D} (hn : W.rank + t = n) (U : Mx D a n) :
    jn hn (c1 hn U) (c2 hn U) = U := by
  ext i j
  obtain ⟨s, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective j
  rcases s with k | k <;> simp [jn, c1, c2]

theorem shear_gen {R : Type} [Ring R] (hn : r + t = n) (w : Matrix (Fin a) (Fin r) R)
    (v : Matrix (Fin a) (Fin t) R) (y : Matrix (Fin r) (Fin t) R) :
    ((Matrix.fromCols w v).submatrix id (finSumFinEquiv.trans (finCongr hn)).symm : Matrix (Fin a) (Fin n) R) *
        ((Matrix.fromBlocks 1 y 0 1).submatrix (finSumFinEquiv.trans (finCongr hn)).symm
          (finSumFinEquiv.trans (finCongr hn)).symm : Matrix (Fin n) (Fin n) R) =
      (Matrix.fromCols w (w * y + v)).submatrix id (finSumFinEquiv.trans (finCongr hn)).symm := by
  rw [Matrix.submatrix_mul_equiv, fromCols_mul_shear]

theorem jn_bl (hn : r + t = n) (w : Mx D a r) (v : Mx D a t) (y : Mx D r t) :
    mm (jn hn w v) (bl hn 1 y 0 1) = jn hn w (mm w y + v) :=
  shear_gen hn w v y

end GlobalTheory.CompanionTheory.ColumnSplitting.JnM

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem jnPi_holds : JnPi := by
  intro D n t B W d hn x₀ g p
  obtain ⟨h, U, y⟩ := p
  have hX : XU d hn x₀ h U =
      jn hn (mm d.jX (c1 hn U) + mm d.j0 (ww W x₀ h)) (mm d.jX (c2 hn U)) := by
    unfold XU
    conv_lhs => rw [← JnM.jn_c (W := W) hn U]
    have h0 : mm d.j0 (0 : Mx D W.rank t) = 0 := Matrix.mul_zero _
    rw [JnM.mm_jn, JnM.mm_jn, JnM.jn_add, h0, add_zero]
  simp only [hX, JnM.jn_bl, JnM.mm_jn]
  rfl

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.joined_projection_formula : JnPi := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ColumnSplitting.jnPi_holds
end

section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.joined_block_formula : JnBl := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.jnBl | exact GlobalTheory.CompanionTheory.ColumnSplitting.jnBl | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.jnBl <;> assumption)
end

section
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem map_cols0 {R S : Type*} [Zero R] [Zero S] {a r t n : ℕ} (f : R → S) (hf : f 0 = 0)
    (e : Fin n ≃ Fin r ⊕ Fin t) (x : Matrix (Fin a) (Fin r) R) :
    ((Matrix.fromCols x (0 : Matrix (Fin a) (Fin t) R)).submatrix id e).map f =
      (Matrix.fromCols (x.map f) (0 : Matrix (Fin a) (Fin t) S)).submatrix id e := by
  ext i j
  simp only [Matrix.map_apply, Matrix.submatrix_apply, id]
  rcases e j with k | k
  · simp
  · simp [hf]

theorem mul_cols0 {R : Type*} [NonUnitalNonAssocSemiring R] {a b r t n : ℕ}
    (e : Fin n ≃ Fin r ⊕ Fin t) (A : Matrix (Fin a) (Fin b) R) (x : Matrix (Fin b) (Fin r) R) :
    A * (Matrix.fromCols x (0 : Matrix (Fin b) (Fin t) R)).submatrix id e =
      (Matrix.fromCols (A * x) (0 : Matrix (Fin a) (Fin t) R)).submatrix id e := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
  rcases e j with k | k
  · simp [Matrix.mul_apply]
  · simp

theorem extension_by_zero_orbit_action : Ext0 := by
  intro D n t W hn x₀ h
  have h1 : (rat (L.ext0 hn x₀) : Matrix (Fin W.rank) (Fin n) (AE D)) =
      (Matrix.fromCols (rat x₀ : Matrix (Fin W.rank) (Fin W.rank) (AE D))
        (0 : Matrix (Fin W.rank) (Fin t) (AE D))).submatrix id (finSumFinEquiv.trans (finCongr hn)).symm :=
    map_cols0 (incA D) (map_zero _) _ x₀
  have h2 := mul_cols0 (t := t) (finSumFinEquiv.trans (finCongr hn)).symm (mt W h⁻¹)
    (rat x₀ : Matrix (Fin W.rank) (Fin W.rank) (AE D))
  exact (congrArg (fun M => mt W h⁻¹ * M) h1).trans h2

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extension_by_zero_orbit_formula : Ext0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ColumnSplitting.extension_by_zero_orbit_action
end

section
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.ColumnSplitting.ShiftP
section Generic
variable {R : Type} [CommRing R] {r t n : ℕ}

theorem upperUnipotent_mul (hn : r + t = n) (y y' : Matrix (Fin r) (Fin t) R) :
    bl hn 1 y 0 1 * bl hn 1 y' 0 1 = bl hn 1 (y + y') 0 1 := by
  unfold bl
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [add_comm]

theorem upperUnipotent_zero (hn : r + t = n) : bl hn (1 : Matrix (Fin r) (Fin r) R) 0 0 1 = 1 := by
  unfold bl
  rw [Matrix.fromBlocks_one]
  exact Matrix.submatrix_one_equiv _

theorem det_bl_one (hn : r + t = n) (y : Matrix (Fin r) (Fin t) R) : (bl hn 1 y 0 1).det = 1 := by
  unfold bl
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  simp

end Generic

variable {D : D7} {n t : ℕ} {B W : HSp D}

def shear {r : ℕ} (hn : r + t = n) (y : Mx D r t) : GL (Fin n) (AE D) where
  val := bl hn 1 y 0 1
  inv := bl hn 1 (-y) 0 1
  val_inv := by rw [upperUnipotent_mul, add_neg_cancel, upperUnipotent_zero]
  inv_val := by rw [upperUnipotent_mul, neg_add_cancel, upperUnipotent_zero]

theorem det_shear {r : ℕ} (hn : r + t = n) (y : Mx D r t) :
    Matrix.GeneralLinearGroup.det (shear (D := D) hn y : GL (Fin n) (AE D)) = 1 :=
  Units.ext (det_bl_one hn y)

theorem integral_shear {r : ℕ} (hn : r + t = n) (y : Mx D r t) {m : ℕ} (μ : Measure (Mx D m n)) (hμ : μ.IsAddHaarMeasure)
    (f : Mx D m n → ℂ) : ∫ U, f (mm U (bl hn 1 y 0 1)) ∂μ = ∫ U, f U ∂μ := by
  have h := GlobalTheory.CompanionTheory.IwaAd.integral_mul_right m μ hμ (shear hn y) f
  rw [det_shear, map_one, one_npow, one_mul] at h
  exact h

end GlobalTheory.CompanionTheory.ColumnSplitting.ShiftP

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem shift : Shift := by
  intro D n t B W d hn I Φ y a
  obtain ⟨𝓕, hf⟩ := I.cov₁
  have e := ShiftP.integral_shear hn y I.μ₁ hf.1
    (fun U => projS I.νK Φ (d.jX ⬝ U + d.j0 ⬝ (mm a (bl hn 1 y 0 1))))
  simp only [ikp, ikS]
  rw [← e]
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  simp only [projS]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  simp only [mm, Matrix.mul_assoc, Matrix.add_mul]

end GlobalTheory.CompanionTheory.ColumnSplitting
end
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_shift_invariance : Shift := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ColumnSplitting.shift
end

section
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting.IkLintProof

theorem integral_nonneg_real {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hn : ∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) : 0 ≤ (∫ x, f x ∂μ).re ∧ (∫ x, f x ∂μ).im = 0 := by
  have e2 : ∫ x, f x ∂μ = ((∫ x, (f x).re ∂μ : ℝ) : ℂ) := by
    refine Eq.trans (integral_congr_ae (ae_of_all _ fun x => ?_)) integral_complex_ofReal
    exact Complex.ext (by simp) (by simp [(hn x).2])
  rw [e2]
  exact ⟨by simpa using integral_nonneg fun x => (hn x).1, by simp⟩

theorem lintegral_enorm_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ} (hf : Integrable f μ)
    (hn : ∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) : ∫⁻ x, ‖f x‖ₑ ∂μ = ‖∫ x, f x ∂μ‖ₑ := by
  have e : ∀ x, f x = ((f x).re : ℂ) := fun x => Complex.ext (by simp) (by simp [(hn x).2])
  have hr : Integrable (fun x => (f x).re) μ := hf.re
  have h0 : 0 ≤ ∫ x, (f x).re ∂μ := integral_nonneg fun x => (hn x).1
  have e2 : ∫ x, f x ∂μ = ((∫ x, (f x).re ∂μ : ℝ) : ℂ) := by
    exact Eq.trans (integral_congr_ae (ae_of_all _ e)) integral_complex_ofReal
  have e3 : ∀ x, ‖f x‖ₑ = ENNReal.ofReal (f x).re := fun x => by
    conv_lhs => rw [e x]
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (hn x).1]
  rw [lintegral_congr e3, ← ofReal_integral_eq_lintegral_ofReal hr (ae_of_all _ fun x => (hn x).1), e2,
    ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg h0]

variable {D : D7}

theorem integrable_ik {θ : InfFam D} (hθ : IsInfFam θ) {T T' : HSp D} {t n : ℕ} (d : HypDec T T' t)
    (μ : Measure (Mx D t n)) [μ.IsAddHaarMeasure] {Φ : Mx D T.rank n → ℂ} (hΦ : Φ ∈ schwartzA θ T.rank n)
    (a : Mx D T'.rank n) : Integrable (fun x : Mx D t n => Φ (d.jX ⬝ x + d.j0 ⬝ a)) μ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, h⟩ := h
    exact (GlobalTheory.RegSch.IkSchwartz.pure d hθ μ f g hg Φ h).1 a
  | zero => exact integrable_zero _ _ _
  | add Φ Ψ _ _ h1 h2 => exact h1.add h2
  | smul c Φ _ h => exact h.smul c

theorem integrable_K {T : HSp D} {n : ℕ} {K : Subgroup (GA D T)} (hK : IsCompact (K : Set (GA D T))) (ν : Measure K)
    [IsProbabilityMeasure ν] {Φ : Mx D T.rank n → ℂ} (hΦ : Continuous Φ) (x : Mx D T.rank n) :
    Integrable (fun k : K => Φ (mm (mt T ((k : GA D T)⁻¹)) x)) ν := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨-, k2, -, -, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T
  have hB : BorelSpace (GA D T) := ⟨rfl⟩
  have hKB : BorelSpace K := Subtype.borelSpace _
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hc : Continuous fun k : K => Φ (mm (mt T ((k : GA D T)⁻¹)) x) :=
    hΦ.comp (((continuous_mt T).comp continuous_subtype_val.inv).matrix_mul continuous_const)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

end GlobalTheory.CompanionTheory.ColumnSplitting.IkLintProof

namespace GlobalTheory.CompanionTheory.ColumnSplitting

open IkLintProof in

theorem ikLint : IkLint := by
  intro D n t B W d I θ hθ M hM hn a
  haveI := I.probK
  obtain ⟨𝓕, hμ⟩ := I.cov₁
  haveI := hμ.1
  have hK := (GlobalTheory.RegSch.FirstTermCompare.hasIw_of_good d I.good).2
  have hP : projS I.νK M ∈ schwartzA θ B.rank n := GlobalTheory.T.compactAverageSchwartzProjection_mem_adelicSchwartz D θ hθ B n I.l.K hK I.νK I.probK _ hM
  have hc : Continuous M := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ M hM).1
  have hi := fun x => integrable_K hK I.νK hc x
  have inner : ∀ x, ∫⁻ k : I.l.K, ‖M (mm (mt B ((k : GA D B)⁻¹)) x)‖ₑ ∂I.νK = ‖projS I.νK M x‖ₑ :=
    fun x => lintegral_enorm_eq (hi x) fun k => hn _
  have pos : ∀ x, 0 ≤ (projS I.νK M x).re ∧ (projS I.νK M x).im = 0 :=
    fun x => integral_nonneg_real fun k => hn _
  rw [lintegral_congr fun U => inner _]
  exact lintegral_enorm_eq (integrable_ik hθ d I.μ₁ hP a) fun U => pos _

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_section_local_integrability : IkLint := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ColumnSplitting.ikLint
end

section
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ColumnSplitting

section Fub4Proof

variable {α β γ δ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]

theorem integral_prod_three (b : Measure β) (c : Measure γ) (a : Measure α) [SFinite a] [SFinite b] [SFinite c]
    (g : β × γ × α → ℂ) (hg : Integrable g (b.prod (c.prod a))) :
    ∫ q, g q ∂(b.prod (c.prod a)) = ∫ h, ∫ u, ∫ k, g (h, u, k) ∂a ∂c ∂b := by
  rw [integral_prod _ hg]
  refine integral_congr_ae ?_
  filter_upwards [hg.prod_right_ae] with h hh
  exact integral_prod _ hh

theorem integral_prod_four (e : Measure δ) (b : Measure β) (c : Measure γ) (a : Measure α)
    [SFinite a] [SFinite b] [SFinite c] [SFinite e]
    (g : δ × β × γ × α → ℂ) (hg : Integrable g (e.prod (b.prod (c.prod a)))) :
    ∫ q, g q ∂(e.prod (b.prod (c.prod a))) = ∫ y, ∫ h, ∫ u, ∫ k, g (y, h, u, k) ∂a ∂c ∂b ∂e := by
  rw [integral_prod _ hg]
  refine integral_congr_ae ?_
  filter_upwards [hg.prod_right_ae] with y hy
  exact integral_prod_three b c a _ hy

theorem lintegral_prod_four (e : Measure δ) (b : Measure β) (c : Measure γ) (a : Measure α)
    [SFinite a] [SFinite b] [SFinite c] [SFinite e]
    (g : δ × β × γ × α → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ q, g q ∂(e.prod (b.prod (c.prod a))) = ∫⁻ y, ∫⁻ h, ∫⁻ u, ∫⁻ k, g (y, h, u, k) ∂a ∂c ∂b ∂e := by
  rw [lintegral_prod _ hg.aemeasurable]
  refine lintegral_congr fun y => ?_
  have h1 : Measurable fun q : β × γ × α => g (y, q) := hg.comp measurable_prodMk_left
  rw [lintegral_prod _ h1.aemeasurable]
  refine lintegral_congr fun h => ?_
  have h2 : Measurable fun q : γ × α => g (y, h, q) := h1.comp measurable_prodMk_left
  exact lintegral_prod _ h2.aemeasurable

def swapFour (α β γ δ : Type) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ] :
    (α × β × γ × δ) ≃ᵐ (δ × β × γ × α) where
  toFun p := (p.2.2.2, p.2.1, p.2.2.1, p.1)
  invFun p := (p.2.2.2, p.2.1, p.2.2.1, p.1)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    dsimp only [Equiv.coe_fn_mk]
    fun_prop
  measurable_invFun := by
    dsimp only [Equiv.coe_fn_symm_mk]
    fun_prop

theorem measurePreserving_swapFour (a : Measure α) (b : Measure β) (c : Measure γ) (e : Measure δ)
    [SFinite a] [SFinite b] [SFinite c] [SFinite e] :
    MeasurePreserving (swapFour α β γ δ) (a.prod (b.prod (c.prod e))) (e.prod (b.prod (c.prod a))) := by
  have p1 : MeasurePreserving (Prod.map id (MeasurableEquiv.prodAssoc (α := β) (β := γ) (γ := δ)).symm)
      (a.prod (b.prod (c.prod e))) (a.prod ((b.prod c).prod e)) :=
    (MeasurePreserving.id a).prod ((measurePreserving_prodAssoc b c e).symm _)
  have p2 : MeasurePreserving (MeasurableEquiv.prodAssoc (α := α) (β := β × γ) (γ := δ)).symm
      (a.prod ((b.prod c).prod e)) ((a.prod (b.prod c)).prod e) :=
    (measurePreserving_prodAssoc a (b.prod c) e).symm _
  have p3 : MeasurePreserving Prod.swap ((a.prod (b.prod c)).prod e) (e.prod (a.prod (b.prod c))) :=
    Measure.measurePreserving_swap
  have p4 : MeasurePreserving (Prod.map id Prod.swap) (e.prod (a.prod (b.prod c))) (e.prod ((b.prod c).prod a)) :=
    (MeasurePreserving.id e).prod Measure.measurePreserving_swap
  have p5 : MeasurePreserving (Prod.map id (MeasurableEquiv.prodAssoc (α := β) (β := γ) (γ := α)))
      (e.prod ((b.prod c).prod a)) (e.prod (b.prod (c.prod a))) :=
    (MeasurePreserving.id e).prod (measurePreserving_prodAssoc b c a)
  exact (((p5.comp p4).comp p3).comp p2).comp p1

end Fub4Proof

theorem iterated_integrals_four_factors_holds : Fub4 := by
  intro α β γ δ _ _ _ _ a b c e _ _ _ _
  have hm := measurePreserving_swapFour a b c e
  constructor
  · intro f hf
    let g : δ × β × γ × α → ℂ := fun q => f (q.2.2.2, q.2.1, q.2.2.1, q.1)
    have hfg : g ∘ swapFour α β γ δ = f := rfl
    have hg : Integrable g (e.prod (b.prod (c.prod a))) :=
      (hm.integrable_comp_emb (swapFour α β γ δ).measurableEmbedding).1 (by rwa [hfg])
    calc ∫ p, f p ∂(a.prod (b.prod (c.prod e)))
        = ∫ p, g (swapFour α β γ δ p) ∂(a.prod (b.prod (c.prod e))) := rfl
      _ = ∫ q, g q ∂(e.prod (b.prod (c.prod a))) :=
          hm.integral_comp (swapFour α β γ δ).measurableEmbedding g
      _ = _ := integral_prod_four e b c a g hg
  · intro f hf
    let g : δ × β × γ × α → ℝ≥0∞ := fun q => f (q.2.2.2, q.2.1, q.2.2.1, q.1)
    have hg : Measurable g := hf.comp (swapFour α β γ δ).symm.measurable
    calc ∫⁻ p, f p ∂(a.prod (b.prod (c.prod e)))
        = ∫⁻ p, g (swapFour α β γ δ p) ∂(a.prod (b.prod (c.prod e))) := rfl
      _ = ∫⁻ q, g q ∂(e.prod (b.prod (c.prod a))) := hm.lintegral_comp hg
      _ = _ := lintegral_prod_four e b c a g hg

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iterated_integrals_four_factors : Fub4 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ColumnSplitting.iterated_integrals_four_factors_holds
end

section
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting.Form

theorem continuous_jn_pair {D : D7} {a r t n : ℕ} (hn : r + t = n) :
    Continuous fun z : Mx D a r × Mx D a t => jn hn z.1 z.2 := by
  unfold jn
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.submatrix_apply, id]
  cases (finSumFinEquiv.trans (finCongr hn)).symm j with
  | inl c => simpa using continuous_fst.matrix_elem i c
  | inr c => simpa using continuous_snd.matrix_elem i c

theorem continuous_yv_pair {D : D7} {r t : ℕ} (V : HSp D) (b₀ : HermE D r) :
    Continuous (yv (t := t) V b₀) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  unfold yv ip
  exact continuous_const.matrix_mul ((continuous_adj.comp continuous_fst).matrix_mul
    (continuous_const.matrix_mul continuous_snd))

theorem nuT_form : ZpEq → AcEq → JnPi → Ext0 → Fub4 → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t)
    (hn : W.rank + t = n) (I : IkD d n) θ, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure →
    ∀ (b₀ : HermE D W.rank), b₀.1.det ≠ 0 → ∀ x₀, gramQ W x₀ = b₀.1 → ∀ Φ ∈ schwartzA θ B.rank n,
    ∀ η ∈ schwartzA θ W.rank t, Integrable (core hn I x₀ Φ η) (I.νK.prod (Q0 I μ)) →
    Integrable (fun z => Φ (jn hn z.1 z.2) * conj (η (yv B b₀ z))) (nuT hn I μ x₀) ∧
    ∫ z, Φ (jn hn z.1 z.2) * conj (η (yv B b₀ z)) ∂(nuT hn I μ x₀) =
      ∫ y, orb W I.m (ikp I fun X => Φ (mm X (bl hn 1 y 0 1))) (ext0 hn x₀) * conj (η y) ∂μ := by
  intro hZ hA hJ hE hF D n t B W d hn I θ hθ μ hμ b₀ hb x₀ hx Φ hΦ η hη hint
  obtain ⟨g1, g2⟩ := top_pair (D := D) B.rank W.rank t
  obtain ⟨-, -, p3, -, p5⟩ := top_mx (D := D) B.rank W.rank
  obtain ⟨-, -, p3', -, p5'⟩ := top_mx (D := D) B.rank t
  have hΦc := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ Φ hΦ).1
  have hηc := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ η hη).1
  have hGc : Continuous fun z : Mx D B.rank W.rank × Mx D B.rank t =>
      Φ (jn hn z.1 z.2) * conj (η (yv B b₀ z)) :=
    (hΦc.comp (continuous_jn_pair hn)).mul
      (Complex.continuous_conj.comp (hηc.comp (continuous_yv_pair B b₀)))
  have hπ := measurable_pi hn I x₀
  have hcomp : (fun z : Mx D B.rank W.rank × Mx D B.rank t => Φ (jn hn z.1 z.2) * conj (η (yv B b₀ z))) ∘
      (fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)) = core hn I x₀ Φ η := by
    funext p
    obtain ⟨k, q⟩ := p
    simp only [Function.comp, core]
    rw [hJ D n t B W d hn x₀ _ q, (hA D W.rank t B b₀ _ _).2.1, (hZ D n t B W d hn b₀ hb x₀ hx q).2.1]
  refine ⟨?_, ?_⟩
  · unfold nuT
    rw [integrable_map_measure hGc.aestronglyMeasurable hπ.aemeasurable, hcomp]
    exact hint
  · have e1 : ∫ z, Φ (jn hn z.1 z.2) * conj (η (yv B b₀ z)) ∂(nuT hn I μ x₀) =
        ∫ p, core hn I x₀ Φ η p ∂(I.νK.prod (Q0 I μ)) := by
      unfold nuT
      rw [integral_map hπ.aemeasurable hGc.aestronglyMeasurable, ← hcomp]
      rfl
    rw [e1]
    obtain ⟨-, i2, i3, i4, i5⟩ := top_mx (D := D) t n
    obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) W.rank t
    obtain ⟨-, k2, k3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
    have : BorelSpace (GA D W) := ⟨rfl⟩
    obtain ⟨hc, 𝓕, hf⟩ := I.cov₁
    have := hf.1
    have := I.haar
    have := I.probK
    have e2 := (hF I.l.K (GA D W) (Mx D t n) (Mx D W.rank t) I.νK I.m I.μ₁ μ).1 _ hint
    unfold Q0
    rw [e2]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [core]
    simp_rw [integral_mul_const]
    congr 1
    unfold orb
    refine integral_congr_ae (ae_of_all _ fun h => ?_)
    simp only [hE D n t W hn x₀ h, ikp, ikS, projS, XU]
    refine integral_congr_ae (ae_of_all _ fun u => integral_congr_ae (ae_of_all _ fun k => ?_))
    simp only [mm, Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.ColumnSplitting.Form

end
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_theta_kernel_fibers : ZpEq → AcEq → JnPi → Ext0 → Fub4 → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) θ, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ (b₀ : HermE D W.rank), b₀.1.det ≠ 0 → ∀ x₀, gramQ W x₀ = b₀.1 → ∀ Φ ∈ schwartzA θ B.rank n, ∀ η ∈ schwartzA θ W.rank t, Integrable (core hn I x₀ Φ η) (I.νK.prod (Q0 I μ)) → Integrable (fun z => Φ (jn hn z.1 z.2) * conj (η (yv B b₀ z))) (nuT hn I μ x₀) ∧ ∫ z, Φ (jn hn z.1 z.2) * conj (η (yv B b₀ z)) ∂(nuT hn I μ x₀) = ∫ y, orb W I.m (ikp I fun X => Φ (mm X (bl hn 1 y 0 1))) (ext0 hn x₀) * conj (η y) ∂μ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ColumnSplitting.Form.nuT_form
end

section
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem jn_firstCols {D : D7} {a r t n : ℕ} (hn : r + t = n) (w : Mx D a r) (v : Mx D a t) :
    (jn hn w v).submatrix id (fun j : Fin r => finCongr hn (Fin.castAdd t j)) = w := by
  ext i j
  have e : (finSumFinEquiv.trans (finCongr hn)).symm (finCongr hn (Fin.castAdd t j)) = Sum.inl j := by
    rw [Equiv.symm_apply_eq]
    simp
  simp only [jn, Matrix.submatrix_apply, id, e, Matrix.fromCols_apply_inl]

theorem continuous_jn_pair {D : D7} {a r t n : ℕ} (hn : r + t = n) :
    Continuous fun p : Mx D a r × Mx D a t => jn hn p.1 p.2 := by
  refine continuous_matrix fun i j => ?_
  simp only [jn, Matrix.submatrix_apply, id]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm j with k | k
  · simpa using (continuous_fst.matrix_elem i k)
  · simpa using (continuous_snd.matrix_elem i k)

theorem continuous_orb_shear : IkSch → Dom → OrbFin → Shift → JnBl → Ext0 → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t)
    (hn : W.rank + t = n) (I : IkD d n) θ, IsInfFam θ → ∀ (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E), x₀.det ≠ 0 →
    ∀ Φ ∈ schwartzA θ B.rank n,
      Continuous (fun y : Mx D W.rank t => orb W I.m (ikp I fun X => Φ (mm X (bl hn 1 y 0 1))) (ext0 hn x₀)) := by
  intro hIk hDom hOrb hShift hJn hExt D n t B W d hn I θ hθ x₀ hx Φ hΦ
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨hT, -, hS, -, -⟩ := top_mx (D := D) W.rank t
  obtain ⟨hT', -, -, -, -⟩ := top_mx (D := D) W.rank W.rank
  obtain ⟨-, g2, g3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hBor : BorelSpace (GA D W) := ⟨rfl⟩
  have hΨ : ikp I Φ ∈ schwartzA θ W.rank n := (hIk D n t B W d I θ hθ Φ hΦ).2
  have hcΨ : Continuous (ikp I Φ) := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ _ hΨ).1
  have hinj : Function.Injective fun j : Fin W.rank => finCongr hn (Fin.castAdd t j) := by
    intro a b h
    exact Fin.castAdd_injective _ _ ((finCongr hn).injective h)
  obtain ⟨M, hM, -, hMd⟩ := hDom D θ hθ W.rank n W.rank _ hinj _ hΨ
  have hcM : Continuous M := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ M hM).1
  have hform : ∀ (y : Mx D W.rank t) (h : GA D W),
      (ikp I fun X => Φ (mm X (bl hn 1 y 0 1))) (mm (mt W h⁻¹) (rat (ext0 hn x₀))) =
        ikp I Φ (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0)) := by
    intro y h
    rw [hShift D n t B W d hn I Φ y, hExt D n t W hn x₀ h, hJn D n t W.rank W.rank hn]
  have hfun : (fun y : Mx D W.rank t => orb W I.m (ikp I fun X => Φ (mm X (bl hn 1 y 0 1))) (ext0 hn x₀)) =
      fun y => ∫ h, ikp I Φ (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0)) ∂I.m := by
    funext y
    exact integral_congr_ae (Eventually.of_forall fun h => hform y h)
  rw [hfun]
  have hcw := continuous_ww (D := D) (W := W) x₀
  have hb : Integrable (fun h => M (ww W x₀ h)) I.m :=
    ⟨(hcM.comp hcw).aestronglyMeasurable, hOrb D θ hθ W I.m I.haar x₀ hx M hM⟩
  have hpt : ∀ (h : GA D W), Continuous fun y : Mx D W.rank t => ikp I Φ (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0)) := by
    intro h
    refine hcΨ.comp ((continuous_jn_pair hn).comp (continuous_const.prodMk ?_))
    exact (continuous_const.matrix_mul continuous_id).add continuous_const
  have hmeas : ∀ y : Mx D W.rank t, Continuous fun h : GA D W => ikp I Φ (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0)) := by
    intro y
    refine hcΨ.comp ((continuous_jn_pair hn).comp (hcw.prodMk ?_))
    exact (hcw.matrix_mul continuous_const).add continuous_const
  have hF : FirstCountableTopology (Mx D W.rank t) :=
    @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ hS
  refine continuous_of_dominated (bound := fun h => ‖M (ww W x₀ h)‖)
    (fun y => (hmeas y).aestronglyMeasurable) (fun y => Eventually.of_forall fun h => ?_) hb.norm
    (Eventually.of_forall hpt)
  have h1 := hMd (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0))
  rw [jn_firstCols] at h1
  exact h1.trans (Complex.re_le_norm _)

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_orbital_integral_unipotent : IkSch → Dom → OrbFin → Shift → JnBl → Ext0 → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) θ, IsInfFam θ → ∀ (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E), x₀.det ≠ 0 → ∀ Φ ∈ schwartzA θ B.rank n, Continuous (fun y : Mx D W.rank t => orb W I.m (ikp I fun X => Φ (mm X (bl hn 1 y 0 1))) (ext0 hn x₀)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ColumnSplitting.continuous_orb_shear
end

section
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting.Frame

theorem det_ne_zero_of_gramQ : ∀ (D : D7) (W : HSp D) (b₀ : HermE D W.rank), b₀.1.det ≠ 0 →
    ∀ x₀, gramQ W x₀ = b₀.1 → x₀.det ≠ 0 := by
  intro D W b₀ hb x₀ hx h0
  apply hb
  rw [← hx]
  unfold gramQ
  simp [Matrix.det_mul, h0]

end GlobalTheory.CompanionTheory.ColumnSplitting.Frame
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_ne_zero_of_gram_nondegenerate : ∀ (D : D7) (W : HSp D) (b₀ : HermE D W.rank), b₀.1.det ≠ 0 → ∀ x₀, gramQ W x₀ = b₀.1 → x₀.det ≠ 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ColumnSplitting.Frame.det_ne_zero_of_gramQ
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.CompanionTheory.ColumnSplitting

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem main : IdemEx → LatBound → QK → IkSch → ThetaSideMeasure := by
  intro _ hLat hQK hIk D n t B W d hn I θ hθ μ hμ b₀ hb x₀ hx
  have hdx := GlobalTheory.T.det_ne_zero_of_gram_nondegenerate D W b₀ hb x₀ hx
  have hDom := GlobalTheory.T.fundamental_domain_property
  have hOF := GlobalTheory.T.orbit_finiteness_of_lattice_bound hLat
  have hZ := GlobalTheory.T.zeta_polynomial_identity
  have hA := GlobalTheory.T.abscissa_convergence_identity
  have hJ := GlobalTheory.T.joined_projection_formula
  have hB := GlobalTheory.T.joined_block_formula
  have hE := GlobalTheory.T.extension_by_zero_orbit_formula
  have hS := GlobalTheory.T.unipotent_shift_invariance
  have hL := GlobalTheory.T.induced_section_local_integrability
  have hF := GlobalTheory.T.iterated_integrals_four_factors
  refine ⟨nuT hn I μ x₀, ⟨GlobalTheory.T.finite_on_compacts_orbit_measure D n t B W d hn I μ hμ b₀ hb x₀ hx, GlobalTheory.T.orbit_measure_concentrated_on_quadric hZ hA D n t B W d hn I μ hμ b₀ hb x₀ hx,
    fun h _ => GlobalTheory.T.orbit_measure_unitary_group_invariant hQK GlobalTheory.T.law_of_orbit_measure D n t B W d hn I μ hμ x₀ h,
    fun y _ => GlobalTheory.T.orbit_measure_translation_invariant D n t B W d hn I μ hμ x₀ y,
    fun g _ => GlobalTheory.T.orbit_measure_GL_right_scaling D n t B W d hn I μ hμ x₀ g⟩,
    GlobalTheory.T.orbit_measure_integral_points_nonzero D n t B W d hn I μ hμ x₀, fun Φ hΦ η hη => ?_⟩
  have hc := GlobalTheory.T.integrable_theta_kernel_product hIk hDom hOF hS hL hF hB D n t B W d hn I θ hθ μ hμ x₀ hdx Φ hΦ η hη
  obtain ⟨h1, h2⟩ := GlobalTheory.T.integrable_theta_kernel_fibers hZ hA hJ hE hF D n t B W d hn I θ hθ μ hμ b₀ hb x₀ hx Φ hΦ η hη hc
  exact ⟨h1, GlobalTheory.T.continuous_orbital_integral_unipotent hIk hDom hOF hS hB hE D n t B W d hn I θ hθ x₀ hdx Φ hΦ, h2⟩

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end
