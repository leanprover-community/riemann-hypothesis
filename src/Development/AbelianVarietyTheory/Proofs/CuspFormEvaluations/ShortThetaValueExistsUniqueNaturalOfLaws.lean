import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBC
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FaithfullyFlatPointsBaseChangeDescent
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDVal
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHomStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsVtOverIsUUOverBaseChange
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmonicValueBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InZhGeoInjStableStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsotropicSumIndependentOfChoicesLocal
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ModuliUnivEtaKilled
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsPowMulCoprimeLe
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTranslationSectionsUniversalObject
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatRoots
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatSplitIsotropicGroup

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicSum_independent_of_choices_local : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (P : MvPolynomial (LtN Dw n) c.F) (T : Type) [CommRing T] [IsLocalRing T] [Algebra c.F T] (y : FrPt Xo c T) (z1 : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (tp1 : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (F1 : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (z2 : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (tp2 : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (F2 : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))), (∀ i, InZh Xo Λ N (z1 i)) → GeoInj Xo y.x z1 → (∀ q b, tp1 q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp1 q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z1 i b) (tp1 q b) (F1 q i b)) → (∀ i, InZh Xo Λ N (z2 i)) → GeoInj Xo y.x z2 → (∀ q b, tp2 q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp2 q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z2 i b) (tp2 q b) (F2 q i b)) → ∀ q, ∑ i, ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F1 q i b) (colOf m b) = ∑ i, ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F2 q i b) (colOf m b) := by
  first | exact @GlobalTheory.shortSum_indep_local | exact GlobalTheory.shortSum_indep_local | (intros; apply GlobalTheory.shortSum_indep_local <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShortCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_pull (hC : ChartIndepSt2) [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab)
    {n : ℕ} (Λ : GenLat E n) (N : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)))
    {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) (w : FrPt Xo c T) (hm : FrMap ψ y w)
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G))
    (tp : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G))
    (F : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x)))
    (hz : ∀ i, InZh Xo Λ N (z i)) (hg : GeoInj Xo y.x z)
    (ht : ∀ q b, tp q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp q b))
    (hF : ∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z i b) (tp q b) (F q i b)) :
    ∃ (z' : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo w.x ⟶ Xo.univ.t.G))
      (tp' : (Fin n → LevQ Dw l) → Fin n → (ptO Xo w.x ⟶ Xo.univ.t.G))
      (F' : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
        LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo w.x))),
      (∀ i, InZh Xo Λ N (z' i)) ∧ GeoInj Xo w.x z' ∧
      (∀ q b, tp' q b ^ N = levPt Xo w.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp' q b)) ∧
      (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N w.s (z' i b) (tp' q b) (F' q i b)) ∧
      ∀ q, ψ (∑ i, ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
          ∏ b, nab y ((N : ℤ) ^ 2) (F q i b) (colOf m b)) =
        ∑ i, ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) *
          ∏ b, nab w ((N : ℤ) ^ 2) (F' q i b) (colOf m b) := by
  have hx : w.x = spMap ψ.toRingHom ≫ y.x := by
    unfold FrMap at hm
    exact hm.1
  let h : ptO Xo w.x ⟶ ptO Xo y.x := Over.homMk (spMap ψ.toRingHom) hx.symm
  have hh : h.left = spMap ψ.toRingHom := rfl
  have hs := GlobalTheory.FramedBaseChange.isPullSec ψ hm h hh
  have hpull : ∀ q i b, IsPullSec Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (h ▷ Xo.univ.t.G)
      (whiskerRight_snd _ _) (F q i b) (GlobalTheory.VVRank.pullS Xo.univ.t.G ((N : ℤ) ^ 2) h (F q i b)) :=
    fun q i b => GlobalTheory.VVRank.isPullSec_pullS _ _ h _
  obtain ⟨hZ, -, hG, -⟩ := GlobalTheory.T.inZh_geoInj_stable_alt E H Dw l Xo n Λ N
  refine ⟨fun i b => h ≫ z i b, fun q b => h ≫ tp q b,
    fun q i b => GlobalTheory.VVRank.pullS Xo.univ.t.G ((N : ℤ) ^ 2) h (F q i b),
    fun i => hZ _ _ h _ (hz i), hG S T y.x w.x ψ.toRingHom h hh _ z hg, fun q b => ⟨?_, ?_⟩,
    fun q i b => (GlobalTheory.VtBaseChange.isVtOver_isUUOver_baseChange E H Dw l Xo N ⊥ _ _ h y.s w.s hs
      (F q i b) _ (hpull q i b)).2 (z i b) (tp q b) (hF q i b), fun q => ?_⟩
  · dsimp only
    rw [← MonObj.comp_pow, (ht q b).1]
    unfold levPt
    rw [← Category.assoc, toUnit_unique (h ≫ toUnit _) (toUnit _)]
  · obtain ⟨j, hj⟩ := (ht q b).2
    refine ⟨j, ?_⟩
    unfold KilledBy at hj ⊢
    intro x hx
    rw [Category.assoc, hj x hx, MonObj.comp_one]
  · rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact GlobalTheory.T.harmonicValue_baseChange_alt hC E H Dw l Xo c nab hnab S T ψ y w hm h hh a n P hP N (F q i)
      (fun b => GlobalTheory.VVRank.pullS Xo.univ.t.G ((N : ℤ) ^ 2) h (F q i b)) (hpull q i)

theorem eq_of_local {K T : Type} [Field K] [CommRing T] [Algebra K T] (u v : T)
    (h : ∀ (U : Type) [CommRing U] [IsLocalRing U] [Algebra K U] (κ : T →ₐ[K] U), κ u = κ v) : u = v := by
  rw [← sub_eq_zero]
  refine eq_zero_of_localization (u - v) fun J hJ => ?_
  have := hJ.isPrime
  have e := h (Localization.AtPrime J) (IsScalarTower.toAlgHom K T (Localization.AtPrime J))
  simpa [map_sub, sub_eq_zero] using e

theorem shortSum_eq_of_witnesses : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (S1 : Type) [CommRing S1] [Algebra c.F S1] (φ1 : S →ₐ[c.F] S1) (y1 : FrPt Xo c S1) (z1 : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y1.x ⟶ Xo.univ.t.G)) (tp1 : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y1.x ⟶ Xo.univ.t.G)) (F1 : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y1.x))) (S2 : Type) [CommRing S2] [Algebra c.F S2] (φ2 : S →ₐ[c.F] S2) (y2 : FrPt Xo c S2) (z2 : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y2.x ⟶ Xo.univ.t.G)) (tp2 : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y2.x ⟶ Xo.univ.t.G)) (F2 : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y2.x))), FrMap φ1 y y1 → FrMap φ2 y y2 → (∀ i, InZh Xo Λ N (z1 i)) → GeoInj Xo y1.x z1 → (∀ q b, tp1 q b ^ N = levPt Xo y1.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp1 q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y1.s (z1 i b) (tp1 q b) (F1 q i b)) → (∀ i, InZh Xo Λ N (z2 i)) → GeoInj Xo y2.x z2 → (∀ q b, tp2 q b ^ N = levPt Xo y2.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp2 q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y2.s (z2 i b) (tp2 q b) (F2 q i b)) → ∀ (T : Type) [CommRing T] [Algebra c.F T] (ψ1 : S1 →ₐ[c.F] T) (ψ2 : S2 →ₐ[c.F] T), ψ1.comp φ1 = ψ2.comp φ2 → ∀ q, ψ1 (∑ i, ∑ m ∈ P.support, algebraMap c.F S1 (P.coeff m) * ∏ b, nab y1 ((N : ℤ) ^ 2) (F1 q i b) (colOf m b)) = ψ2 (∑ i, ∑ m ∈ P.support, algebraMap c.F S2 (P.coeff m) * ∏ b, nab y2 ((N : ℤ) ^ 2) (F2 q i b) (colOf m b)) := by
  intro hL hC E _ _ _ H Dw l Xo c _ nab hnab n Λ N hUn hTr hLev a P hP S _ _ y S1 _ _ φ1 y1 z1 tp1 F1
    S2 _ _ φ2 y2 z2 tp2 F2 hm1 hm2 hz1 hg1 ht1 hF1 hz2 hg2 ht2 hF2 T _ _ ψ1 ψ2 hψ q
  refine eq_of_local (K := c.F) _ _ fun U _ _ _ κ => ?_
  obtain ⟨yU, hyU⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algHom hL E H Dw l Xo c S U ((κ.comp ψ1).comp φ1) y
  have e : (κ.comp ψ1).comp φ1 = (κ.comp ψ2).comp φ2 := by
    rw [AlgHom.comp_assoc, AlgHom.comp_assoc, hψ]
  have hU1 : FrMap (κ.comp ψ1) y1 yU := GlobalTheory.FramedBaseChange.cancel φ1 (κ.comp ψ1) hm1 hyU
  have hU2 : FrMap (κ.comp ψ2) y2 yU := GlobalTheory.FramedBaseChange.cancel φ2 (κ.comp ψ2) hm2 (e ▸ hyU)
  obtain ⟨z1', tp1', F1', hz1', hg1', ht1', hF1', hs1⟩ :=
    exists_pull hC nab hnab Λ N a P hP (κ.comp ψ1) y1 yU hU1 z1 tp1 F1 hz1 hg1 ht1 hF1
  obtain ⟨z2', tp2', F2', hz2', hg2', ht2', hF2', hs2⟩ :=
    exists_pull hC nab hnab Λ N a P hP (κ.comp ψ2) y2 yU hU2 z2 tp2 F2 hz2 hg2 ht2 hF2
  have key := GlobalTheory.T.isotropicSum_independent_of_choices_local hL E H Dw l Xo c nab hnab n Λ N hUn hTr hLev P U yU z1' tp1' F1' z2' tp2' F2'
    hz1' hg1' ht1' hF1' hz2' hg2' ht2' hF2' q
  have h1 := hs1 q
  have h2 := hs2 q
  simp only [AlgHom.comp_apply] at h1 h2
  rw [h1, h2]
  exact key

end GlobalTheory.ShortCompare
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortThetaSum_eq_of_witnesses_common_algebra : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (S1 : Type) [CommRing S1] [Algebra c.F S1] (φ1 : S →ₐ[c.F] S1) (y1 : FrPt Xo c S1) (z1 : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y1.x ⟶ Xo.univ.t.G)) (tp1 : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y1.x ⟶ Xo.univ.t.G)) (F1 : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y1.x))) (S2 : Type) [CommRing S2] [Algebra c.F S2] (φ2 : S →ₐ[c.F] S2) (y2 : FrPt Xo c S2) (z2 : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y2.x ⟶ Xo.univ.t.G)) (tp2 : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y2.x ⟶ Xo.univ.t.G)) (F2 : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y2.x))), FrMap φ1 y y1 → FrMap φ2 y y2 → (∀ i, InZh Xo Λ N (z1 i)) → GeoInj Xo y1.x z1 → (∀ q b, tp1 q b ^ N = levPt Xo y1.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp1 q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y1.s (z1 i b) (tp1 q b) (F1 q i b)) → (∀ i, InZh Xo Λ N (z2 i)) → GeoInj Xo y2.x z2 → (∀ q b, tp2 q b ^ N = levPt Xo y2.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp2 q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y2.s (z2 i b) (tp2 q b) (F2 q i b)) → ∀ (T : Type) [CommRing T] [Algebra c.F T] (ψ1 : S1 →ₐ[c.F] T) (ψ2 : S2 →ₐ[c.F] T), ψ1.comp φ1 = ψ2.comp φ2 → ∀ q, ψ1 (∑ i, ∑ m ∈ P.support, algebraMap c.F S1 (P.coeff m) * ∏ b, nab y1 ((N : ℤ) ^ 2) (F1 q i b) (colOf m b)) = ψ2 (∑ i, ∑ m ∈ P.support, algebraMap c.F S2 (P.coeff m) * ∏ b, nab y2 ((N : ℤ) ^ 2) (F2 q i b) (colOf m b)) := by
  first | exact @GlobalTheory.ShortCompare.shortSum_eq_of_witnesses | exact GlobalTheory.ShortCompare.shortSum_eq_of_witnesses | (intros; apply GlobalTheory.ShortCompare.shortSum_eq_of_witnesses <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_faithfullyFlat_split_isotropicGroup : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x0 : Sp S ⟶ Xo.X) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G)), φ.FaithfullyFlat ∧ (∀ i, InZh Xo Λ N (z i)) ∧ GeoInj Xo (spMap φ ≫ x0) z := by
  first | exact @GlobalTheory.exists_faithfullyFlat_split_Zh | exact GlobalTheory.exists_faithfullyFlat_split_Zh | (intros; apply GlobalTheory.exists_faithfullyFlat_split_Zh <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem finite_levQ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (l : Level H) :
    Finite (LevQ Dw l) := by
  have hne : l.Mb ≠ ⊥ := by
    intro h
    have h2 := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h2
    have h3 : (l.M : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.mpr (by have := l.three_le; omega)
    exact h3 h2
  have : Finite (𝓞 E ⧸ l.Mb) := Ideal.finiteQuotientOfFreeOfNeBot l.Mb hne
  have : Module.Finite (𝓞 E) Dw.La := Dw.fin
  have : Module.Finite (𝓞 E ⧸ l.Mb) (LevQ Dw l) :=
    Module.Finite.of_restrictScalars_finite (𝓞 E) (𝓞 E ⧸ l.Mb) (LevQ Dw l)
  exact Module.finite_of_finite (𝓞 E ⧸ l.Mb)

theorem exists_cover_shortVal_data :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), ∃ (S' : Type) (_ : CommRing S') (_ : Algebra c.F S') (φ : S →ₐ[c.F] S') (y' : FrPt Xo c S') (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y'.x ⟶ Xo.univ.t.G)) (tp : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y'.x ⟶ Xo.univ.t.G)) (F : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y'.x))), φ.toRingHom.FaithfullyFlat ∧ FrMap φ y y' ∧ (∀ i, InZh Xo Λ N (z i)) ∧ GeoInj Xo y'.x z ∧ (∀ q b, tp q b ^ N = levPt Xo y'.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp q b)) ∧ (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y'.s (z i b) (tp q b) (F q i b)) := by
  intro hL E _ _ _ H Dw l Xo c n Λ N hU hT hN S _ _ y
  have hN0 : 0 < N := hN.1.pos
  have hle : Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La := le_trans hN.2.2 inf_le_left
  have hlev : ∀ {R R' : Type} [CommRing R] [CommRing R'] (x : Sp R ⟶ Xo.X) (x' : Sp R' ⟶ Xo.X)
      (h : ptO Xo x' ⟶ ptO Xo x) (a : Dw.La), h ≫ levPt Xo x a = levPt Xo x' a := by
    intro R R' _ _ x x' h a
    rw [levPt, levPt, ← Category.assoc, comp_toUnit]
  have hkill : ∀ {R : Type} [CommRing R] (x : Sp R ⟶ Xo.X) (a : Dw.La), KilledBy Xo l.Mb (levPt Xo x a) := by
    intro R _ x a b hb
    rw [levPt, Category.assoc, (moduli_univ_eta_killed hL E H Dw l Xo a).1 b hb, MonObj.comp_one]
  have hpowM : ∀ {R : Type} [CommRing R] (x : Sp R ⟶ Xo.X) (a : Dw.La), levPt Xo x a ^ l.M = 1 := by
    intro R _ x a
    rw [levPt, ← MonObj.comp_pow, (moduli_univ_eta_killed hL E H Dw l Xo a).2.2, MonObj.comp_one]
  have hpowN : ∀ {R : Type} [CommRing R] (x : Sp R ⟶ Xo.X) (a : Dw.La), levPt Xo x a ^ N = 1 := by
    intro R _ x a
    obtain ⟨k, hk⟩ := hN.2.1
    rw [hk, pow_mul, hpowM, one_pow]
  have : Finite (LevQ Dw l) := finite_levQ Dw l
  let _ : Fintype ((Fin n → LevQ Dw l) × Fin n) := Fintype.ofFinite _
  obtain ⟨B1, _, φ1, w, hφ1, hw⟩ := GlobalTheory.T.exists_faithfullyFlat_nthRoots_of_torsion hL E H Dw l Xo S y.x N l.M hN0
    (by have := l.three_le; omega) ((Fin n → LevQ Dw l) × Fin n)
    (fun j => levPt Xo y.x (levRep (j.1 j.2))) (fun j => hpowM _ _)
  have hw' : ∀ j, w j ^ N = levPt Xo (spMap φ1 ≫ y.x) (levRep (j.1 j.2)) := by
    intro j
    apply Over.OverMorphism.ext
    rw [hw j, ← hlev y.x (spMap φ1 ≫ y.x) (Over.homMk (spMap φ1) rfl), Over.comp_left]
    rfl
  have hroot := fun j => (exists_root_killedBy_pow E H Dw l Xo (ptO Xo (spMap φ1 ≫ y.x))
    (levPt Xo (spMap φ1 ≫ y.x) (levRep (j.1 j.2))) (w j) N hN0 (hkill _ _) (hw' j)).1
  choose tp1 htp1 htp1k using hroot
  obtain ⟨B2, _, φ2, z, hφ2, hz, hzg⟩ := GlobalTheory.T.exists_faithfullyFlat_split_isotropicGroup hL E H Dw l Xo B1 (spMap φ1 ≫ y.x) n Λ N hU hN0 hle
  let _ : Algebra c.F B2 := ((φ2.comp φ1).comp (algebraMap c.F S)).toAlgebra
  let φA : S →ₐ[c.F] B2 := { toRingHom := φ2.comp φ1, commutes' := fun _ => rfl }
  obtain ⟨y', hy'⟩ := FramedBaseChange.exists_frMap hL E H Dw l Xo c S B2 φA y
  have hyx : y'.x = spMap φ2 ≫ spMap φ1 ≫ y.x := by
    rw [hy'.1, ← Category.assoc, FramedBaseChange.spMap_spMap]
  let hA : ptO Xo y'.x ⟶ ptO Xo (spMap φ1 ≫ y.x) := Over.homMk (spMap φ2) hyx.symm
  let hB : ptO Xo y'.x ⟶ ptO Xo (spMap φ2 ≫ spMap φ1 ≫ y.x) :=
    Over.homMk (𝟙 _) (by rw [Category.id_comp]; exact hyx.symm)
  have hI := GlobalTheory.T.inZh_geoInj_stable_alt E H Dw l Xo n Λ N
  have hz' : ∀ i, InZh Xo Λ N (fun b => hB ≫ z i b) := fun i => hI.1 _ _ hB (z i) (hz i)
  have htpN : ∀ q b, (hA ≫ tp1 (q, b)) ^ N = levPt Xo y'.x (levRep (q b)) := by
    intro q b
    rw [← MonObj.comp_pow, htp1, hlev]
  have hUU := (exists_isVtOver_and_existsUnique_isUUOver hL E H Dw l Xo N hN.1 (ptO Xo y'.x) y'.s).2
  have hF : ∀ (q : Fin n → LevQ Dw l) (i : Fin (Λ.zCard N (Dw.p + Dw.q))) (b : Fin n), ∃ F,
      IsUUOver Xo.univ.t.G Xo.univ.t.PP N y'.s (hB ≫ z i b) (hA ≫ tp1 (q, b)) F := by
    intro q i b
    refine (hUU _ _ ((hz' i).1 b) ?_).exists
    rw [pow_two, pow_mul, htpN, hpowN]
  choose F hF using hF
  refine ⟨B2, inferInstance, inferInstance, φA, y', fun i b => hB ≫ z i b, fun q b => hA ≫ tp1 (q, b), F,
    RingHom.FaithfullyFlat.stableUnderComposition φ1 φ2 hφ1 hφ2, hy', hz', ?_, ?_, hF⟩
  · exact hI.2.2.1 B2 B2 _ y'.x (RingHom.id B2) hB
      (Spec.map_id (CommRingCat.of B2)).symm _ z hzg
  · intro q b
    obtain ⟨j, hj⟩ := htp1k (q, b)
    exact ⟨htpN q b, j, fun a ha => by rw [Category.assoc, hj a ha, MonObj.comp_one]⟩

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_faithfullyFlat_cover_shortThetaValue_data : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), ∃ (S' : Type) (_ : CommRing S') (_ : Algebra c.F S') (φ : S →ₐ[c.F] S') (y' : FrPt Xo c S') (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y'.x ⟶ Xo.univ.t.G)) (tp : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y'.x ⟶ Xo.univ.t.G)) (F : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y'.x))), φ.toRingHom.FaithfullyFlat ∧ FrMap φ y y' ∧ (∀ i, InZh Xo Λ N (z i)) ∧ GeoInj Xo y'.x z ∧ (∀ q b, tp q b ^ N = levPt Xo y'.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp q b)) ∧ (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y'.s (z i b) (tp q b) (F q i b)) := by
  atlas_forward_decl GlobalTheory.exists_cover_shortVal_data
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShortValue

theorem finite_levelQuotient {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H)
    (l : Geo.Tor.Level H) : Finite (LevQ Dw l) := by
  have hne : l.Mb ≠ ⊥ := by
    intro h
    have hp := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] at hp
    have := l.three_le
    omega
  haveI : Finite (𝓞 E ⧸ l.Mb) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  haveI := Dw.fin
  exact Submodule.finite_quotient_smul l.Mb (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem map_weighted_finsum {F S₁ S₂ T Q : Type} [Field F] [CommRing S₁] [CommRing S₂] [CommRing T]
    [Algebra F S₁] [Algebra F S₂] [Algebra F T] [Finite Q] (ψ₁ : S₁ →ₐ[F] T) (ψ₂ : S₂ →ₐ[F] T)
    (k : F) (w : Q → F) (A₁ : Q → S₁) (A₂ : Q → S₂) (h : ∀ q, ψ₁ (A₁ q) = ψ₂ (A₂ q)) :
    ψ₁ (algebraMap F S₁ k * ∑ᶠ q, algebraMap F S₁ (w q) * A₁ q) =
      ψ₂ (algebraMap F S₂ k * ∑ᶠ q, algebraMap F S₂ (w q) * A₂ q) := by
  haveI := Fintype.ofFinite Q
  simp only [finsum_eq_sum_of_fintype, map_mul, map_sum, AlgHom.commutes, h]

end GlobalTheory.ShortValue

namespace GlobalTheory

theorem shortThetaValue_existsUnique_natural : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (w : (Fin n → LevQ Dw l) → c.F) (β : c.F), (∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), ∃! v, ShortValAt Xo c nab w Λ β N P y v) ∧ ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y0 : FrPt Xo c S) (y : FrPt Xo c T), FrMap φ y0 y → ∀ v0 v, ShortValAt Xo c nab w Λ β N P y0 v0 → ShortValAt Xo c nab w Λ β N P y v → φ v0 = v := by
  intro hL hC E _ _ _ H Dw l Xo c _ nab hnab n Λ N hU hT hN a P hP w β
  haveI := ShortValue.finite_levelQuotient Dw l
  have cmp := GlobalTheory.T.shortThetaSum_eq_of_witnesses_common_algebra hL hC E H Dw l Xo c nab hnab n Λ N hU hT hN a P hP
  have nat : ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
      (y0 : FrPt Xo c S) (y : FrPt Xo c T), FrMap φ y0 y → ∀ v0 v, ShortValAt Xo c nab w Λ β N P y0 v0 →
      ShortValAt Xo c nab w Λ β N P y v → φ v0 = v := by
    intro S T _ _ _ _ φ y0 y hφ v0 v h0 h1
    obtain ⟨S1, _, _, φ1, y1, z1, tp1, F1, hf1, hm1, hz1, hg1, ht1, hu1, e1⟩ := h0
    obtain ⟨S2, _, _, φ2, y2, z2, tp2, F2, hf2, hm2, hz2, hg2, ht2, hu2, e2⟩ := h1
    obtain ⟨U, _, _, ψ2, ψ1, hc, -, hinj⟩ :=
      exists_faithfullyFlat_pushout c.F S S2 S1 (φ2.comp φ) φ1 hf1
    have key := cmp S y0 S1 φ1 y1 z1 tp1 F1 S2 (φ2.comp φ) y2 z2 tp2 F2 hm1
      (FramedBaseChange.trans φ φ2 hφ hm2) hz1 hg1 ht1 hu1 hz2 hg2 ht2 hu2 U ψ1 ψ2 hc.symm
    have hinj2 : Function.Injective φ2 := hf2.injective
    apply hinj2
    apply hinj
    have e0 : ψ2 (φ2 (φ v0)) = ψ1 (φ1 v0) := AlgHom.congr_fun hc v0
    rw [e0, e1, e2]
    exact ShortValue.map_weighted_finsum ψ1 ψ2 _ w _ _ key
  refine ⟨fun S _ _ y => ?_, nat⟩
  obtain ⟨S1, _, _, φ1, y1, z1, tp1, F1, hf1, hm1, hz1, hg1, ht1, hu1⟩ :=
    GlobalTheory.T.exists_faithfullyFlat_cover_shortThetaValue_data hL E H Dw l Xo c n Λ N hU hT hN S y
  obtain ⟨v, hv, -⟩ := existsUnique_preimage_of_faithfullyFlat c.F S S1 φ1 hf1
    (algebraMap c.F S1 (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ *
        ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ *
        ((N : c.F) ^ P.totalDegree)⁻¹) *
      ∑ᶠ q : Fin n → LevQ Dw l, algebraMap c.F S1 (w q) *
        ∑ i, ∑ m ∈ P.support, algebraMap c.F S1 (P.coeff m) *
          ∏ b, nab y1 ((N : ℤ) ^ 2) (F1 q i b) (colOf m b))
    (fun T _ _ ψ1 ψ2 hc => ShortValue.map_weighted_finsum ψ1 ψ2 _ w _ _
      (cmp S y S1 φ1 y1 z1 tp1 F1 S1 φ1 y1 z1 tp1 F1 hm1 hm1 hz1 hg1 ht1 hu1 hz1 hg1 ht1 hu1 T ψ1 ψ2 hc))
  have hv' : ShortValAt Xo c nab w Λ β N P y v :=
    ⟨S1, _, _, φ1, y1, z1, tp1, F1, hf1, hm1, hz1, hg1, ht1, hu1, hv⟩
  exact ⟨v, hv', fun v' h' => nat S S (AlgHom.id c.F S) y y (FramedBaseChange.refl y) v' v h' hv'⟩

end GlobalTheory
end
