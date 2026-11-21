import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFiCComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderTBijective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGLocIdGChiTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryOfIsON
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionModPrimeLevelPrimeSmulEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CevInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBasisAtOfIsLocBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEmbFIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondOperatorsOnCharts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedLevelChainHost
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedLevelChain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelTwistPrimesStepZeroCharacterEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsTopRowSym
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedTopLevelChain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvSmulMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InclMulInvMul
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.SplitIntPI
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.SelfDualPI
import Formalism.LocalToGlobal.GroupLattices.TrivialTransfer.OneAddPowOfSq
import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemStabGLAdeleIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianStepLevelOfChartFormsLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianClassConditionOfChartClasses
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianDataAtLevelPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianColumnsGeneratorsBaseLatticesFunctional
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.ChiMemSubfield
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassPairMovedOfMultipliesLocalFunctional

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.FormSym

theorem hform_last {E : Type} [CommRing E] (σ : E →+* E) {N : ℕ} (hN : 0 < N) {J : Matrix (Fin N) (Fin N) E} (hJ : J = 1) {p : E}
    {z : Fin N → E} (hz : ∀ j, z j = if j.1 + 1 = N then p else 0) (x : Fin N → E) :
    hform σ J z x = σ p * x ⟨N - 1, by omega⟩ := by
  obtain rfl : z = fun j => if j.1 + 1 = N then p else 0 := funext hz
  subst hJ
  unfold hform
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single ⟨N - 1, by omega⟩]
  · simp [show N - 1 + 1 = N by omega]
  · intro b _ hb
    have : ¬ (b.1 + 1 = N) := fun h => hb (Fin.ext (by simp; omega))
    simp [this]
  · simp

theorem sigD_conj (D : D7) (x : D.host.E) : (sigD D : D.host.E →+* D.host.E) x = D.host.conj x := by
  first | rfl | exact Formalism.BasicNotions.Examples₂.star_eq_conj _ _

set_option maxHeartbeats 4000000 in

theorem formsTiedSym_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∃ (Ch : B.Word → ℕ → Type) (chOf : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch u) (chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) ∧ (∀ u i, Finite (Ch u i)) ∧ (∀ u, Nonempty (Unique (Ch u B.R.m))) ∧ (∀ u u', (F u).gl = (F u').gl) ∧ CharacterCompatible (F B.u₀).gl B.R.m := by
  intro B X I hOk hPins l Z
  obtain ⟨G, hG, hChi⟩ := GlobalTheory.Mem.TypePrimes.exists_gLoc_idG_chiTied I hOk hPins l Z
  obtain ⟨-, -, -, hN⟩ := GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z

  have hch : ∀ (u : B.Word) (i : ℕ), ∃ (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u I.mu0 i).Cl → Ch)
      (K : ∀ (hi : i ≤ B.R.m) (β : Ch), LevelChart (I.rec7 l Z) (B.T u) (badG (I.rec7 l Z)) i hi
        (fun c : {c // chOf c = β} => (I.chain l u I.mu0).stab i c.1)
        (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c.1))),
      (∀ hi, I.ReadsK l Z u I.mu0 i hi chOf (K hi)) ∧ (∀ hi c, ((K hi (chOf c)).y ⟨c, rfl⟩).1 = I.yStd u i c) ∧
      ((i = 0 ∨ i = B.R.m) → Nonempty (Unique Ch)) ∧ ∀ hi β, FunKilled (K hi β).lev (X.piT u) := by
    intro u i
    by_cases hi : i ≤ B.R.m
    · obtain ⟨Ch, hF, chOf, K, h1, h2, h3⟩ := GlobalTheory.Mem.Col2.MemChart.exists_charts I hOk hPins l Z u i hi
      obtain ⟨K', h4, h5⟩ := GlobalTheory.Mem.Col2.TC.charts_funKilled I hOk hPins l Z u I.mu0 i hi _ Ch chOf K h1
      refine ⟨Ch, hF, chOf, fun _ => K', fun _ => h4, fun _ c => ?_, h3, fun _ β => (h5 β).1⟩
      rw [(h5 (chOf c)).2.2.2.2.2.1]
      exact h2 c
    · refine ⟨Unit, inferInstance, fun _ => (), fun h => absurd h hi, fun h => absurd h hi, fun h => absurd h hi, fun h => ?_, fun h => absurd h hi⟩
      exfalso
      rcases h with h | h <;> omega
  choose Ch hChF chOf K hRK hYs hU hFK using hch
  have hYs' : ∀ u i hi β c (e : chOf u i c = β), ((K u i hi β).y ⟨c, e⟩).1 = I.yStd u i c := by
    intro u i hi β c e
    subst e
    exact hYs u i hi c
  let A : ∀ u, AtTTied (D := I.rec7 l Z) u := fun u => GlobalTheory.Mem.AtLevel.atTTied I l Z u
  have hIdV : ∀ u, I.IdV l u I.mu0 (A u).eV := fun _ _ => rfl
  choose eY hIdY hde using fun u i (hi : i ≤ B.R.m) => ((hN i hi).2.2 u I.mu0).2
  choose Lv hLv using fun u i (hi : i ≤ B.R.m) => GlobalTheory.Mem.Col2.TC.exists_level_projections I hOk hPins l Z u I.mu0 i hi
  have hde1 : ∀ u i (hi : i ≤ B.R.m), ∃ C : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E,
      cT (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) C.1 * C.1 = gramN (I.rec7 l Z) i hi ∧
      (∀ x : Fin ((I.rec7 l Z).R.N i) → (I.rec7 l Z).host.E, x ∈ selfDualLatticeCoords (I.rec7 l Z) i hi ↔
        ∀ a, (C.1 *ᵥ x) a ∈ (algebraMap (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E).range) ∧
      ∀ τ z, ((I.rec7 l Z).mem u).C.de i z τ = embT (I.rec7 l Z) τ C.1.det * ((eY u i hi z).1 τ).det := by
    intro u i hi
    refine ⟨1, ?_, fun x => ?_, fun τ z => ?_⟩
    · rw [(hN i hi).1]
      simp [cT]
    · rw [Units.val_one]
      simp only [Matrix.one_mulVec]
      exact (hN i hi).2.1 x
    · refine (hde u i hi τ z).trans ?_
      rw [Units.val_one, Matrix.det_one, map_one, one_mul]
  have hVG := fun u i (hi : i ≤ B.R.m) => GlobalTheory.Mem.Col2.TC.val_tied I hOk hPins l Z u I.mu0 i hi _ (Ch u i) (chOf u i) (K u i hi)
    (eY u i hi) (hRK u i hi) (hIdY u i hi)
  have hIN := fun u i (hi : i ≤ B.R.m) => GlobalTheory.Mem.Col2.MetricTie.ipV_norm_tie I hOk hPins l Z u I.mu0 i hi (eY u i hi) (hIdY u i hi)
  have hNm : ∀ u i hi, NormTieG (D := I.rec7 l Z) ((I.rec7 l Z).fm u) (eY u i hi) := fun u i hi => (hIN u i hi).2
  have hDil := fun u i (hi : i ≤ B.R.m) => GlobalTheory.Mem.Col2.DiaChart.dilTied I hOk hPins l Z u I.mu0 i hi _ (Ch u i) (chOf u i) (K u i hi)
    (eY u i hi) (A u).eV (hRK u i hi) (hFK u i hi) (hIdY u i hi) (hIdV u)
  choose fMe hFv hFvT using fun u i (hi : i ≤ B.R.m) => GlobalTheory.Mem.Col2.LevFun.fvTieG I hOk hPins l Z u I.mu0 i hi _ (Ch u i) (chOf u i)
    (K u i hi) (A u).eV (Lv u i hi) (hRK u i hi) (hIdV u) (hLv u i hi) (hFK u i hi)
  have hUp := fun u i (hi : i ≤ B.R.m) => GlobalTheory.Mem.Col2.UpChart.upNatTie I hOk hPins l Z u I.mu0 i hi _ (Ch u i) (chOf u i) (K u i hi)
    (eY u i hi) (A u).eV (Lv u i hi) (hRK u i hi) (hIdY u i hi) (hIdV u) (hLv u i hi)
  have hDn := fun u i (hi : i ≤ B.R.m) => GlobalTheory.DnMove.dnNatTieG_cols I hOk hPins l Z u I.mu0 i hi _ (Ch u i) (chOf u i) (K u i hi)
    (eY u i hi) (A u).eV (Lv u i hi) (hRK u i hi) (hIdY u i hi) (hIdV u) (hLv u i hi)
  have hBw := fun u i (hi : i ≤ B.R.m) => GlobalTheory.Mem.Col2.TC.bw_tie I hOk hPins l Z u I.mu0 i hi (eY u i hi) (hIdY u i hi)

  have hHex : ∀ u i (β : Ch u i), ∃ (H : ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)),
      ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → Subgroup (GL (Fin (B.R.N i)) (kv (I.rec7 l Z).host.F v)))
      (lam : ∀ j v h, H j v h →* ℂˣ), ∀ hi : i ≤ B.R.m, Nonempty (GLevH (K u i hi β).lev G H lam) := by
    intro u i β
    by_cases hi : i ≤ B.R.m
    · obtain ⟨H, lam, h⟩ := GlobalTheory.Mem.Col2.ChartLevel.chart_gLevH I hOk hPins l Z u G i hi (Ch u i) (chOf u i) (K u i hi) hG (hRK u i hi) β
      exact ⟨H, lam, fun _ => h⟩
    · exact ⟨fun _ _ _ => ⊤, fun _ _ _ => 1, fun h => absurd h hi⟩
  choose Hc lamC hGH using hHex

  choose J lamJ VJ Yb hYbF hYbA yb hJ using fun u => GlobalTheory.Mem.Col2.OneLevel.stepBefore_oneLevel I hOk hPins l Z u G (Ch u (B.R.m - 1))
    (chOf u (B.R.m - 1)) (K u (B.R.m - 1) (Nat.sub_le _ _)) hG (hRK u _ _)

  choose KP WP hKP using fun u => GlobalTheory.Mem.Col2.TC.clsP_tie I hOk hPins l Z u

  choose jM hjM using fun u => GlobalTheory.Mem.Col2.PerConj.period_conj I hOk hPins l Z u I.mu0

  let β0 : ∀ u i, (i = 0 ∨ i = B.R.m) → Ch u i := fun u i h => (hU u i h).some.default
  have hβ0 : ∀ u i h c, chOf u i c = β0 u i h := fun u i h c => (hU u i h).some.uniq _
  have hSub : ∀ u i, (i = 0 ∨ i = B.R.m) → Subsingleton (Ch u i) := fun u i h => @Unique.instSubsingleton _ (hU u i h).some
  let clsF : ∀ u i hi (h : i = 0 ∨ i = B.R.m), ClsTied (D := I.rec7 l Z) u i hi := fun u i hi h =>
    clsOfChart (β0 u i h) (hβ0 u i h) (K u i hi (β0 u i h))
  let valF : ∀ u i hi (h : i = 0 ∨ i = B.R.m), ValTied (D := I.rec7 l Z) u (A u).eV i hi (clsF u i hi h) := fun u i hi h =>
    @valOfG _ u i hi (Ch u i) (chOf u i) (hSub u i h) (A u).eV (K u i hi) (β0 u i h) (hβ0 u i h) (eY u i hi) (hde1 u i hi)
      (hVG u i hi) (hIN u i hi).1 (hDil u i hi)
  have hR : ∀ u i hi (h : i = 0 ∨ i = B.R.m), ∃ k, I.Reads u I.mu0 i (fun _ => ()) (fun _ => (clsF u i hi h).lev.Lb)
      (fun _ => (clsF u i hi h).lev.U) (fun _ => (clsF u i hi h).lev.chi) (fun c => ((clsF u i hi h).y c).1)
      (fun c s => ((clsF u i hi h).stabI c s).1) k :=
    fun u i hi h => readsK_one I l Z (hRK u i hi) (β0 u i h) (hβ0 u i h)
  choose V0 hV0 using fun u => GlobalTheory.Mem.Col2.TC.GLev0.glev_zero I hOk hPins l Z u G (clsF u 0 (Nat.zero_le _) (Or.inl rfl)) hG
    (hR u 0 _ (Or.inl rfl))
  choose lamM lamP VM VP hVM using fun u => GlobalTheory.Mem.Col2.TC.levels_top_row_sym I hOk hPins l Z u G (clsF u B.R.m le_rfl (Or.inr rfl)) (KP u) hG
    (hR u _ le_rfl (Or.inr rfl)) (hKP u).1
  choose Tl Ta hTl using fun u => GlobalTheory.Mem.Col2.TC.til_ties I hOk hPins l Z u (A u) (clsF u B.R.m le_rfl (Or.inr rfl)) (KP u)
    (lvOfG (A u) (Lv u B.R.m le_rfl)) (valF u B.R.m le_rfl (Or.inr rfl)) rfl (hR u _ le_rfl (Or.inr rfl)) (hKP u).1
    (fun v c z h => (hLv u B.R.m le_rfl).1 v c z h) (hIdY u B.R.m le_rfl)
  choose eW heW hEvz using fun u => (hTl u).2.2
  have hNpos : 0 < B.R.N B.R.m := by
    have := k_le_N B.R B.R.m
    have := B.R.m_add_three_le_k
    omega
  have hTilFv : ∀ u, TilBaseFv (Tl u) (clsF u B.R.m le_rfl (Or.inr rfl)) (fun v => fMe u B.R.m le_rfl (β0 u B.R.m (Or.inr rfl)) v) := by
    intro u v t x r ht hr
    refine hFvT u B.R.m le_rfl (β0 u B.R.m (Or.inr rfl)) v x ⟨B.R.N B.R.m - 1, by omega⟩ r t (by show B.R.N B.R.m - 1 + 1 = _; omega) ht ?_
    refine hr.trans ((hform_last _ hNpos (hN B.R.m le_rfl).1 (hTl u).1 x).trans ?_)
    exact congrArg (fun s : B.host.E => s * (show B.host.E from x ⟨B.R.N B.R.m - 1, Nat.sub_lt hNpos Nat.one_pos⟩)) (sigD_conj (I.rec7 l Z) _)
  have hFrExt : ∀ u, FrExtFr (D := I.rec7 l Z) (Tl u).z0 G (VM u).fr (VP u).fr := by
    intro u
    rw [funext (hTl u).1]
    exact (hVM u).2.2.2
  let F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch u) (chOf u) := fun u =>
    { atT := A u
      gl := G
      gl_K := fun i => by rw [hG.piG]; exact X.piG_K i
      cls := clsF u
      val := valF u
      glev0 := V0 u
      lamM := lamM u
      lamM_eq := (hVM u).1
      glevM := VM u
      lv := fun i hi => lvOfG (A u) (Lv u i hi)
      fMe := fun i hi h v => fMe u i hi (β0 u i h) v
      fv := fun i hi h => fvOfG (A u) (Lv u i hi) (K u i hi) (β0 u i h) (hβ0 u i h) (fMe u i hi) (hFv u i hi)
      upN := fun i hi h => upOfG (A u) (Lv u i hi) (K u i hi) (β0 u i h) (hβ0 u i h) (eY u i hi) (valF u i hi h) rfl
        (hUp u i hi)
      dnN := fun i hi h => dnOfG (A u) (Lv u i hi) (K u i hi) (β0 u i h) (hβ0 u i h) (eY u i hi) (valF u i hi h) rfl
        (hDn u i hi)
      norm := fun i hi h => (normOfG (D := I.rec7 l Z) (u := u) (eY u i hi) (valF u i hi h) rfl (hNm u i hi) :)
      bw := fun i hi h => bwOfG (A u) (eY u i hi) (valF u i hi h) rfl (hBw u i hi)
      ch := fun i _ h2 β => K u i (le_of_succ_m h2) β
      H := Hc u
      lamC := lamC u
      glevC := fun i _ h2 β => (hGH u i β (le_of_succ_m h2)).some
      eYC := fun i _ h2 => eY u i (le_of_succ_m h2)
      deC := fun i _ h2 => hde1 u i (le_of_succ_m h2)
      valC := fun i _ h2 => hVG u i (le_of_succ_m h2)
      ipVC := fun i _ h2 => (hIN u i (le_of_succ_m h2)).1
      normC := fun i _ h2 => (hIN u i (le_of_succ_m h2)).2
      dilC := fun i _ h2 => hDil u i (le_of_succ_m h2)
      lvC := fun i _ h2 => Lv u i (le_of_succ_m h2)
      fMeC := fun i _ h2 => fMe u i (le_of_succ_m h2)
      fvC := fun i _ h2 => hFv u i (le_of_succ_m h2)
      upC := fun i _ h2 => hUp u i (le_of_succ_m h2)
      dnC := fun i _ h2 => hDn u i (le_of_succ_m h2)
      bwC := fun i _ h2 => hBw u i (le_of_succ_m h2)
      levJ := J u
      lamJ := lamJ u
      lamJ_eq := (hJ u).2.1
      glevJ := VJ u
      Yb := Yb u
      YbFin := hYbF u
      YbAct := hYbA u
      yb := yb u
      yb_orbit := (hJ u).2.2.1
      levJ_Lb := fun _ β => ((hJ u).2.2.2 β).1
      levJ_le := fun _ β => ((hJ u).2.2.2 β).2.1
      levJ_stab := fun _ β => ((hJ u).2.2.2 β).2.2.1
      levJ_chi := fun _ β => ((hJ u).2.2.2 β).2.2.2
      clsP := KP u
      valP := WP u
      normP := (hKP u).2.1
      lamP := lamP u
      eigenvalue_eq₂ := (hVM u).2.1
      glevP := VP u
      til := Tl u
      tilLat := (hTl u).2.1
      tilFv := hTilFv u
      tilAd := Ta u
      frExt := hFrExt u
      eWz := eW u
      evz := hEvz u
      jM := jM u
      per := ⟨(hjM u).2.1, (hjM u).2.2.1, (hjM u).2.2.2.1⟩
      DGam := rfl }
  refine ⟨Ch, chOf, F, fun u => ⟨?_, ?_⟩, hChF, fun u => hU u B.R.m (Or.inr rfl), fun _ _ => rfl, hChi⟩
  · exact
      { eV := fun _ => rfl
        piU := rfl
        res := rfl
        gl := hG
        ends := fun i hi h => hR u i hi h
        yE := fun i hi h c => hYs' u i hi _ c (hβ0 u i h c)
        mid := fun i _ h2 => hRK u i (le_of_succ_m h2)
        eY := fun i hi _ => hIdY u i hi
        eYC := fun i _ h2 => hIdY u i (le_of_succ_m h2)
        pr := fun i hi => (hLv u i hi).1
        prk := fun i hi => (hLv u i hi).2
        fr0 := hV0 u
        frP := (hVM u).2.2.1
        what₂ := (hKP u).1
        eW := (hKP u).2.2
        z0 := (hTl u).1
        eWz := heW u }
  · exact ⟨fun i _ h2 => hLv u i (le_of_succ_m h2), (hJ u).1⟩

end GlobalTheory.Mem.FormSym

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_standardFormComparison_symmetricLevel_members : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∃ (Ch : B.Word → ℕ → Type) (chOf : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch u) (chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) ∧ (∀ u i, Finite (Ch u i)) ∧ (∀ u, Nonempty (Unique (Ch u B.R.m))) ∧ (∀ u u', (F u).gl = (F u').gl) ∧ CharacterCompatible (F B.u₀).gl B.R.m := by
  atlas_forward_decl GlobalTheory.Mem.FormSym.formsTiedSym_std
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.LevZero
open scoped TensorProduct

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem reL_rfl {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) : reL rfl L = L := by
  ext x; simp [reL, reV]

theorem reGL_rfl' {n : ℕ} (R : Type) [CommRing R] (g : GL (Fin n) R) : reGL rfl R g = g := by
  apply Units.ext; ext x y; rfl

theorem reGL_rfl_hom {n : ℕ} (R : Type) [CommRing R] :
    (reGL (rfl : n = n) R).toMonoidHom = MonoidHom.id _ := by
  ext1 g
  exact reGL_rfl' R g

theorem exists_reindex {a b : ℕ} (h : a = b) {σ : E →ₐ[F] E} (J : Matrix (Fin a) (Fin a) E)
    {J' : Matrix (Fin b) (Fin b) E} (hJ : ∀ x y, J' x y = J (Fin.cast h.symm x) (Fin.cast h.symm y))
    {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} {gp : Fin 2 → ℕ} {G : GLoc F E σ gp} {a' t nb skip fc : ℕ} {zl : Bool}
    (S' : Formalism.L2.Forms.StepLevel F E σ J' T f bad) (L' : GLev S' G a' t nb skip fc zl)
    {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)] (lat : cl → Submodule (𝓞 E) (Fin a → E))
    (y' : cl → UPts σ J' (FiniteAdeleRing (𝓞 F) F))
    (y_bij : Function.Bijective (fun c => (Quotient.mk'' (y' c) : Cls S')))
    (y_lat : ∀ c (x : Fin b → E ⊗[F] FiniteAdeleRing (𝓞 F) F),
      x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (reL h (lat c)) ↔
      ((y' c).1⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S'.Lb)
    (st' : ∀ c, stab c →* UJ (σ : E →+* E) J') (st_inj : ∀ c, Function.Injective (st' c))
    (st_range : ∀ c (γ : UJ (σ : E →+* E) J'), γ ∈ (st' c).range ↔
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ S'.U.map (MulAut.conj (y' c).1).toMonoidHom) :
    ∃ (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (L : GLev S G a' t nb skip fc zl)
      (y : cl → UPts σ J (FiniteAdeleRing (𝓞 F) F)) (st : ∀ c, stab c →* UJ (σ : E →+* E) J),
      Function.Bijective (fun c => (Quotient.mk'' (y c) : Cls S)) ∧
      (∀ c (x : Fin a → E ⊗[F] FiniteAdeleRing (𝓞 F) F),
        x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
          (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (lat c) ↔
        ((y c).1⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
          (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S.Lb) ∧
      (∀ c, Function.Injective (st c)) ∧
      (∀ c (γ : UJ (σ : E →+* E) J), γ ∈ (st c).range ↔
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ S.U.map (MulAut.conj (y c).1).toMonoidHom) ∧
      SameCar h S.Lb S'.Lb S.Uloc S'.Uloc S.U S'.U (fun c => (y c).1) (fun c => (y' c).1)
        (fun c s => (st c s).1) (fun c s => (st' c s).1) ∧
      ∀ i v hv, L'.fr i v hv = reGL h _ (L.fr i v hv) := by
  subst h
  obtain rfl : J' = J := by ext x y; exact hJ x y
  simp only [reL_rfl] at y_lat
  refine ⟨S', L', y', st', y_bij, y_lat, st_inj, st_range, ⟨(reL_rfl _).symm, fun v => ?_, ?_,
    fun c => (reGL_rfl' _ _).symm, fun c s => (reGL_rfl' _ _).symm⟩, fun i v hv => (reGL_rfl' _ _).symm⟩
  · rw [reGL_rfl_hom, Subgroup.map_id]
  · rw [reGL_rfl_hom, Subgroup.map_id]

end Gen

section Loc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem not_both_mem {p q : ℕ} (h : Nat.Coprime p q) (v : HeightOneSpectrum (𝓞 F)) (hp : (p : 𝓞 F) ∈ v.asIdeal)
    (hq : (q : 𝓞 F) ∈ v.asIdeal) : False := by
  obtain ⟨a, b, hab⟩ : IsCoprime (p : 𝓞 F) (q : 𝓞 F) := Nat.Coprime.cast h
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hp) (v.asIdeal.mul_mem_left _ hq)))

theorem exists_place (p : ℕ) (hp : p.Prime) : ∃ v : HeightOneSpectrum (𝓞 F), (p : 𝓞 F) ∈ v.asIdeal := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have : (Ideal.span {(p : ℤ)}).IsMaximal :=
    (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ |>.isMaximal (by simpa using hpZ.ne_zero)
  obtain ⟨Q, hQ, hov⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 F) (Ideal.span {(p : ℤ)})
  have hmem : (p : 𝓞 F) ∈ Q := by
    have : (p : ℤ) ∈ Q.under ℤ := by rw [← hov.over]; exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ.isPrime, ?_⟩, hmem⟩
  rintro rfl
  have : (p : 𝓞 F) = 0 := by simpa using hmem
  exact hp.ne_zero (by exact_mod_cast this)

theorem inJ_iff {k : Type} [Field k] {n a t fc : ℕ} (ha : n ≤ a) (hfc : n ≤ fc) (M : Matrix (Fin n) (Fin n) k) :
    InJ a t fc false M ↔ ∀ i j : Fin n, (j < i → M i j = 0) ∧ M i i = 1 := by
  have hb : ∀ x : Fin n, blkOf a t x = x := fun x => if_pos (lt_of_lt_of_le x.2 ha)
  constructor
  · rintro ⟨h1, h2, -, -⟩ i j
    exact ⟨fun h => h1 i j (by rw [hb, hb]; exact h), h2 i (lt_of_lt_of_le i.2 ha)⟩
  · intro h
    refine ⟨fun x y hxy => (h x y).1 (by rw [hb, hb] at hxy; exact hxy), fun x _ => (h x x).2,
      fun x y hy => absurd y.2 (by omega), fun hz => absurd hz (by simp)⟩

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {gp : Fin 2 → ℕ}

set_option maxHeartbeats 1000000 in

theorem mem_Uloc_iff_iwU (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) {G : GLoc F E σ gp} {a t nb skip fc : ℕ}
    (L : GLev S G a t nb skip fc false) (ha : n ≤ a) (hfc : n ≤ fc) (i : Fin 2) (v : HeightOneSpectrum (𝓞 F))
    (hv : (gp i : 𝓞 F) ∈ v.asIdeal) (hT : (T : 𝓞 F) ∉ v.asIdeal) (x : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hx : x ∈ UPts σ J (v.adicCompletion F)) :
    x ∈ S.Uloc v ↔ (L.fr i v hv)⁻¹ * bc ((RingHom.fst _ _).comp (G.sp i v hv).toRingHom) x * L.fr i v hv ∈ iwU F n v := by
  have hst : Formalism.L2.G.SplitStabL σ J v (G.sp i v hv) S.Lb (L.fr i v hv) :=
    Formalism.L2.G.splitStabL_of σ J v (G.sp i v hv) S.Lb (L.fr i v hv) (G.sp_sig i v hv)
      (Formalism.L2.G.split_integral_completion F E v _ (G.sp_alg i v hv))
      (Formalism.L2.G.self_dual_lattice_at F E n σ J v S.Lb T S.Lb_fin (fun x hx y hy => S.Lb_int y hy x hx)
        (fun y hy => S.Lb_dual y hy) hT) (L.fr_lat i v hv)
  have h1 := hst x hx
  rw [Formalism.L2.G.toFr_apply] at h1
  have key : ∀ g : GL (Fin n) (v.adicCompletionIntegers F),
      bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) g =
        (L.fr i v hv)⁻¹ * bc ((RingHom.fst _ _).comp (G.sp i v hv).toRingHom) x * L.fr i v hv →
      (InJ a t fc false (redM F v (G.mat i v hv (L.fr i v hv) x)) ↔
        redGL (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) g ∈ upperUni n _) := by
    intro g hg
    have e : G.mat i v hv (L.fr i v hv) x =
        (bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) g : GL (Fin n) (v.adicCompletion F)).1 := by
      rw [hg]; rfl
    rw [e, Formalism.L2.G.redM_bc]
    exact inJ_iff (k := Formalism.L2.Forms.kv F v) ha hfc _
  constructor
  · intro hU
    have hlev := S.Uloc_lev v hU
    obtain ⟨g, hg⟩ := h1.1 hlev
    exact Subgroup.mem_map.2 ⟨g, Subgroup.subset_closure ((key g hg).1 ((L.mem i v hv x hlev).1 hU)), hg⟩
  · intro hI
    obtain ⟨g, hg, e⟩ := Subgroup.mem_map.1 hI
    exact (L.mem i v hv x (h1.2 ⟨g, e⟩)).2
      ((key g e).2 (Formalism.L2.G.Triv.closure_upperUni _ _ (Subgroup.mem_comap.1 hg)))

set_option maxHeartbeats 1000000 in

theorem stab_class_lattice (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (M : Submodule (𝓞 E) (Fin n → E))
    (hfin : Module.Finite (𝓞 E) M) (hspan : Submodule.span E (M : Set (Fin n → E)) = ⊤)
    (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hy : ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
        x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
          (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) M ↔
        (y⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
          (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S.Lb)
    (γ : GL (Fin n) E)
    (hγ : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ ∈ S.U.map (MulAut.conj y).toMonoidHom) (x : Fin n → E) :
    x ∈ M ↔ γ.1 *ᵥ x ∈ M := by
  obtain ⟨k, hk, e⟩ := Subgroup.mem_map.1 hγ
  have hk' := (S.U_eq k).1 hk
  have hst := ((GlobalTheory.LatticeStabLocal.mem_levelAfL_iff F E σ n J S.Lb S.Lb_fin k).2
    ⟨hk'.1, fun v => S.Uloc_lev v (hk'.2 v)⟩).2
  have hM : ∀ z : Fin n → E, z ∈ M ↔ (y⁻¹).1 *ᵥ (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (z i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S.Lb := by
    intro z
    rw [← hy]
    have h1 : z ∈ Formalism.UG.CS.globLat (F := F) 1 M ↔
        ((1 : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))⁻¹).1 *ᵥ
          (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (z i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
          (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) M := Iff.rfl
    rwa [Formalism.UG.P.global_lattice_one_holds F E (Fin n) M hfin hspan, inv_one, Units.val_one, one_mulVec] at h1
  have e2 : (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((γ.1 *ᵥ x) i)) =
      (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ).1 *ᵥ
        (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) := by
    funext b
    exact RingHom.map_mulVec (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 x b
  have e3 : y⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ = k * y⁻¹ := by
    rw [← e]
    show y⁻¹ * (y * k * y⁻¹) = _
    group
  rw [hM, hM, e2, mulVec_mulVec, ← Units.val_mul, e3, Units.val_mul, ← mulVec_mulVec]
  exact hst _

end Loc

theorem clsCrd_zero (D : D7) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) :
    clsCrd D u 0 (Nat.zero_le _) c = reL (rank_eq_first_level D.R) (D.sp.crdLat0 (D.clsLat u 0 c)) := by
  unfold clsCrd reL Spaces.crdLat0
  rw [← Submodule.map_comp]
  rfl

theorem crdLat0_fin (D : D7) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) :
    Module.Finite (𝓞 D.host.E) (D.sp.crdLat0 (D.clsLat u 0 c)) :=
  Module.Finite.iff_fg.2 ((D.clsLat_lat u 0 c).fg.map _)

theorem crdLat0_span (D : D7) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) :
    Submodule.span D.host.E (D.sp.crdLat0 (D.clsLat u 0 c) : Set (Fin D.R.k → D.host.E)) = ⊤ := by
  have : (D.sp.crdLat0 (D.clsLat u 0 c) : Set (Fin D.R.k → D.host.E)) =
      (D.sp.crd0 : (D.sp.X 0).V →ₗ[D.host.E] (Fin D.R.k → D.host.E)) '' (D.clsLat u 0 c : Set (D.sp.X 0).V) := rfl
  rw [this, Submodule.span_image, (D.clsLat_lat u 0 c).span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact D.sp.crd0.surjective

set_option maxHeartbeats 4000000 in

theorem exists_colLevel (D : D7) (u : D.what₂.Word) {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (F : FormsTiedSym D u Ch chOf) :
    ∃ L : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u),
      SameCar (rank_eq_first_level D.R) L.Lb (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb
        L.Uloc (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Uloc
        L.U (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U
        (fun c => (L.y c).1) (fun c => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).y c).1)
        (fun c s => (L.stabI c s).1) (fun c s => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).stabI c s).1) ∧
      F.gl.sp = L.splitG ∧ ∀ i v h, F.glev0.fr i v h = reGL (rank_eq_first_level D.R) _ (L.frG i v h) := by
  obtain ⟨S, L, y, st, hbij, hlat, hinj, hrange, hcar, hfr⟩ :=
    exists_reindex (rank_eq_first_level D.R) (σ := sigD D) D.sp.gram0 (J' := gramN D 0 (Nat.zero_le _)) (fun _ _ => rfl)
      (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev F.glev0 (fun c => D.sp.crdLat0 (D.clsLat u 0 c))
      (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).y (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).y_bij
      (fun c x => by rw [← clsCrd_zero]; exact (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).y_lat c x)
      (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).stabI (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).stabI_inj
      (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).stabI_range
  obtain ⟨w, hw⟩ := exists_place (F := D.host.F) (D.host.g 0) (D.host.g_prime 0)
  refine ⟨{
    Lb := S.Lb
    Lb_fin := S.Lb_fin
    Lb_span := S.Lb_span
    Lb_int := S.Lb_int
    Lb_dual := S.Lb_dual
    Lb_index := S.Lb_index
    Uloc := S.Uloc
    Uloc_le := S.Uloc_le
    Uloc_lev := S.Uloc_lev
    Uloc_hyp := fun v h0 h1 hT => S.Uloc_hyp v (fun h => Or.elim h h0 h1) hT
    splitG := F.gl.sp
    splitG_sig := F.gl.sp_sig
    frG := L.fr
    Uloc_g := fun i v h x hx => mem_Uloc_iff_iwU S L le_rfl (rank_eq_first_level D.R).le i v h
      (fun hT => not_both_mem ((Nat.coprime_primes (D.mem u).A.T_prime (D.host.g_prime i)).2 (D.T_ne_g u i)) v hT h) x hx
    fM := S.fM
    fM_acg := S.fM_acg
    fM_mod := S.fM_mod
    fT := S.fT
    fT_ne := S.fT_ne
    fT_T := S.fT_T
    fM_card := S.fM_card
    fT_L := S.fT_L
    UlocAlt := S.UlocAlt
    U := S.U
    U_eq := S.U_eq
    U_compact := S.U_compact
    U_open := S.U_open
    w1 := w
    reflection_mem_Glev_castSucc := hw
    y := y
    y_bij := hbij
    y_lat := hlat
    stabI := st
    stabI_inj := hinj
    stabI_range := fun c γ hγ => hrange c ⟨γ, hγ⟩
    stabI_lat := fun c γ x => stab_class_lattice S _ (crdLat0_fin D u c) (crdLat0_span D u c) (y c).1 (hlat c)
      (st c γ).1 ((hrange c (st c γ)).1 ⟨γ, rfl⟩) x }, hcar, rfl, hfr⟩

set_option maxHeartbeats 4000000 in

theorem colLevel_of_forms : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F →
  ∃ L : ColLevel (I.rec7 l Z).R (I.rec7 l Z).host.F (I.rec7 l Z).host.E (I.rec7 l Z).sp (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).C ((I.rec7 l Z).mem u).A ((I.rec7 l Z).clsLat u),
    SameCar (rank_eq_first_level (I.rec7 l Z).R) L.Lb (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb
      L.Uloc (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Uloc
      L.U (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U
      (fun c => (L.y c).1) (fun c => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).y c).1)
      (fun c s => (L.stabI c s).1) (fun c s => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).stabI c s).1) ∧
    F.gl.sp = L.splitG ∧ ∀ i v h, F.glev0.fr i v h = reGL (rank_eq_first_level (I.rec7 l Z).R) _ (L.frG i v h) :=
  fun I _ _ l Z u _ _ F _ => exists_colLevel (I.rec7 l Z) u F

end GlobalTheory.Mem.LevZero
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnLevel_of_stepZeroFormsLevel_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F →
  ∃ L : ColLevel (I.rec7 l Z).R (I.rec7 l Z).host.F (I.rec7 l Z).host.E (I.rec7 l Z).sp (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).C ((I.rec7 l Z).mem u).A ((I.rec7 l Z).clsLat u),
    SameCar (rank_eq_first_level (I.rec7 l Z).R) L.Lb (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb
      L.Uloc (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Uloc
      L.U (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U
      (fun c => (L.y c).1) (fun c => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).y c).1)
      (fun c s => (L.stabI c s).1) (fun c s => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).stabI c s).1) ∧
    F.gl.sp = L.splitG ∧ ∀ i v h, F.glev0.fr i v h = reGL (rank_eq_first_level (I.rec7 l Z).R) _ (L.frG i v h) := by
  atlas_forward_decl GlobalTheory.Mem.LevZero.colLevel_of_forms
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianStepLevel_of_chartFormsLevel : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → ∀ (i : ℕ) (hi : i ≤ (I.rec7 l Z).R.m) {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)]
  {lat : cl → Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).R.N i) → (I.rec7 l Z).host.E)}
  (K : LevelChart (I.rec7 l Z) ((I.rec7 l Z).mem u).A.T (badG (I.rec7 l Z)) i hi stab lat)
  {Hs : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ((I.rec7 l Z).host.g a : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal →
    Subgroup (GL (Fin ((I.rec7 l Z).R.N i)) (kv (I.rec7 l Z).host.F v))} {lam : ∀ a v h, Hs a v h →* ℂˣ},
  GLevH K.lev F.gl Hs lam → (∀ x, x ∈ K.lev.Lb ↔ x ∈ baseL B ((I.rec7 l Z).R.N i) (X.piT u)) →
  ∃ L : Formalism.L2.Herm.StepLevel (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).A.T (I.rec7 l Z).R.f,
    K.lev.Lb = reL (rankN (I.rec7 l Z) i hi) L.Lb ∧
    (∀ v, K.lev.Uloc v = (L.Uloc v).map (reGL (rankN (I.rec7 l Z) i hi) _).toMonoidHom) ∧
    K.lev.U = L.U.map (reGL (rankN (I.rec7 l Z) i hi) _).toMonoidHom := by
  first | exact @GlobalTheory.Mem.Col2.TC.level_of_chart | exact GlobalTheory.Mem.Col2.TC.level_of_chart | (intros; apply GlobalTheory.Mem.Col2.TC.level_of_chart <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianClassCondition_of_chartClasses : ∀ (D : D7) (i : ℕ) (hi : i ≤ D.R.m) {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {cl cl' : Type} (e : cl' ≃ cl)
  {stab : cl → Type} [∀ c, Group (stab c)] (lat : cl → Submodule (𝓞 D.host.E) (D.sp.X i).V)
  (K : LevelChart D T bad i hi stab (fun c => latCrd D i hi (lat c)))
  {T' f' : ℕ} (L : Formalism.L2.Herm.StepLevel D.sp.cm (D.sp.X i) D.host.g T' f'),
  K.lev.Lb = reL (rankN D i hi) L.Lb → K.lev.U = L.U.map (reGL (rankN D i hi) _).toMonoidHom →
  ∃ C : Formalism.L2.Herm.ClassTie D.sp.cm (D.sp.X i) L.Lb L.U (fun c' => stab (e c')) (fun c' => lat (e c')),
    (∀ c', (K.y (e c')).1 = reGL (rankN D i hi) _ (C.y c').1) ∧
    ∀ c' s, (K.stabI (e c') s).1 = reGL (rankN D i hi) _ (C.stabI c' s).1 := by
  first | exact @GlobalTheory.HermTransport.classTie_of_chart | exact GlobalTheory.HermTransport.classTie_of_chart | (intros; apply GlobalTheory.HermTransport.classTie_of_chart <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ResF

variable {D : D7} {u : D.what₂.Word}

theorem conj_conj_host (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply]
  simp

theorem exists_intF (z : 𝓞 D.host.E) (hz : D.host.conj (z : D.host.E) = z) :
    ∃ zF : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF = z := by
  have hF : (z : D.host.E) ∈ D.host.F := (D.host.conjE_mem_hostF_iff _).2 hz
  refine ⟨⟨⟨z, hF⟩, ?_⟩, ?_⟩
  · exact (isIntegral_algHom_iff (D.host.F.subtype.toIntAlgHom) Subtype.val_injective).mp
      (RingOfIntegers.isIntegral_coe z)
  · rfl

theorem res_algebraMap_surjective (A : AtTTied u) (v : (D.mem u).A.vT) :
    Function.Surjective ((A.res v).comp (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))) := by
  intro r
  obtain ⟨y, rfl⟩ := A.res_surj v r
  let cO : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv
  have hcO : ∀ y : 𝓞 D.host.E, ((cO y : 𝓞 D.host.E) : D.host.E) = D.host.conj (y : D.host.E) := fun y => rfl
  obtain ⟨t, ht⟩ := exists_intF (D := D) (A.piU + cO A.piU) (by
    push_cast; simp only [hcO, map_add, conj_conj_host]; ring)
  obtain ⟨z, hz⟩ := exists_intF (D := D) (y * cO A.piU + cO y * A.piU) (by
    push_cast; simp only [hcO, map_add, map_mul, conj_conj_host]; ring)
  have htp : t ∉ (A.eV v).1.asIdeal := by
    rw [A.res_v, ht, map_add, A.res_pi, zero_add]; exact A.res_conj v _ rfl
  obtain ⟨s, i, hi, hsi⟩ := ((A.eV v).1.isMaximal).exists_inv htp
  have hi0 : A.res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) i) = 0 := (A.res_v v i).1 hi
  have hst : A.res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s) * A.res v (cO A.piU) = 1 := by
    have := congrArg (fun x => A.res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x)) hsi
    simp only [map_add, map_mul, map_one, hi0, add_zero, ht, A.res_pi, zero_add] at this
    exact this
  refine ⟨s * z, ?_⟩
  simp only [RingHom.comp_apply, map_mul, hz, map_add, A.res_pi, mul_zero, add_zero]
  rw [mul_comm (A.res v y), ← mul_assoc, hst, one_mul]

theorem exists_fv_equiv (A : AtTTied u) (v : (D.mem u).A.vT) :
    ∃ e : (D.mem u).A.Fv v ≃+* (𝓞 D.host.F ⧸ (A.eV v).1.asIdeal),
      ∀ a : 𝓞 D.host.F, e (A.res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a)) = Ideal.Quotient.mk _ a := by
  have hker : (A.eV v).1.asIdeal = RingHom.ker ((A.res v).comp (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))) := by
    ext x; rw [RingHom.mem_ker]; exact A.res_v v x
  refine ⟨((Ideal.quotEquivOfEq hker).trans
    (RingHom.quotientKerEquivOfSurjective (res_algebraMap_surjective A v))).symm, fun a => ?_⟩
  rw [RingEquiv.symm_apply_eq]
  rfl

theorem fv_equiv_quot : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → ∀ v : ((I.rec7 l Z).mem u).A.vT,
  ∃ e : ((I.rec7 l Z).mem u).A.Fv v ≃+* (𝓞 (I.rec7 l Z).host.F ⧸ (F.atT.eV v).1.asIdeal),
    ∀ a : 𝓞 (I.rec7 l Z).host.F, e (F.atT.res v (algebraMap (𝓞 (I.rec7 l Z).host.F) (𝓞 (I.rec7 l Z).host.E) a)) = Ideal.Quotient.mk _ a :=
  by
  intro B X I _ _ l Z u Ch chOf F _ v
  exact exists_fv_equiv F.atT v

end GlobalTheory.Mem.Col2.ResF

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueField_equiv_realSubfieldQuotient_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → ∀ v : ((I.rec7 l Z).mem u).A.vT,
  ∃ e : ((I.rec7 l Z).mem u).A.Fv v ≃+* (𝓞 (I.rec7 l Z).host.F ⧸ (F.atT.eV v).1.asIdeal),
    ∀ a : 𝓞 (I.rec7 l Z).host.F, e (F.atT.res v (algebraMap (𝓞 (I.rec7 l Z).host.F) (𝓞 (I.rec7 l Z).host.E) a)) = Ideal.Quotient.mk _ a := by
  atlas_forward_decl GlobalTheory.Mem.Col2.ResF.fv_equiv_quot
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

set_option maxHeartbeats 8000000 in
theorem chart_level_classes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → ∀ (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ (I.rec7 l Z).R.m) (β : Ch i),
  ∃ P : (L : Formalism.L2.Herm.StepLevel (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).A.T (I.rec7 l Z).R.f) ×'
      Formalism.L2.Herm.ClassTie (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) L.Lb L.U (fun c : {c // chOf i c = β} => ((I.rec7 l Z).mem u).C.stab i c.1) (fun c => (I.rec7 l Z).clsLat u i c.1),
    SameCar (rankN (I.rec7 l Z) i (le_of_succ_m h2)) P.1.Lb (F.ch i h1 h2 β).lev.Lb P.1.Uloc (F.ch i h1 h2 β).lev.Uloc
      P.1.U (F.ch i h1 h2 β).lev.U (fun c => (P.2.y c).1) (fun c => ((F.ch i h1 h2 β).y c).1)
      (fun c s => (P.2.stabI c s).1) (fun c s => ((F.ch i h1 h2 β).stabI c s).1) := by
  intro B X I hOk hP l Z u Ch chOf F hS i h1 h2 β
  obtain ⟨k, hk⟩ := hS.mid i h1 h2
  obtain ⟨L, hLb, hUl, hU⟩ := GlobalTheory.T.hermitianStepLevel_of_chartFormsLevel I hOk hP l Z u F hS i (le_of_succ_m h2) (F.ch i h1 h2 β) (F.glevC i h1 h2 β) (hk.lb β)
  obtain ⟨C, hy, hst⟩ := GlobalTheory.T.hermitianClassCondition_of_chartClasses (I.rec7 l Z) i (le_of_succ_m h2) (Equiv.refl _) (fun c : {c // chOf i c = β} => (I.rec7 l Z).clsLat u i c.1)
    (F.ch i h1 h2 β) L hLb hU
  exact ⟨⟨L, C⟩, { Lb_eq := hLb, Uloc_eq := hUl, U_eq := hU, y_eq := hy, st_eq := hst }⟩

set_option maxHeartbeats 8000000 in
theorem top_level_classes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → ∀ (i : ℕ) (hm : i ≤ (I.rec7 l Z).R.m) (him : i = (I.rec7 l Z).R.m) (β : Ch i) (hβ : ∀ c, chOf i c = β),
  ∃ P : (L : Formalism.L2.Herm.StepLevel (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).A.T (I.rec7 l Z).R.f) ×'
      Formalism.L2.Herm.ClassTie (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) L.Lb L.U (fun c : {c // chOf i c = β} => ((I.rec7 l Z).mem u).C.stab i c.1) (fun c => (I.rec7 l Z).clsLat u i c.1),
    SameCar (rankN (I.rec7 l Z) i hm) P.1.Lb (F.cls i hm (Or.inr him)).lev.Lb P.1.Uloc (F.cls i hm (Or.inr him)).lev.Uloc
      P.1.U (F.cls i hm (Or.inr him)).lev.U (fun c => (P.2.y ⟨c, hβ c⟩).1) (fun c => ((F.cls i hm (Or.inr him)).y c).1)
      (fun c s => (P.2.stabI ⟨c, hβ c⟩ s).1) (fun c s => ((F.cls i hm (Or.inr him)).stabI c s).1) := by
  intro B X I hOk hP l Z u Ch chOf F hS i hm him β hβ
  subst him
  obtain ⟨k, hk⟩ := hS.ends _ hm (Or.inr rfl)
  obtain ⟨L, hLb, hUl, hU⟩ := GlobalTheory.T.hermitianStepLevel_of_chartFormsLevel I hOk hP l Z u F hS _ hm ((F.cls _ hm (Or.inr rfl)).toChart) F.glevM (hk.lb ())
  obtain ⟨C, hy, hst⟩ := GlobalTheory.T.hermitianClassCondition_of_chartClasses (I.rec7 l Z) _ hm (Equiv.subtypeUnivEquiv hβ) (fun c => (I.rec7 l Z).clsLat u _ c)
    ((F.cls _ hm (Or.inr rfl)).toChart) L hLb hU
  exact ⟨⟨L, C⟩, { Lb_eq := hLb, Uloc_eq := hUl, U_eq := hU, y_eq := fun c => hy ⟨c, hβ c⟩, st_eq := fun c => hst ⟨c, hβ c⟩ }⟩

set_option maxHeartbeats 8000000 in
theorem level_classes_of {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf)
    (hS : I.StdF l Z u F) (hU : Nonempty (Unique (Ch (I.rec7 l Z).R.m))) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ (I.rec7 l Z).R.m) (β : Ch i) :
    ∃ P : (L : Formalism.L2.Herm.StepLevel (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).A.T (I.rec7 l Z).R.f) ×'
      Formalism.L2.Herm.ClassTie (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) L.Lb L.U (fun c : {c // chOf i c = β} => ((I.rec7 l Z).mem u).C.stab i c.1) (fun c => (I.rec7 l Z).clsLat u i c.1),
      (∀ h2 : i + 1 ≤ (I.rec7 l Z).R.m,
        SameCar (rankN (I.rec7 l Z) i (le_of_succ_m h2)) P.1.Lb (F.ch i h1 h2 β).lev.Lb P.1.Uloc (F.ch i h1 h2 β).lev.Uloc
          P.1.U (F.ch i h1 h2 β).lev.U (fun c => (P.2.y c).1) (fun c => ((F.ch i h1 h2 β).y c).1)
          (fun c s => (P.2.stabI c s).1) (fun c s => ((F.ch i h1 h2 β).stabI c s).1)) ∧
      (∀ (him : i = (I.rec7 l Z).R.m) (hβ : ∀ c, chOf i c = β),
        SameCar (rankN (I.rec7 l Z) i hm) P.1.Lb (F.cls i hm (Or.inr him)).lev.Lb P.1.Uloc (F.cls i hm (Or.inr him)).lev.Uloc
          P.1.U (F.cls i hm (Or.inr him)).lev.U (fun c => (P.2.y ⟨c, hβ c⟩).1) (fun c => ((F.cls i hm (Or.inr him)).y c).1)
          (fun c s => (P.2.stabI ⟨c, hβ c⟩ s).1) (fun c s => ((F.cls i hm (Or.inr him)).stabI c s).1)) := by
  by_cases h2 : i + 1 ≤ (I.rec7 l Z).R.m
  · obtain ⟨P, hP2⟩ := chart_level_classes I hOk hP l Z u F hS i h1 h2 β
    exact ⟨P, fun _ => hP2, fun him _ => absurd h2 (by omega)⟩
  · have him : i = (I.rec7 l Z).R.m := by omega
    have hβ : ∀ c, chOf i c = β := by
      intro c
      subst him
      obtain ⟨U⟩ := hU
      exact Subsingleton.elim _ _
    obtain ⟨P, hP3⟩ := top_level_classes I hOk hP l Z u F hS i hm him β hβ
    exact ⟨P, fun h => absurd h h2, fun _ _ => hP3⟩

set_option maxHeartbeats 8000000 in
theorem hermColsCh_of_forms : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Ch : B.Word → ℕ → Type) (chOf : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch u) (chOf u)) (hf : ∀ u i, Finite (Ch u i)) (hm : ∀ u, Nonempty (Unique (Ch u B.R.m))), (∀ u, I.StdF l Z u (F u)) → ∃ lev0 lev cls vT Fv, CarH (D := (I.rec7 l Z)) { lev0 := lev0, Ch := Ch, ChFin := hf, Ch_m := hm, chOf := chOf, lev := lev, cls := cls, vT := vT, Fv := Fv } F := by
  intro B X I hOk hP l Z Ch chOf F hf hm hS
  have L0 := fun u => GlobalTheory.T.columnLevel_of_stepZeroFormsLevel_trueColumns I hOk hP l Z u (F u) (hS u)
  have LP := fun u i h1 hm' β => level_classes_of I hOk hP l Z u (F u) (hS u) (hm u) i h1 hm' β
  have LF := fun u v => GlobalTheory.T.residueField_equiv_realSubfieldQuotient_trueColumns I hOk hP l Z u (F u) (hS u) v
  refine ⟨fun u => (L0 u).choose, fun u i h1 hm' β => (LP u i h1 hm' β).choose.1,
    fun u i h1 hm' β => (LP u i h1 hm' β).choose.2, fun u => (F u).atT.eV, fun u v => (LF u v).choose, ?_⟩
  exact {
    eV := fun u => rfl
    fv := fun u v a => (LF u v).choose_spec a
    car0 := fun u => (L0 u).choose_spec.1
    carC := fun u i h1 h2 β => (LP u i h1 (le_of_succ_m h2) β).choose_spec.1 h2
    carM := fun u => (LP u _ (one_le_m _) le_rfl _).choose_spec.2 rfl (fun c => @Unique.eq_default _ (hm u).some (chOf u _ c))
    sp := fun u => (L0 u).choose_spec.2.1
    fr0 := fun u => (L0 u).choose_spec.2.2 }

end GlobalTheory.Mem.Col2.TC
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianColumnChoices_of_formsLevelsClasses : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Ch : B.Word → ℕ → Type) (chOf : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch u) (chOf u)) (hf : ∀ u i, Finite (Ch u i)) (hm : ∀ u, Nonempty (Unique (Ch u B.R.m))), (∀ u, I.StdF l Z u (F u)) → ∃ lev0 lev cls vT Fv, CarH (D := (I.rec7 l Z)) { lev0 := lev0, Ch := Ch, ChFin := hf, Ch_m := hm, chOf := chOf, lev := lev, cls := cls, vT := vT, Fv := Fv } F := by
  atlas_forward_decl GlobalTheory.Mem.Col2.TC.hermColsCh_of_forms
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.PsiRat

theorem natCast_resField_eq_zero (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) (h : (p : 𝓞 F) ∈ v.asIdeal) : (p : kv F v) = 0 := by
  rw [← map_natCast (IsLocalRing.residue (v.adicCompletionIntegers F)), IsLocalRing.residue_eq_zero_iff]
  refine (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) _))
    (a := (p : v.adicCompletionIntegers F))).2 ?_
  have h1 : ((p : v.adicCompletionIntegers F) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) ((p : 𝓞 F) : F) := by
    simp
  rw [h1]
  have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v ((p : 𝓞 F) : F)
  have h3 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (p : 𝓞 F)).2 h
  exact h2.trans_lt h3

theorem range_of_pow_g (B : Base) (i : Fin 2) (z : ℂ) (hz : z ^ B.host.g i = 1) : ∃ r : B.LL, B.embLL r = z := by
  have hp := B.host.g_prime i
  obtain ⟨ζ, -, hζ⟩ := B.roots_Ks (B.host.g i * (B.host.g i - 1)) (by fin_cases i <;> simp)
  have hne : B.host.g i * (B.host.g i - 1) ≠ 0 := mul_ne_zero hp.ne_zero (by have := hp.two_le; omega)
  have hprim := Complex.isPrimitiveRoot_exp _ hne
  have : NeZero (B.host.g i * (B.host.g i - 1)) := ⟨hne⟩
  obtain ⟨k, -, hk⟩ := hprim.eq_pow_of_pow_eq_one (ξ := z) (by rw [pow_mul, hz, one_pow])
  exact ⟨ζ ^ k, by rw [map_pow, hζ, hk]⟩

end GlobalTheory.Mem.Col2.TC.PsiRat

open GlobalTheory.Mem.Col2.TC.PsiRat in

theorem GlobalTheory.Mem.Col2.TC.additiveCharacter_typePrimes_values_coefficientField : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (G : GLoc (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (I.rec7 l Z).host.g), I.IdG l Z G → ∀ j v h x, ∃ r : B.LL, B.embLL r = G.psi0 j v h x := by
  intro B X I _ _ l Z G _ j v h x
  refine range_of_pow_g B j _ ?_
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  have h0 := natCast_resField_eq_zero _ v _ h
  erw [h0]
  rw [zero_mul, AddChar.map_zero_eq_one]

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_psi0_eq_embLL : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (G : GLoc (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (I.rec7 l Z).host.g), I.IdG l Z G → ∀ j v h x, ∃ r : B.LL, B.embLL r = G.psi0 j v h x := by
  atlas_forward_decl GlobalTheory.Mem.Col2.TC.additiveCharacter_typePrimes_values_coefficientField
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.LevTwist

section Re

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem reL_rfl {a : ℕ} (L : Submodule (𝓞 E) (Fin a → E)) : reL (rfl : a = a) L = L := by
  have e : ((reV (rfl : a = a) E : (Fin a → E) →ₗ[E] (Fin a → E)).restrictScalars (𝓞 E)) = LinearMap.id :=
    LinearMap.ext fun x => funext fun i => rfl
  rw [reL, e, Submodule.map_id]

theorem reGL_rfl {a : ℕ} (R : Type) [CommRing R] (g : GL (Fin a) R) : reGL (rfl : a = a) R g = g := by
  ext i j
  rfl

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem fun_transport {a b : ℕ} (h : a = b) (σ : E →ₐ[F] E) (J : Matrix (Fin a) (Fin a) E) (J' : Matrix (Fin b) (Fin b) E)
    (hJ : J' = J.reindex (finCongr h) (finCongr h)) (Lb : Submodule (𝓞 E) (Fin a → E)) (Lb' : Submodule (𝓞 E) (Fin b → E))
    (hL : Lb' = reL h Lb) (v : HeightOneSpectrum (𝓞 F)) {M : Type} [AddCommGroup M] [Module (intV E v) M]
    (f' : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J' Lb')) →ₗ[intV E v] M) :
    ∃ f : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J Lb)) →ₗ[intV E v] M,
      (f' ≠ 0 → f ≠ 0) ∧ (∀ r : intV E v, (∀ x, f' (r • x) = 0) → ∀ x, f (r • x) = 0) ∧
      ((∀ x, x.1 ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb' → f' x = 0) →
        ∀ x, x.1 ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb → f x = 0) ∧
      ∀ (U : Subgroup (GL (Fin a) (E ⊗[F] v.adicCompletion F))) (U' : Subgroup (GL (Fin b) (E ⊗[F] v.adicCompletion F))),
        U' = U.map (reGL h _).toMonoidHom → U' = levelVL σ J' v Lb' ⊓ stabFun _ f' →
        U = levelVL σ J v Lb ⊓ stabFun _ f := by
  subst h
  obtain rfl : J' = J := by
    rw [hJ]; ext i j; rfl
  obtain rfl : Lb' = Lb := by rw [hL, reL_rfl]
  refine ⟨f', id, fun _ h => h, id, ?_⟩
  rintro U U' rfl h
  rw [← h]
  ext g
  simp only [Subgroup.mem_map]
  constructor
  · intro hg
    exact ⟨g, hg, reGL_rfl _ g⟩
  · rintro ⟨g', hg', e⟩
    have : g' = g := (reGL_rfl _ g').symm.trans e
    exact this ▸ hg'

end Re

section Pi

theorem smul_eq_zero_of_prime_card {S M : Type} [CommRing S] [AddCommGroup M] [Module S M] {p : ℕ} (hp : p.Prime)
    (hc : Nat.card M = p) (a : S) {m₀ : M} (h1 : m₀ ≠ 0) (h2 : a • m₀ = 0) (m : M) : a • m = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 (mem_zmultiples_of_prime_card hc h1 (g' := m))
  rw [smul_comm, h2, smul_zero]

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem pi_kills {D : D7} {u : D.what₂.Word} {A : AtTTied u} {i : ℕ} {hi : i ≤ D.R.m} (P : LvTied u A i hi) (K : ClsTied u i hi)
    (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v) (hT : FvTie P K fMe) (v : (D.mem u).A.vT)
    (a : intV D.host.E (A.eV v).1)
    (ha : (a : D.host.E ⊗[D.host.F] (A.eV v).1.adicCompletion D.host.F) =
      inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) ((A.piU : 𝓞 D.host.E) : D.host.E))
    (m : K.lev.fM (A.eV v).1 (A.eV v).2) : a • m = 0 := by
  obtain ⟨c, -⟩ := K.y_bij.2 (Quotient.mk'' 1)
  obtain ⟨x, hx⟩ : ∃ x, (D.fm u).fv i v c x ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact (D.fm u).fv_ne i v c (LinearMap.ext hc)
  obtain ⟨z, rfl⟩ := P.pr_surj v c x
  have hin : ∀ z : ↥(Ld D u i hi c), ((bc (prV (E := D.host.E) (A.eV v).1) (K.y c).1)⁻¹).1 *ᵥ
      (fun a => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (z.1 a)) ∈
      latS (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (intV D.host.E (A.eV v).1)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) K.lev.Lb)) :=
    fun z => (GlobalTheory.LevelHecke.MovePair.ld_loc K _ c _).1 (Submodule.subset_span ⟨z.1, z.2, rfl⟩)
  have h1 : K.lev.fT _ (A.eV v).2 ⟨_, hin z⟩ ≠ 0 := by
    intro h0
    apply hx
    rw [hT v c z (hin z), h0, map_zero]
  have h3 : K.lev.fT _ (A.eV v).2 ⟨_, hin (A.piU • z)⟩ = 0 := by
    have hz0 : (D.fm u).fv i v c (P.pr v c (A.piU • z)) = 0 := by
      rw [P.pr_smul, A.res_pi, zero_smul, map_zero]
    exact (fMe v).injective (((hT v c _ (hin _)).symm.trans hz0).trans (map_zero (fMe v)).symm)
  have e : a • (⟨_, hin z⟩ : latS (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (intV D.host.E (A.eV v).1)
      (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) K.lev.Lb))) =
      ⟨_, hin (A.piU • z)⟩ := by
    apply Subtype.ext
    have e1 : (fun b => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) ((A.piU • z).1 b)) =
        (a : D.host.E ⊗[D.host.F] (A.eV v).1.adicCompletion D.host.F) •
          fun b => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (z.1 b) := by
      funext b
      rw [ha]
      show inclE (F := D.host.F) _ (((A.piU : 𝓞 D.host.E) : D.host.E) * z.1 b) = _
      rw [map_mul]
      rfl
    show (a : D.host.E ⊗[D.host.F] (A.eV v).1.adicCompletion D.host.F) •
        (((bc (prV (E := D.host.E) (A.eV v).1) (K.y c).1)⁻¹).1 *ᵥ
          (fun b => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (z.1 b))) =
        ((bc (prV (E := D.host.E) (A.eV v).1) (K.y c).1)⁻¹).1 *ᵥ
          (fun b => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) ((A.piU • z).1 b))
    rw [e1, Matrix.mulVec_smul]
  have h2 : a • K.lev.fT _ (A.eV v).2 ⟨_, hin z⟩ = 0 :=
    (map_smul (K.lev.fT _ (A.eV v).2) a _).symm.trans ((congrArg (K.lev.fT _ (A.eV v).2) e).trans h3)
  exact smul_eq_zero_of_prime_card (D.mem u).A.T_prime (K.lev.fM_card _ _) a h1 h2 m

end Pi

section Main

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem stepZeroHermitianLevel_with_formsFunctional (D : D7) (u : D.what₂.Word) {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (F : FormsTiedSym D u Ch chOf)
    (L : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (hS : SameCar (rank_eq_first_level D.R) L.Lb (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb L.Uloc
      (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Uloc L.U (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U
      (fun c => (L.y c).1) (fun c => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).y c).1)
      (fun c s => (L.stabI c s).1) (fun c s => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).stabI c s).1)) :
    ∃ L' : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u),
      L'.Lb = L.Lb ∧ L'.Uloc = L.Uloc ∧ L'.U = L.U ∧ L'.y = L.y ∧ L'.stabI = L.stabI ∧ L'.splitG = L.splitG ∧ L'.frG = L.frG ∧
      ∀ (w : HeightOneSpectrum (𝓞 D.host.F)) (h : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ w.asIdeal)
        (a : intV D.host.E w),
        (a : TensorProduct D.host.F D.host.E (w.adicCompletion D.host.F)) =
          inclE (F := D.host.F) (w.adicCompletion D.host.F) ((F.atT.piU : 𝓞 D.host.E) : D.host.E) →
        ∀ m : L'.fM w h, a • m = 0 := by
  have hJ : gramN D 0 (Nat.zero_le _) =
      (D.sp.gram0).reindex (finCongr (rank_eq_first_level D.R)) (finCongr (rank_eq_first_level D.R)) := by
    ext i j
    rfl
  have key := fun (w : HeightOneSpectrum (𝓞 D.host.F)) (h : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ w.asIdeal) =>
    fun_transport (rank_eq_first_level D.R) (sigD D) D.sp.gram0 (gramN D 0 (Nat.zero_le _)) hJ L.Lb
      (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb hS.Lb_eq w
      ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fT w h)
  choose fT' k1 k2 k3 k4 using key
  refine ⟨{ L with
    fM := (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fM
    fM_acg := (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fM_acg
    fM_mod := (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fM_mod
    fT := fT'
    fT_ne := fun v h => k1 v h ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fT_ne v h)
    fT_T := fun v h => k2 v h _ ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fT_T v h)
    fM_card := (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fM_card
    fT_L := fun v h => k3 v h ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fT_L v h)
    UlocAlt := fun v h => k4 v h _ _ (hS.Uloc_eq v) ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.UlocAlt v h) },
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro w h a ha m
  obtain ⟨v, hv⟩ := F.atT.eV.surjective ⟨w, h⟩
  have hw : (F.atT.eV v).1 = w := congrArg Subtype.val hv
  subst hw
  exact pi_kills (F.lv 0 (Nat.zero_le _)) (F.cls 0 (Nat.zero_le _) (Or.inl rfl))
    (F.fMe 0 (Nat.zero_le _) (Or.inl rfl)) (F.fv 0 (Nat.zero_le _) (Or.inl rfl)) v a ha m

end Main

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem stepZeroHermitianLevel_uniformiser_kills_values : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → ∀ (L : ColLevel (I.rec7 l Z).R (I.rec7 l Z).host.F (I.rec7 l Z).host.E (I.rec7 l Z).sp (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).C ((I.rec7 l Z).mem u).A ((I.rec7 l Z).clsLat u)), SameCar (rank_eq_first_level (I.rec7 l Z).R) L.Lb (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb L.Uloc (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Uloc L.U (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U (fun c => (L.y c).1) (fun c => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).y c).1) (fun c s => (L.stabI c s).1) (fun c s => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).stabI c s).1) → ∃ L' : ColLevel (I.rec7 l Z).R (I.rec7 l Z).host.F (I.rec7 l Z).host.E (I.rec7 l Z).sp (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).C ((I.rec7 l Z).mem u).A ((I.rec7 l Z).clsLat u), L'.Lb = L.Lb ∧ L'.Uloc = L.Uloc ∧ L'.U = L.U ∧ L'.y = L.y ∧ L'.stabI = L.stabI ∧ L'.splitG = L.splitG ∧ L'.frG = L.frG ∧ ∀ (w : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (h : ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ w.asIdeal) (a : intV (I.rec7 l Z).host.E w), (a : TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (w.adicCompletion (I.rec7 l Z).host.F)) = inclE (F := (I.rec7 l Z).host.F) (w.adicCompletion (I.rec7 l Z).host.F) ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) → ∀ m : L'.fM w h, a • m = 0 :=
  by
  intro B X I _ _ l Z u Ch chOf F _ L hS
  exact stepZeroHermitianLevel_with_formsFunctional (I.rec7 l Z) u F L hS

end GlobalTheory.Mem.Col2.LevTwist

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepZeroHermitianLevel_uniformiser_kills_values_alt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → ∀ (L : ColLevel (I.rec7 l Z).R (I.rec7 l Z).host.F (I.rec7 l Z).host.E (I.rec7 l Z).sp (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).C ((I.rec7 l Z).mem u).A ((I.rec7 l Z).clsLat u)), SameCar (rank_eq_first_level (I.rec7 l Z).R) L.Lb (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb L.Uloc (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Uloc L.U (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U (fun c => (L.y c).1) (fun c => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).y c).1) (fun c s => (L.stabI c s).1) (fun c s => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).stabI c s).1) → ∃ L' : ColLevel (I.rec7 l Z).R (I.rec7 l Z).host.F (I.rec7 l Z).host.E (I.rec7 l Z).sp (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).C ((I.rec7 l Z).mem u).A ((I.rec7 l Z).clsLat u), L'.Lb = L.Lb ∧ L'.Uloc = L.Uloc ∧ L'.U = L.U ∧ L'.y = L.y ∧ L'.stabI = L.stabI ∧ L'.splitG = L.splitG ∧ L'.frG = L.frG ∧ ∀ (w : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (h : ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ w.asIdeal) (a : intV (I.rec7 l Z).host.E w), (a : TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (w.adicCompletion (I.rec7 l Z).host.F)) = inclE (F := (I.rec7 l Z).host.F) (w.adicCompletion (I.rec7 l Z).host.F) ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) → ∀ m : L'.fM w h, a • m = 0 := by
  atlas_forward_decl GlobalTheory.Mem.Col2.LevTwist.stepZeroHermitianLevel_uniformiser_kills_values
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

set_option maxHeartbeats 4000000 in

theorem colsTiedSym_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)),
    ∃ C : ColsTiedSym (I.rec7 l Z), I.StdC l Z C ∧ ∀ u, I.StdLvC l Z u (C.forms u) := by
  intro B X I hOk hP l Z
  obtain ⟨Ch, chOf, F, hF, hfin, hm, hgl, hchi⟩ := GlobalTheory.T.exists_standardFormComparison_symmetricLevel_members I hOk hP l Z
  obtain ⟨lev00, lev, cls, vT, Fv, hH0⟩ := GlobalTheory.T.hermitianColumnChoices_of_formsLevelsClasses I hOk hP l Z Ch chOf F hfin hm (fun u => (hF u).1)
  choose lev0 hLb hUl hU hy hst hsp hfrG hpi using fun u => GlobalTheory.T.stepZeroHermitianLevel_uniformiser_kills_values_alt I hOk hP l Z u (F u) (hF u).1 (lev00 u) (hH0.car0 u)
  let H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z) :=
    { lev0 := lev0, Ch := Ch, ChFin := hfin, Ch_m := hm, chOf := chOf, lev := lev, cls := cls, vT := vT, Fv := Fv }
  have hH : CarH H F :=
    { eV := hH0.eV, fv := hH0.fv
      car0 := fun u => by
        show SameCar _ (lev0 u).Lb _ (lev0 u).Uloc _ (lev0 u).U _ (fun c => ((lev0 u).y c).1) _ (fun c s => ((lev0 u).stabI c s).1) _
        rw [hLb u, hUl u, hU u, hy u, hst u]; exact hH0.car0 u
      carC := hH0.carC, carM := hH0.carM
      sp := fun u => by show _ = (lev0 u).splitG; rw [hsp u]; exact hH0.sp u
      fr0 := fun u => by show ∀ i v h, _ = reGL _ _ ((lev0 u).frG i v h); rw [hfrG u]; exact hH0.fr0 u }
  obtain ⟨A, hT, hAd, hSt⟩ := GlobalTheory.T.exists_hermitian_data_carT_of_std I hOk hP l Z H F hF hH
  obtain ⟨hCof, hBase, ⟨hFv⟩, X0, hX0⟩ := GlobalTheory.T.hermitianColumns_generators_baseLattices_functionals I hOk hP l Z H F A hF hH hT
    (fun u w h a ha m => hpi u w h a (by rw [ha, hT.piU u]) m)
  have hStd := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hP l Z).1
  have hpiG : ∀ u u', (X0 u).piG = (X0 u').piG := fun u u' => by rw [hX0 u, hX0 u']
  have hpiG' : ∀ u, (F u).gl.piG = (X0 u).piG := fun u => by rw [hX0 u]; exact ((hF u).1.gl).piG
  have hfr0 : ∀ u u', (F u).glev0.fr = (F u').glev0.fr := fun u u' => by
    funext j v h
    rw [(hF u).1.fr0, (hF u').1.fr0]
  have hfrP : ∀ u u', (F u).glevP.fr = (F u').glevP.fr := fun u u' => by
    funext j v h
    rw [(hF u).1.frP, (hF u').1.frP]
  refine ⟨
    { herm :=
        { base := H, atT := A, levelZeroCompatibility := X0, ad := hAd, cof := hCof, piG := hpiG,
          stabMap := hSt, fvI := hFv, std := hStd, baseL := hBase }
      forms := F
      eV := hH.eV
      piU := hT.piU
      res := hT.res
      car0 := hH.car0
      carC := hH.carC
      carM := hH.carM
      carP := hT.carP
      lattice₂ := hT.lattice₂
      pr := hT.pr
      prk := hT.prk
      prC := hT.prC
      z0 := hT.z0
      ga := hT.ga
      sp := hH.sp
      piG := hpiG'
      fr0 := hH.fr0
      gl_const := hgl
      chi := hchi
      frame_level_zero_const := hfr0
      frP_const := hfrP }, fun u => (hF u).1, fun u => (hF u).2⟩

end GlobalTheory.Mem.Col2.TC
end
