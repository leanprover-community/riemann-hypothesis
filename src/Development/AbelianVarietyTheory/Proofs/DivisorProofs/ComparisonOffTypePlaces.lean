import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpanCuspFormsBaseTupleSecondField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondLinkOfWeightRowsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunNumericalConditionsHoldAlongFamily
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlDetEqOneOfMemUnip
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortRuleChangeOfCongr
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAdaptedCongr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceShortSeriesEqMulAdelicSeries
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMulAddEqOneOfNotMem
import Formalism.LocalToGlobal.Columns.CoefficientsModP.BaseCh
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.EqZeroOfFischSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseTupleThetaKernelTameCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeLowerBlockVectorMultipleKernelTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesDatumMoveToFullRank
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SignAtBasePlaceEqEmbedding
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.OneMapExact.det_eq_one_of_mem_base {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type}
    {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A) (h : R.IsGrp F) :
    ∀ u : F.P0, ∀ PP : R.Pg, ((R.eG (u : G) PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1 := by
  intro u PP
  obtain ⟨ψ, -, h0, -⟩ := h.levels
  have h1 : F.P0.comap R.eG.symm.toMonoidHom = Subgroup.pi Set.univ (fun v : R.Pg => unip (kP v.1) D.R.r) :=
    congrArg LevelP.H h0
  have h2 : R.eG u ∈ F.P0.comap R.eG.symm.toMonoidHom := by
    rw [Subgroup.mem_comap]; simp
  rw [h1] at h2
  rw [← Matrix.GeneralLinearGroup.val_det_apply, GlobalTheory.TraceIncl.gl_det_eq_one_of_mem_unip (h2 PP (Set.mem_univ _)),
    Units.val_one]
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.OrbitAdapt

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence GlobalTheory.ShortMove

theorem shortRule_change_mat (D : D7) (T : Full D) (hF : LawsFull T) (j : ℕ) (hj : InR D j) (n : ℕ)
    (Λ : GenLat D.host.E n) (g : Matrix (Fin n) (Fin n) D.host.E) (b : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) (hg : IsUnitaryM g) (hb : (T.dδ j n).l₂.M ∣ b)
    (hcg : GlobalTheory.UnRep.CongAt (stdLat D.host.E n) b b g)
    (hev : Even n) (hU : Λ.Unimod) (hU' : (actLat g Λ).Unimod) (hT : Λ.TrivAt (badN D))
    (hT' : (actLat g Λ).TrivAt (badN D)) (hM : Λ.TrivAt (T.dδ j n).l₂.M) (hM' : (actLat g Λ).TrivAt (T.dδ j n).l₂.M)
    (hP : P ∈ harmL T.Q.c Λ a) :
    ∃ (P' : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) (ζ : T.Q.c.F), P' ∈ harmL T.Q.c (actLat g Λ) a ∧ ζ ≠ 0 ∧
      (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧
      ∀ (x0 : Fin n → (T.Q.Dw j).La) (N N' : ℕ) (f : Rul (T.Q.Xo j) T.Q.c),
        Λ.LevOK N (T.dδ j n).l₂.M → (actLat g Λ).LevOK N' (T.dδ j n).l₂.M →
        IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j n) Λ N x0 P f →
        IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j n) (actLat g Λ) N' x0 P' (ζ • f) := by
  set d := T.dδ j n with hd
  obtain ⟨_, hnab⟩ := hF.sh.dNab j hj n
  have hCI := GlobalTheory.T.harmonic_germ_value_chart_independent
  have hbad := GlobalTheory.ShortChange.badOK_host D T.Q.H d.l₂
  have hdv : D.host.QS * D.host.q * D.host.d ∣ badN D := Dvd.intro _ rfl
  have hb1 : D.host.QS * D.host.q * D.host.d * d.l₂.M ≠ 1 := fun h => by
    have := hbad.2.1
    omega
  have hB := GlobalTheory.ShortChange.trivAt_mul (trivAt_of_dvd hdv hT) hM
  have hB' := GlobalTheory.ShortChange.trivAt_mul (trivAt_of_dvd hdv hT') hM'
  have hK := hF.p.kPsi j hj
  obtain ⟨ze, ⟨k, hk, hze⟩, hrep⟩ := GlobalTheory.T.thetaChangeOfRepRootOfUnity_of_chartIndependence hCI D.host.E T.Q.H (T.Q.Dw j) d.l₂ d.Xo₂ d.c₂ d.nab₂ n
    ⟨(GlobalTheory.PlaceInt.host_galois_discr_moves D T.Q.H).1, GlobalTheory.ShortChange.odd_rank T hF j hj, hev, hnab⟩ _ hbad
    Λ g _ _ hU hg hB hB' (isBeta_cover d hK hb1 Λ hU hB) (isBeta_cover d hK hb1 _ hU' hB')
  have hP' := ((GlobalTheory.PushKeeps.push_keeps D.host.E T.Q.H (T.Q.Dw j) T.Q.l T.Q.c n a g hg).2 Λ).2.2.2 P hP
  have hz : d.eF.symm ze ^ k = 1 := by rw [← map_pow, hze, map_one]
  refine ⟨pushLet T.Q.c g P, d.eF.symm ze, hP', fun h0 => ?_, ⟨k, hk, hz⟩,
    fun x0 N N' f hN hN' hR K _ _ _ _ hKe y y₂ hy => ?_⟩
  · rw [h0, zero_pow hk.ne'] at hz
    exact zero_ne_one hz
  obtain ⟨v, hv, hval⟩ := hR K hKe y y₂ hy
  have h₂ := (((GlobalTheory.PlaceInt.eF_transfer D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c n d Λ).2.1 a P hP).1)
  have h₂' := (((GlobalTheory.PlaceInt.eF_transfer D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c n d _).2.1 a _ hP').1)
  obtain ⟨v', hv', -⟩ := (GlobalTheory.shortThetaValue_existsUnique_natural GlobalTheory.firstFiveLaws.1 hCI D.host.E T.Q.H (T.Q.Dw j)
    d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab n _ N' hU' hM' hN' a _ h₂'.1 (d.w x0)
    (d.eF (betaH (Dw := T.Q.Dw j) T.Q.c (actLat g Λ)))).1 K y₂
  refine ⟨v', hv', ?_⟩
  rw [map_pushLet] at hv'
  have hvv := hrep (d.w x0) (fixesDatum_of_congAt d.c₂ hb hcg _) N N' hN hN' a _ h₂ K y₂ v v' hv hv'
  have hs : evR (T.Q.Xo j) T.Q.c (d.eF.symm ze • f) y =
      algebraMap T.Q.c.F K (d.eF.symm ze) * evR (T.Q.Xo j) T.Q.c f y :=
    evR_mul (T.Q.Xo j) T.Q.c _ f _ (fun p y => Algebra.smul_def _ _) y
  rw [hs, hval, hvv, ← hKe, AlgEquiv.apply_symm_apply]
  ring

theorem congAt_of_cols {E : Type} [Field E] [NumberField E] {n : ℕ} (gm : Matrix (Fin n) (Fin n) E) (m : ℕ)
    (h : ∀ j : Fin n, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.CongAt m (fun i => gm i j)
      fun i => (((1 : Matrix (Fin n) (Fin n) (𝓞 E)) i j : 𝓞 E) : E)) :
    GlobalTheory.UnRep.CongAt (stdLat E n) m m gm := by
  choose k hk b hb using h
  refine ⟨∏ j, k j, Nat.Coprime.prod_left fun j _ => hk j, fun v hv => ?_⟩
  have hv' : ∀ i, ∃ y : 𝓞 E, (y : E) = v i := fun i => by
    have := (Submodule.mem_pi.1 hv) i (Set.mem_univ _)
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 this
    exact ⟨y, hy⟩
  choose y hy using hv'
  refine ⟨fun i => ((∑ j, ((∏ l ∈ Finset.univ.erase j, k l : ℕ) : 𝓞 E) * b j i * y j : 𝓞 E) : E), ?_, ?_⟩
  · refine Submodule.mem_pi.2 fun i _ => Submodule.mem_one.2 ⟨_, rfl⟩
  · funext i
    have e1 : ∀ j, ((∏ l, k l : ℕ) : E) * (gm i j - (((1 : Matrix (Fin n) (Fin n) (𝓞 E)) i j : 𝓞 E) : E)) =
        ((∏ l ∈ Finset.univ.erase j, k l : ℕ) : E) * ((m : E) * (b j i : E)) := fun j => by
      have hp : (∏ l, k l) = k j * ∏ l ∈ Finset.univ.erase j, k l :=
        (Finset.mul_prod_erase (s := Finset.univ) (f := k) (Finset.mem_univ j)).symm
      rw [hp]
      push_cast
      have h' := hb j i
      simp only at h'
      linear_combination (∏ l ∈ Finset.univ.erase j, ((k l : ℕ) : E)) * h'
    have e2 : (gm.mulVec v - v) i = ∑ j, (gm i j - (((1 : Matrix (Fin n) (Fin n) (𝓞 E)) i j : 𝓞 E) : E)) * v j := by
      simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]
      congr 1
      simp [Matrix.one_apply]
    simp only [Pi.smul_apply, nsmul_eq_mul, e2]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hy j]
    have h' := e1 j
    push_cast at h'
    linear_combination ((y j : 𝓞 E) : E) * h'

theorem plc_prime {K : Type} [Field K] [NumberField K] (lam : HeightOneSpectrum (𝓞 K)) : (Formalism.EigenvalueLevelCeiling.plc lam).Prime := by
  unfold Formalism.EigenvalueLevelCeiling.plc
  haveI : lam.asIdeal.IsPrime := lam.isPrime
  have hne : Ideal.absNorm lam.asIdeal ≠ 0 := fun h => lam.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hz : ((Ideal.absNorm lam.asIdeal : ℕ) : 𝓞 K ⧸ lam.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk lam.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.absNorm_mem _
  have hd : ringChar (𝓞 K ⧸ lam.asIdeal) ∣ Ideal.absNorm lam.asIdeal :=
    (ringChar.spec (𝓞 K ⧸ lam.asIdeal) _).1 hz
  rcases CharP.char_is_prime_or_zero (𝓞 K ⧸ lam.asIdeal) (ringChar (𝓞 K ⧸ lam.asIdeal)) with h | h
  · exact h
  · rw [h, zero_dvd_iff] at hd
    exact absurd hd hne

attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem exists_step_split (D : D7) (T : Full D) (hF : LawsFull T) (j : ℕ) (hj : InR D j) (V : Formalism.BasicNotions.TH.HSp D)
    (hg : V.gram = 1) (hL : Formalism.IndefR.Bridge.hLat V 1 = stdLat D.host.E V.rank) (hev : Even V.rank) (hb : 0 < badN D)
    (p : ℕ) (hp : 0 < p) (Λ : GenLat D.host.E V.rank) (N : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN (T.Q.Dw j) V.rank) T.Q.c.F) (hU : Λ.Unimod)
    (hT : Λ.TrivAt (badN D * (T.dδ j V.rank).l₂.M * p)) (hN : Λ.LevOK N (T.dδ j V.rank).l₂.M)
    (hP : P ∈ harmL T.Q.c Λ a) :
    ∃ (h : Formalism.L2.Theta.GA D V) (Λ' : GenLat D.host.E V.rank) (N' : ℕ)
      (P' : MvPolynomial (LtN (T.Q.Dw j) V.rank) T.Q.c.F) (ζ : T.Q.c.F),
      Formalism.IndefR.FWT.SplitOffBad V (badN D * (T.dδ j V.rank).l₂.M) h ∧
      (∀ w, w ∈ Λ'.La ↔ (fun b => star (w b)) ∈ Formalism.IndefR.Bridge.hLat V (Formalism.IndefR.FWT.fin V h)) ∧
      Λ'.Unimod ∧ Λ'.TrivAt (badN D) ∧ Λ'.TrivAt (T.dδ j V.rank).l₂.M ∧ Λ'.TrivAt p ∧
      Λ'.LevOK N' (T.dδ j V.rank).l₂.M ∧ P' ∈ harmL T.Q.c Λ' a ∧ ζ ≠ 0 ∧ (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧
      ∀ (x0 : Fin V.rank → (T.Q.Dw j).La) (f : Rul (T.Q.Xo j) T.Q.c),
        IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j V.rank) Λ N x0 P f →
        IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j V.rank) Λ' N' x0 P' (ζ • f) := by
  have hM0 : 0 < (T.dδ j V.rank).l₂.M := by have := (T.dδ j V.rank).l₂.three_le; omega
  have hpos : 0 < badN D * p * (T.dδ j V.rank).l₂.M := Nat.mul_pos (Nat.mul_pos hb hp) hM0
  have hT' : Λ.TrivAt (badN D * p * (T.dδ j V.rank).l₂.M) := by
    rwa [show badN D * p * (T.dδ j V.rank).l₂.M = badN D * (T.dδ j V.rank).l₂.M * p by ring]
  obtain ⟨gm, h, hgm, hc, hh, hs, e⟩ := GlobalTheory.T.exists_rationalUnitary_move_selfDual_to_split D V hg hL T.Q.H _ hpos Λ hU hT'
  have h2 : 2 ∣ badN D * p := by
    unfold badN
    exact dvd_mul_of_dvd_left (((((dvd_pow_self 2 (by omega)).trans D.host.tower_dvd : 2 ∣ D.host.QS).mul_right _).mul_right _).mul_right _) p
  obtain ⟨N', c1, c2, c3, c4, -⟩ := GlobalTheory.SplitReps.exists_conjLat V hg hL T.Q.H (T.dδ j V.rank).l₂ (badN D * p) h2 h hs
  rw [← e] at c1 c2 c3 c4
  have hcg := congAt_of_cols gm _ hc
  have hTb : Λ.TrivAt (badN D) := trivAt_of_dvd ⟨(T.dδ j V.rank).l₂.M * p, by ring⟩ hT
  have hTM : Λ.TrivAt (T.dδ j V.rank).l₂.M := trivAt_of_dvd ⟨badN D * p, by ring⟩ hT
  obtain ⟨P', ζ, hP', hζ, hroot, hR⟩ := shortRule_change_mat D T hF j hj V.rank Λ gm _ a P hgm
    (dvd_mul_left _ _) hcg hev hU c1 hTb (trivAt_of_dvd (dvd_mul_right _ _) c2) hTM c3 hP
  have hsp : Formalism.IndefR.FWT.SplitOffBad V (badN D * p * (T.dδ j V.rank).l₂.M) h :=
    GlobalTheory.SplitReps.splitOffBad_of_suppSplit V _ h hh hs
  refine ⟨h, actLat gm Λ, N', P', ζ, ?_, fun w => by rw [e]; rfl, c1, trivAt_of_dvd (dvd_mul_right _ _) c2, c3,
    trivAt_of_dvd (dvd_mul_left _ _) c2, c4, hP', hζ, hroot, fun x0 f hf => hR x0 N N' f hN c4 hf⟩
  obtain ⟨h1, e', Q, h3, h4, h5⟩ := hsp
  refine ⟨h1, e', Q, h3, fun PP hP hbd => h4 PP hP ?_, h5⟩
  rw [show badN D * p * (T.dδ j V.rank).l₂.M = badN D * (T.dδ j V.rank).l₂.M * p by ring, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hbd

attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem star_mem_one (D : D7) {x : D.host.E} (hx : x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) :
    star x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hx
  exact Submodule.mem_one.2 ⟨⟨star (algebraMap _ _ y),
    (RingOfIntegers.isIntegral_coe y).map (starRingEnd D.host.E).toIntAlgHom⟩, rfl⟩

attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem zero_case (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (hL : Formalism.IndefR.Bridge.hLat V 1 = stdLat D.host.E V.rank)
    (Λ : GenLat D.host.E V.rank) (hT : Λ.TrivAt 0) :
    (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Formalism.IndefR.Bridge.hLat V (Formalism.IndefR.FWT.fin V 1)) ∧
      (∀ b, Formalism.IndefR.FWT.SplitOffBad V b 1) ∧ ∀ m, Λ.TrivAt m := by
  obtain ⟨k, hk, h1, h2⟩ := hT
  obtain rfl : k = 1 := (Nat.coprime_zero_right k).1 hk
  simp only [Nat.cast_one, Ideal.span_singleton_one, Submodule.top_smul] at h1 h2
  have hΛ : Λ.La = stdLat D.host.E V.rank := le_antisymm h1 h2
  refine ⟨fun w => ?_, fun b => ?_, fun m => ⟨1, Nat.coprime_one_left m, by simpa using h1, by simpa using h2⟩⟩
  · have hf : Formalism.IndefR.FWT.fin V (1 : Formalism.L2.Theta.GA D V) = 1 := map_one _
    rw [hf, hL, hΛ]
    constructor
    · intro hw
      exact Submodule.mem_pi.2 fun i _ => star_mem_one D ((Submodule.mem_pi.1 hw) i (Set.mem_univ _))
    · intro hw
      refine Submodule.mem_pi.2 fun i _ => ?_
      have := star_mem_one D ((Submodule.mem_pi.1 hw) i (Set.mem_univ _))
      simpa only [star_star] using this
  · refine ⟨one_mem _, 0, ∅, ⟨⟨fun _ => 0, by simp, by simp⟩, by simp⟩, by simp, fun a c => ?_⟩
    have : Formalism.L2.Theta.mt V (1 : Formalism.L2.Theta.GA D V) = 1 := by simp [Formalism.L2.Theta.mt]
    simp [this]

end GlobalTheory.OrbitAdapt
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.OrbitAdapt

section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out Formalism.MainNotions.WeightAlgebra GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence GlobalTheory.ShortMove

theorem exists_step_int (D : D7) (T : Full D) (hF : LawsFull T) (j : ℕ) (hj : InR D j) (n : ℕ) (hev : Even n)
    (hb : 0 < badN D) (Λ : GenLat D.host.E n) (N : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) (hU : Λ.Unimod) (hT : Λ.TrivAt (badN D))
    (hM : Λ.TrivAt (T.dδ j n).l₂.M) (hN : Λ.LevOK N (T.dδ j n).l₂.M) (hP : P ∈ harmL T.Q.c Λ a) (p : ℕ)
    (hp : 0 < p) :
    ∃ (Λ₁ : GenLat D.host.E n) (N₁ : ℕ) (P₁ : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) (ζ : T.Q.c.F),
      Λ₁.Unimod ∧ Λ₁.TrivAt (badN D * (T.dδ j n).l₂.M * p) ∧ Λ₁.LevOK N₁ (T.dδ j n).l₂.M ∧ P₁ ∈ harmL T.Q.c Λ₁ a ∧
      ζ ≠ 0 ∧ (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧
      (∀ (x0 : Fin n → (T.Q.Dw j).La) (f : Rul (T.Q.Xo j) T.Q.c),
        IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j n) Λ N x0 P f →
        IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j n) Λ₁ N₁ x0 P₁ (ζ • f)) := by
  have hBM := GlobalTheory.ShortChange.trivAt_mul hT hM
  have hMpos : 0 < (T.dδ j n).l₂.M := by have := (T.dδ j n).l₂.three_le; omega
  obtain ⟨γ, Λ', hγ, hc, hmove, hU', s, -, -, -, -, k, hk, hk1, hk2⟩ :=
    GlobalTheory.AdaptCongr.exists_move_split D.host.E T.Q.H n _ p Λ (Nat.mul_pos hb hMpos) hp hU hBM
  have h2b : 2 ∣ badN D := by
    unfold badN
    exact ((D.host.two_dvd_QS.mul_right _).mul_right _).mul_right _
  have hg : IsUnitaryM γ.1 := by
    refine Matrix.ext fun i l => ?_
    have := hγ (Pi.single l 1) (Pi.single i 1)
    rw [GlobalTheory.UnRep.Move.hermE_one, GlobalTheory.UnRep.Move.hermE_one] at this
    simp only [Matrix.mulVec_single_one, Matrix.col_apply] at this
    simp only [adjM, Matrix.mul_apply, Matrix.of_apply, this, Matrix.one_apply, Pi.single_apply]
    by_cases h : i = l
    · subst h; simp [apply_ite (IsCMField.complexConj D.host.E)]
    · simp [h, apply_ite (IsCMField.complexConj D.host.E), Ne.symm h]
  have hinv' : ∀ v : Fin n → D.host.E, γ.1 *ᵥ ((γ⁻¹).1 *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  obtain rfl : Λ' = actLat γ.1 Λ := by
    cases Λ' with
    | mk L =>
      simp only [actLat, GenLat.mk.injEq]
      ext v
      constructor
      · intro hv
        exact ⟨_, (hmove _).2 (by rw [hinv']; exact hv), hinv' v⟩
      · rintro ⟨u, hu, rfl⟩
        exact (hmove u).1 hu
  have hkT : ∀ m, m ∣ p * (badN D * (T.dδ j n).l₂.M) → (actLat γ.1 Λ).TrivAt m := fun m hm =>
    ⟨k, hk.coprime_dvd_right hm, hk1, hk2⟩
  have hN₁ : (actLat γ.1 Λ).LevOK ((T.dδ j n).l₂.M * k) (T.dδ j n).l₂.M := by
    refine ⟨?_, dvd_mul_right _ _, ?_⟩
    · exact (T.dδ j n).l₂.odd.mul
        (Nat.coprime_two_right.1 (hk.coprime_dvd_right ((h2b.mul_right _).mul_left _)))
    · show _ ≤ (actLat γ.1 Λ).La ⊓ Formalism.L2.Pj.stdLat D.host.E n
      refine le_inf ((Submodule.smul_mono_left ?_).trans hk2) Submodule.smul_le_right
      refine Ideal.span_singleton_le_span_singleton.2 ?_
      rw [Nat.cast_mul]
      exact dvd_mul_left _ _
  obtain ⟨P₁, ζ, hP₁, hζ, hroot, hR⟩ := shortRule_change_mat D T hF j hj n Λ γ.1 _ a P hg
    (dvd_mul_left _ _) hc hev hU hU' hT (hkT _ ((dvd_mul_right _ _).mul_left _)) hM
    (hkT _ ((dvd_mul_left _ _).mul_left _)) hP
  exact ⟨actLat γ.1 Λ, _, P₁, ζ, hU', hkT _ (by rw [mul_comm]), hN₁, hP₁, hζ, hroot,
    fun x0 f h => hR x0 N _ f hN hN₁ h⟩

theorem exists_step_split_off (D : D7) (T : Full D) (hF : LawsFull T) (j : ℕ) (hj : InR D j) (V : Formalism.BasicNotions.TH.HSp D)
    (hg : V.gram = 1) (hL : Formalism.IndefR.Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank) (hev : Even V.rank) (hb : 0 < badN D)
    (p : ℕ) (hp : 0 < p) (Λ : GenLat D.host.E V.rank) (N : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN (T.Q.Dw j) V.rank) T.Q.c.F) (hU : Λ.Unimod)
    (hT : Λ.TrivAt (badN D * (T.dδ j V.rank).l₂.M * p)) (hN : Λ.LevOK N (T.dδ j V.rank).l₂.M)
    (hP : P ∈ harmL T.Q.c Λ a) :
    ∃ (h : Formalism.L2.Theta.GA D V) (Λ' : GenLat D.host.E V.rank) (N' : ℕ)
      (P' : MvPolynomial (LtN (T.Q.Dw j) V.rank) T.Q.c.F) (ζ : T.Q.c.F),
      Formalism.IndefR.FWT.SplitOffBad V (badN D * (T.dδ j V.rank).l₂.M * p) h ∧
      (∀ w, w ∈ Λ'.La ↔ (fun b => star (w b)) ∈ Formalism.IndefR.Bridge.hLat V (Formalism.IndefR.FWT.fin V h)) ∧
      Λ'.Unimod ∧ Λ'.TrivAt (badN D) ∧ Λ'.TrivAt (T.dδ j V.rank).l₂.M ∧ Λ'.TrivAt p ∧
      Λ'.LevOK N' (T.dδ j V.rank).l₂.M ∧ P' ∈ harmL T.Q.c Λ' a ∧ ζ ≠ 0 ∧ (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧
      ∀ (x0 : Fin V.rank → (T.Q.Dw j).La) (f : Rul (T.Q.Xo j) T.Q.c),
        IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j V.rank) Λ N x0 P f →
        IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j V.rank) Λ' N' x0 P' (ζ • f) := by
  have hM0 : 0 < (T.dδ j V.rank).l₂.M := by have := (T.dδ j V.rank).l₂.three_le; omega
  have hpos : 0 < badN D * p * (T.dδ j V.rank).l₂.M := Nat.mul_pos (Nat.mul_pos hb hp) hM0
  have hT' : Λ.TrivAt (badN D * p * (T.dδ j V.rank).l₂.M) := by
    rwa [show badN D * p * (T.dδ j V.rank).l₂.M = badN D * (T.dδ j V.rank).l₂.M * p by ring]
  obtain ⟨gm, h, hgm, hc, hh, hs, e⟩ := GlobalTheory.T.exists_rationalUnitary_move_selfDual_to_split D V hg hL T.Q.H _ hpos Λ hU hT'
  have h2 : 2 ∣ badN D * p := by
    unfold badN
    exact dvd_mul_of_dvd_left (((D.host.two_dvd_QS.mul_right _).mul_right _).mul_right _) p
  obtain ⟨N', c1, c2, c3, c4, -⟩ := GlobalTheory.SplitReps.exists_conjLat V hg hL T.Q.H (T.dδ j V.rank).l₂ (badN D * p) h2 h hs
  rw [← e] at c1 c2 c3 c4
  have hcg := congAt_of_cols gm _ hc
  have hTb : Λ.TrivAt (badN D) := trivAt_of_dvd ⟨(T.dδ j V.rank).l₂.M * p, by ring⟩ hT
  have hTM : Λ.TrivAt (T.dδ j V.rank).l₂.M := trivAt_of_dvd ⟨badN D * p, by ring⟩ hT
  obtain ⟨P', ζ, hP', hζ, hroot, hR⟩ := shortRule_change_mat D T hF j hj V.rank Λ gm _ a P hgm
    (dvd_mul_left _ _) hcg hev hU c1 hTb (trivAt_of_dvd (dvd_mul_right _ _) c2) hTM c3 hP
  have hsp : Formalism.IndefR.FWT.SplitOffBad V (badN D * p * (T.dδ j V.rank).l₂.M) h :=
    GlobalTheory.SplitReps.splitOffBad_of_suppSplit V _ h hh hs
  refine ⟨h, actLat gm Λ, N', P', ζ, ?_, fun w => by rw [e]; rfl, c1, trivAt_of_dvd (dvd_mul_right _ _) c2, c3,
    trivAt_of_dvd (dvd_mul_left _ _) c2, c4, hP', hζ, hroot, fun x0 f hf => hR x0 N N' f hN c4 hf⟩
  rwa [show badN D * (T.dδ j V.rank).l₂.M * p = badN D * p * (T.dδ j V.rank).l₂.M by ring]

theorem splitOffBad_of_dvd (D : D7) (V : Formalism.BasicNotions.TH.HSp D) {a b : ℕ} (hab : a ∣ b) {h : Formalism.L2.Theta.GA D V}
    (hs : Formalism.IndefR.FWT.SplitOffBad V b h) : Formalism.IndefR.FWT.SplitOffBad V a h := by
  obtain ⟨h1, e', Q, h3, h4, h5⟩ := hs
  obtain ⟨c, rfl⟩ := hab
  refine ⟨h1, e', Q, h3, fun PP hP hbd => h4 PP hP ?_, h5⟩
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hbd

end

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence GlobalTheory.ShortMove in
set_option maxHeartbeats 1000000 in

theorem exists_adapted : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)) (U : Subgroup G) (lam : HeightOneSpectrum (𝓞 D.what₂.LL)) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)), IsOrbitFamily (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (badN D) (wtA (κ i)) (T.dδ ((i : ℕ) + 1) (κ i).n) (fun u : U => ℓ u) (fun u => ((f u).1 : T.R ((i : ℕ) + 1))) → ∃ (a : 𝓞 T.Q.c.F) (s : ℕ) (f' : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La), (s : 𝓞 D.what₂.LL) ∉ lam.asIdeal ∧ (∀ u, (s : T.Q.c.F) • ((f u).1 : T.R ((i : ℕ) + 1)) = (a : T.Q.c.F) • ((f' u).1 : T.R ((i : ℕ) + 1))) ∧ SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h ∧ (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) ∧ Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) ∧ Λ.Unimod ∧ Λ.TrivAt (badN D) ∧ Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M ∧ Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M ∧ AdmX (l := T.Q.l) true x₀ ∧ P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) ∧ ∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f' u).1 : T.R ((i : ℕ) + 1)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hk i hO ℓ U lam f hf
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hrk : (Vc D i).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hn : (κ i).n = (Vc D i).rank := (fw.kap i (D.eTau.symm 1)).2.2.trans hrk.symm
  have hr : Odd D.R.r := by
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    have h2 := D.R.two_le_m
    exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩
  have hev : Even (Vc D i).rank := hrk ▸ hr.add_odd D.R.t_odd
  have hV := hO.2.lift.std
  have hg : (Vc D i).gram = 1 := hV.1
  have hL : Bridge.hLat (Vc D i) 1 = Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank := hV.2
  rw [hn] at hf
  obtain ⟨Λ, N, x₀, P, x, hU, hTb, hTM, hN, hA, hP, hx⟩ := hf
  have hp := plc_prime lam
  have hq : 0 < Formalism.EigenvalueLevelCeiling.plc lam * (O i).bad () := Nat.mul_pos hp.pos (hO.2.bad ()).1
  obtain ⟨h, Λ', N', P', ζ, hs, hmem, hU', hTb', hTM', hTp, hN', hP', hζ, ⟨m, hm, hζm⟩, hR⟩ :
      ∃ (h : GA D (Vc D i)) (Λ' : GenLat D.host.E (Vc D i).rank) (N' : ℕ)
        (P' : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (ζ : T.Q.c.F),
        SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h ∧
        (∀ w, w ∈ Λ'.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) ∧
        Λ'.Unimod ∧ Λ'.TrivAt (badN D) ∧ Λ'.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M ∧
        Λ'.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) ∧ Λ'.LevOK N' (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M ∧
        P' ∈ harmL T.Q.c Λ' (wtA (κ i)) ∧ ζ ≠ 0 ∧ (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧
        ∀ (x0 : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (g : Rul (T.Q.Xo ((i : ℕ) + 1)) T.Q.c),
          IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N x0 P g →
          IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ' N' x0 P' (ζ • g) := by
    rcases Nat.eq_zero_or_pos (badN D) with hb | hb
    · rw [hb] at hTb
      obtain ⟨h1, h2, h3⟩ := zero_case D (Vc D i) hL Λ hTb
      exact ⟨1, Λ, N, P, 1, h2 _, h1, hU, h3 _, h3 _, h3 _, hN, hP, one_ne_zero, ⟨1, one_pos, one_pow _⟩,
        fun x0 g hg => by rwa [one_smul]⟩
    · obtain ⟨Λ₁, N₁, P₁, ζ₁, hU₁, hT₁, hN₁, hP₁, hζ₁, ⟨m₁, hm₁, e₁⟩, hR₁⟩ :=
        exists_step_int D T hT ((i : ℕ) + 1) hj _ hev hb Λ N (wtA (κ i)) P hU hTb hTM hN hP _ hq
      obtain ⟨h, Λ', N', P', ζ₂, d1, d2, d3, d4, d5, d6, d7, d8, hζ₂, ⟨m₂, hm₂, e₂⟩, hR₂⟩ :=
        exists_step_split_off D T hT _ hj (Vc D i) hg hL hev hb _ hq Λ₁ N₁ _ P₁ hU₁ hT₁ hN₁ hP₁
      refine ⟨h, Λ', N', P', ζ₂ * ζ₁, splitOffBad_of_dvd D _ ⟨Formalism.EigenvalueLevelCeiling.plc lam, by ring⟩ d1, d2, d3, d4, d5,
        trivAt_of_dvd (dvd_mul_right _ _) d6, d7, d8, mul_ne_zero hζ₂ hζ₁,
        ⟨m₁ * m₂, Nat.mul_pos hm₁ hm₂, by rw [mul_pow, pow_mul' ζ₂, e₂, pow_mul ζ₁, e₁, one_pow, one_pow, one_mul]⟩,
        fun x0 g hg => ?_⟩
      rw [mul_smul]
      exact hR₂ x0 _ (hR₁ x0 g hg)
  have hint : IsIntegral ℤ (ζ ^ (m - 1)) :=
    IsIntegral.pow (IsIntegral.of_pow hm (by rw [hζm]; exact isIntegral_one)) _
  have hinv : ζ ^ (m - 1) * ζ = 1 := by rw [← pow_succ, Nat.sub_add_cancel hm, hζm]
  refine ⟨⟨ζ ^ (m - 1), hint⟩, 1, fun u => ⟨ζ • (f u).1, Submodule.smul_mem _ ζ (f u).2⟩, Λ', h, N', x₀, P', x,
    ?_, fun u => ?_, hs, hmem, hTp, hU', hTb', hTM', hN', hA, hP', fun u => ⟨(hx u).1, (hx u).2.1, hR _ _ (hx u).2.2⟩⟩
  · rw [Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).1 lam.isPrime.ne_top
  · show ((1 : ℕ) : T.Q.c.F) • ((f u).1 : T.R ((i : ℕ) + 1)) = (ζ ^ (m - 1)) • (ζ • ((f u).1 : T.R ((i : ℕ) + 1)))
    rw [Nat.cast_one, one_smul, smul_smul, hinv, one_smul]

end GlobalTheory.OrbitAdapt
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orbit_family_adapted_lattice_split_support : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)) (U : Subgroup G) (lam : HeightOneSpectrum (𝓞 D.what₂.LL)) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)), IsOrbitFamily (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (badN D) (wtA (κ i)) (T.dδ ((i : ℕ) + 1) (κ i).n) (fun u : U => ℓ u) (fun u => ((f u).1 : T.R ((i : ℕ) + 1))) → ∃ (a : 𝓞 T.Q.c.F) (s : ℕ) (f' : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La), (s : 𝓞 D.what₂.LL) ∉ lam.asIdeal ∧ (∀ u, (s : T.Q.c.F) • ((f u).1 : T.R ((i : ℕ) + 1)) = (a : T.Q.c.F) • ((f' u).1 : T.R ((i : ℕ) + 1))) ∧ SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h ∧ (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) ∧ Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) ∧ Λ.Unimod ∧ Λ.TrivAt (badN D) ∧ Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M ∧ Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M ∧ AdmX (l := T.Q.l) true x₀ ∧ P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) ∧ ∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f' u).1 : T.R ((i : ℕ) + 1)) := by
  atlas_forward_decl GlobalTheory.OrbitAdapt.exists_adapted
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

namespace GlobalTheory.HarmInCoef

open NumberField IsDedekindDomain Formalism.L2.DIV

theorem exists_nat_smul_mem_nabAtr {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} [Fintype ι]
    {n : ℕ} (emb : ι → E →+* K) (lam : ι → DomWeight n) {L L' : Submodule (𝓞 E) (Fin n → E)}
    (hL : Submodule.IsLattice E L) (hL' : Submodule.IsLattice E L') {a : ℕ} (h : ∀ x ∈ L, a • x ∈ L')
    (h' : ∀ x ∈ L', a • x ∈ L) (w₀ : HeightOneSpectrum (𝓞 K)) (ha : a.Coprime (ringChar (𝓞 K ⧸ w₀.asIdeal)))
    {x : VV K lam} (hx : x ∈ nabAtr emb lam L) :
    ∃ s : ℕ, (s : 𝓞 K) ∉ w₀.asIdeal ∧ s • x ∈ nabAtr emb lam L' := by
  classical
  have hp : (ringChar (𝓞 K ⧸ w₀.asIdeal)).Prime := by
    haveI := w₀.isMaximal
    haveI : Finite (𝓞 K ⧸ w₀.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w₀.ne_bot
    letI := Ideal.Quotient.field w₀.asIdeal
    exact CharP.prime_ringChar _
  set p := ringChar (𝓞 K ⧸ w₀.asIdeal) with hpdef
  have hpw : ((p : ℕ) : 𝓞 K) ∈ w₀.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact (ringChar.spec _ _).2 dvd_rfl
  let J : Ideal (𝓞 K) := (nabAtr emb lam L').comap (LinearMap.toSpanSingleton (𝓞 K) _ x)
  have hmemJ : ∀ r : 𝓞 K, r ∈ J ↔ r • x ∈ nabAtr emb lam L' := fun r => Iff.rfl
  have hJw : ∀ w : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ w.asIdeal → ¬ J ≤ w.asIdeal := by
    intro w hw hle
    have hcong := (GlobalTheory.GO.localization_nabAtr_delAtr_congr emb lam hL hL' h h' w
      (GlobalTheory.GO.natCast_notMem_of_coprime ha w hw)).1
    have hx0 : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabAtr emb lam L) :=
      ⟨1, fun h1 => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), by simpa using hx⟩
    have hx' : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabAtr emb lam L') := hcong ▸ hx0
    obtain ⟨u, hu, hux⟩ := hx'
    exact hu (hle ((hmemJ u).2 hux))
  have hp0 : ((p : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hJp : J ⊔ Ideal.span {((p : ℕ) : 𝓞 K)} = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hpm : ((p : ℕ) : 𝓞 K) ∈ m := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hm0 : m ≠ ⊥ := fun h0 => hp0 (by rw [h0] at hpm; exact (Submodule.mem_bot _).1 hpm)
    exact hJw ⟨m, hm.isPrime, hm0⟩ hpm (le_sup_left.trans hle)
  have hJ0 : J ≠ ⊥ := fun h0 => hJw w₀ hpw (h0 ▸ bot_le)
  refine ⟨Ideal.absNorm J, ?_, ?_⟩
  · intro hmem
    have hdvd : p ∣ Ideal.absNorm J := by
      refine (ringChar.spec (𝓞 K ⧸ w₀.asIdeal) _).1 ?_
      rw [← map_natCast (Ideal.Quotient.mk w₀.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
      exact hmem
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Finite (𝓞 K ⧸ J) := Ideal.finiteQuotientOfFreeOfNeBot J hJ0
    obtain ⟨z, hz⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 K ⧸ J) p
      (by rwa [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply])
    have h1mem : (1 : 𝓞 K) ∈ J ⊔ Ideal.span {((p : ℕ) : 𝓞 K)} := hJp ▸ Submodule.mem_top
    obtain ⟨j, hj, y, hy, hjy⟩ := Submodule.mem_sup.1 h1mem
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    have h1 : Ideal.Quotient.mk J (c * (p : 𝓞 K)) = 1 := by
      rw [← map_one (Ideal.Quotient.mk J), ← hjy, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hj, zero_add]
    have hpz : p • z = 0 := hz ▸ addOrderOf_nsmul_eq_zero z
    have hz0 : z = 0 := by
      calc z = Ideal.Quotient.mk J (c * (p : 𝓞 K)) * z := by rw [h1, one_mul]
        _ = Ideal.Quotient.mk J c * (p • z) := by rw [map_mul, nsmul_eq_mul, map_natCast]; ring
        _ = 0 := by rw [hpz, mul_zero]
    rw [hz0, addOrderOf_zero] at hz
    exact hp.one_lt.ne hz
  · rw [← Nat.cast_smul_eq_nsmul (𝓞 K)]
    exact (hmemJ _).1 (Ideal.absNorm_mem J)

end GlobalTheory.HarmInCoef

namespace GlobalTheory.HarmInCoef

open NumberField MvPolynomial Formalism.L2.Pj

theorem coeff_aeval_scale {σ K : Type} [Field K] (t : K) (P : MvPolynomial σ K) (m : σ →₀ ℕ) :
    (aeval (fun i => C t * X i) P).coeff m = t ^ (m.sum fun _ e => e) * P.coeff m := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d a =>
    have e : aeval (fun i => C t * X i) (monomial d a) = monomial d (t ^ (d.sum fun _ e => e) * a) := by
      rw [aeval_monomial, monomial_eq]
      simp only [Algebra.algebraMap_self, RingHom.id_apply, mul_pow, Finsupp.prod_mul, Finsupp.prod, Finsupp.sum,
        Finset.prod_pow_eq_pow_sum, C_mul, C_pow, algebraMap_eq]
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      ring
    rw [e, coeff_monomial, coeff_monomial]
    by_cases h : d = m
    · subst h; simp
    · simp [h]
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (c : Coeff l)

theorem symO_std_le {n : ℕ} :
    symO (Dw := Dw) c (⟨Formalism.L2.Pj.stdLat E n⟩ : GenLat E n) ≤
      (MvPolynomial.map (algebraMap (integralClosure ℤ c.F) c.F)).range := by
  refine (Subring.closure_le).2 ?_
  rintro f (⟨o, rfl⟩ | ⟨σ, i, b, hb, rfl⟩)
  · exact ⟨C o, by simp⟩
  · have hb' : ∀ j, ∃ y : 𝓞 E, algebraMap (𝓞 E) E y = b j := fun j => by
      have := (Submodule.mem_pi.1 hb) j (Set.mem_univ _)
      exact Submodule.mem_one.1 this
    choose y hy using hb'
    have hint : ∀ j, IsIntegral ℤ (embF c σ (b j)) := fun j => by
      rw [← hy j]
      exact (RingOfIntegers.isIntegral_coe (y j)).map (embF c σ).toIntAlgHom
    refine ⟨∑ j, C (⟨embF c σ (b j), (mem_integralClosure_iff ℤ c.F).2 (hint j)⟩ : integralClosure ℤ c.F) *
      X (⟨σ, i, j⟩ : LtN Dw n), ?_⟩
    simp [letB]

theorem scale_mem_symO {n : ℕ} (Λ : GenLat E n) (k : ℕ) (hk : ∀ b ∈ Λ.La, (k : 𝓞 E) • b ∈ Formalism.L2.Pj.stdLat E n)
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ symO c Λ) :
    aeval (fun i => C (k : c.F) * X i) P ∈ symO c (⟨Formalism.L2.Pj.stdLat E n⟩ : GenLat E n) := by
  let φ : MvPolynomial (LtN Dw n) c.F →+* MvPolynomial (LtN Dw n) c.F :=
    (aeval (fun i => C (k : c.F) * X i) : MvPolynomial (LtN Dw n) c.F →ₐ[c.F] _).toRingHom
  have hle : symO c Λ ≤ (symO c (⟨Formalism.L2.Pj.stdLat E n⟩ : GenLat E n)).comap φ := by
    refine (Subring.closure_le).2 ?_
    rintro f (⟨o, rfl⟩ | ⟨σ, i, b, hb, rfl⟩)
    · refine Subring.subset_closure (Or.inl ⟨o, ?_⟩)
      simp [φ]
    · refine Subring.subset_closure (Or.inr ⟨σ, i, (k : 𝓞 E) • b, hk b hb, ?_⟩)
      simp only [φ, letB, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_mul, aeval_C, aeval_X,
        algebraMap_eq, Pi.smul_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← mul_assoc, ← C_mul]
      congr 2
      rw [Algebra.smul_def, map_mul, map_natCast, map_natCast, mul_comm]
  exact hle hP

theorem exists_pow_mul_coeff_integral {n : ℕ} (Λ : GenLat E n) (k : ℕ) (hk : ∀ b ∈ Λ.La, (k : 𝓞 E) • b ∈ Formalism.L2.Pj.stdLat E n)
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ symO c Λ) :
    ∃ D : ℕ, ∀ m, IsIntegral ℤ ((k : c.F) ^ D * P.coeff m) := by
  refine ⟨P.totalDegree, fun m => ?_⟩
  by_cases hm : m ∈ P.support
  · obtain ⟨Q, hQ⟩ := symO_std_le c (scale_mem_symO c Λ k hk hP)
    have h1 : IsIntegral ℤ ((k : c.F) ^ (m.sum fun _ e => e) * P.coeff m) := by
      rw [← coeff_aeval_scale, ← hQ, coeff_map]
      exact (mem_integralClosure_iff ℤ c.F).1 (Q.coeff m).2
    have h2 : (m.sum fun _ e => e) ≤ P.totalDegree := le_totalDegree hm
    rw [← Nat.sub_add_cancel h2, pow_add, mul_assoc]
    have hk' : IsIntegral ℤ (k : c.F) := by
      simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ c.F (k : ℤ)))
    exact (hk'.pow _).mul h1
  · rw [notMem_support_iff.1 hm, mul_zero]
    exact isIntegral_zero

end GlobalTheory.HarmInCoef

namespace GlobalTheory.HarmInCoef

open MvPolynomial Formalism.L2.Pj

theorem smul_mem_HHa {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k] {cc : T → T} {isX : T → Prop} {a : T → ℕ → ℕ}
    {P : MvPolynomial (Letter T r n) k} (hP : P ∈ HHa r n k cc isX a) (t : k) : t • P ∈ HHa r n k cc isX a :=
  ⟨Submodule.smul_mem _ t hP.1, fun σ i i' h s => by rw [map_smul, hP.2.1 σ i i' h s],
    fun m hm σ i => hP.2.2 m (MvPolynomial.support_smul hm) σ i⟩

theorem map_mem_HHa {T : Type} {r : T → ℕ} {n : ℕ} {k K : Type} [Field k] [CharZero k] [Field K] (f : k →+* K)
    {cc : T → T} {isX : T → Prop} {a : T → ℕ → ℕ} {P : MvPolynomial (Letter T r n) k} (hP : P ∈ HHa r n k cc isX a) :
    MvPolynomial.map f P ∈ HHa r n K cc isX a :=
  ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.harmK_map f hP.1, GlobalTheory.RowSpan.rowInv_map f hP.2.1,
    fun m hm => hP.2.2 m (MvPolynomial.support_map_subset f P hm)⟩

theorem coeff_smul_map_mem {σ k K : Type} [Field k] [Field K] (f : k →+* K) (t : k) (P : MvPolynomial σ k) (m : σ →₀ ℕ)
    (h : IsIntegral ℤ (t * P.coeff m)) :
    (f t • MvPolynomial.map f P).coeff m ∈ (integralClosure ℤ K).toSubring := by
  rw [coeff_smul, coeff_map, smul_eq_mul, ← map_mul]
  exact Subalgebra.mem_toSubring.2 ((mem_integralClosure_iff ℤ _).2 (h.map f.toIntAlgHom))

end GlobalTheory.HarmInCoef

namespace GlobalTheory.HarmInCoef

open NumberField IsDedekindDomain MvPolynomial Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR.FWT

set_option maxHeartbeats 1000000 in

theorem harm_mem_coefLat : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (lam : HeightOneSpectrum (𝓞 D.what₂.LL)), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∀ P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)), ∃ (y : VsV D i (O i).c'.F) (s : ℕ), (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P ∧ (s : 𝓞 D.what₂.LL) ∉ lam.asIdeal ∧ InCoefLat R i h ((s : ℂ) • (O i).c0' y) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT _hk i hpins Λ h _hsplit hLa lam htriv P hP

  obtain ⟨hfield, hP'⟩ := hpins
  obtain ⟨k, hkcop, hk1, hk2⟩ := htriv
  have hlift := hP'.lift
  obtain ⟨gramR, c0R, c0L, hFT, hC0⟩ := hlift.c0
  have hfld : (inC (O i).c').comp (O i).jL = D.what₂.embLL := hlift.field
  obtain ⟨_, cga, hIo⟩ := hP'.io
  have hsub := hIo.2.2.2.2.2.2.2

  have hp : (Formalism.EigenvalueLevelCeiling.plc lam).Prime := by
    haveI := lam.isMaximal
    haveI : Finite (𝓞 D.what₂.LL ⧸ lam.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ lam.ne_bot
    letI := Ideal.Quotient.field lam.asIdeal
    exact CharP.prime_ringChar _
  have hplam : ((Formalism.EigenvalueLevelCeiling.plc lam : ℕ) : 𝓞 D.what₂.LL) ∈ lam.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact (ringChar.spec _ _).2 dvd_rfl
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hp.one_lt.ne' (Nat.coprime_zero_left _ |>.1 hkcop)
  have hklam : ((k : ℕ) : 𝓞 D.what₂.LL) ∉ lam.asIdeal := GlobalTheory.GO.natCast_notMem_of_coprime hkcop lam hplam

  have hkΛ : ∀ b ∈ Λ.La, (k : 𝓞 D.host.E) • b ∈ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank := fun b hb =>
    hk1 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hb)
  obtain ⟨Dg, hDg⟩ := exists_pow_mul_coeff_integral _ Λ k hkΛ hP.2

  set f := incF T.J.toCore.Q.c (O i).c' (O i).hle with hf
  have hQ : f ((k : T.Q.c.F) ^ Dg) • MvPolynomial.map f P ∈ harmA (Dw := T.J.toCore.Q.Dw ((i : ℕ) + 1)) (O i).c'
      (wtA (κ i)) (Vc D i).rank :=
    ⟨smul_mem_HHa (map_mem_HHa f hP.1) _, fun m => coeff_smul_map_mem f _ P m (hDg m)⟩
  obtain ⟨y0, hy0, hy0io⟩ := hsub hQ

  have hsurj : Function.Surjective (O i).jL := by
    intro z
    have hz : (z : ℂ) ∈ D.what₂.embLL.toRatAlgHom.fieldRange := hfield ▸ z.2
    obtain ⟨a, ha⟩ := AlgHom.mem_fieldRange.1 hz
    refine ⟨a, Subtype.ext ?_⟩
    exact (RingHom.congr_fun hfld a).trans ha
  let e : D.what₂.LL ≃+* (O i).c'.F := RingEquiv.ofBijective (O i).jL ⟨(O i).jL.injective, hsurj⟩
  have hje : (O i).jL.comp (e.symm : (O i).c'.F →+* D.what₂.LL) = RingHom.id _ := by
    refine RingHom.ext fun z => ?_
    exact e.apply_symm_apply z
  let F0 : Pol D.what₂.LL D.what₂.Tau (Vc D i).rank := MvPolynomial.map (e.symm : (O i).c'.F →+* D.what₂.LL) (y0 : Pol _ _ _)
  have hF0 : MvPolynomial.map (O i).jL F0 = (y0 : Pol _ _ _) := by
    rw [MvPolynomial.map_map, hje, MvPolynomial.map_id]
  have hx0V : F0 ∈ VV D.what₂.LL (lamV D i) :=
    ((Formalism.L2.DIV.baseChangeSpace_holds D.what₂.LL (O i).c'.F (O i).jL D.what₂.Tau (Vc D i).rank (lamV D i)).1 F0).2
      (hF0 ▸ y0.2)
  let x0 : VsV D i D.what₂.LL := ⟨F0, hx0V⟩

  have hstd : Submodule.IsLattice D.host.E (Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank) := by
    have := GlobalTheory.RepsCompare.isLattice_hLat (Vc D i) 1
    rw [hlift.std.2] at this
    exact this
  have hemb : (fun τ => (O i).jL.comp (labLL D τ)) = fun τ => embF (O i).c' (tauE D τ) :=
    funext fun τ => embV_eq_embF (O i).c' (O i).jL hfld τ
  have hx0nab : x0 ∈ nabAtr (labLL D) (lamV D i) (Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank) := by
    refine ((Formalism.L2.DIV.nablaDeltaDescentAt_holds D.host.E D.what₂.LL (O i).c'.F (O i).jL D.what₂.Tau (Vc D i).rank
      (labLL D) (lamV D i) _ hstd x0 y0 hF0.symm).2.2.1).2 ?_
    rw [hemb]
    exact hy0

  have hstarStd : ∀ x ∈ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank,
      (fun b => star (x b)) ∈ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank := by
    intro x hx
    refine Submodule.mem_pi.2 fun j _ => ?_
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 ((Submodule.mem_pi.1 hx) j (Set.mem_univ _))
    have hint : IsIntegral ℤ (star (x j)) := by
      rw [← hy]
      exact (RingOfIntegers.isIntegral_coe y).map (starRingEnd D.host.E).toIntAlgHom
    exact Submodule.mem_one.2 ⟨⟨star (x j), (mem_integralClosure_iff ℤ _).2 hint⟩, rfl⟩
  have hcmp1 : ∀ x ∈ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank, k • x ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h) := by
    intro x hx
    have h2 : (k : 𝓞 D.host.E) • (fun b => star (x b)) ∈ Λ.La :=
      hk2 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (hstarStd x hx))
    have h3 := (hLa _).1 h2
    convert h3 using 1
    funext b
    simp [Algebra.smul_def, star_mul', star_natCast]
  have hcmp2 : ∀ x ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h), k • x ∈ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank := by
    intro x hx
    have h1 : (fun b => star (x b)) ∈ Λ.La := (hLa _).2 (by simpa using hx)
    have h2 : (k : 𝓞 D.host.E) • (fun b => star (x b)) ∈ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank :=
      hk1 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) h1)
    have h3 := hstarStd _ h2
    convert h3 using 1
    funext b
    simp [Algebra.smul_def, star_mul', star_natCast]
  obtain ⟨s, hs, hsx⟩ := exists_nat_smul_mem_nabAtr (labLL D) (lamV D i) hstd
    (GlobalTheory.RepsCompare.isLattice_hLat (Vc D i) (fin (Vc D i) h)) hcmp1 hcmp2 lam hkcop hx0nab

  obtain ⟨v', hv'pol, hv'c⟩ := hC0 (s • x0)
  have hv'eq : v' = s • y0 := by
    apply Subtype.ext
    rw [hv'pol]
    show MvPolynomial.map (O i).jL (s • F0) = s • (y0 : Pol _ _ _)
    rw [map_nsmul, hF0]
  set r : (O i).c'.F := f ((k : T.Q.c.F) ^ Dg) with hrdef
  have hr : r = (k : (O i).c'.F) ^ Dg := by rw [hrdef]; erw [map_pow, map_natCast]
  have hr0 : r ≠ 0 := by rw [hr]; exact pow_ne_zero _ (Nat.cast_ne_zero.2 hk0)
  refine ⟨r⁻¹ • y0, s * k ^ Dg, ?_, ?_, ?_⟩
  · rw [map_smul, hy0io]
    exact inv_smul_smul₀ hr0 _
  · push_cast
    intro hm
    rcases lam.isPrime.mem_or_mem hm with h1 | h1
    · exact hs h1
    · exact hklam (lam.isPrime.mem_of_pow_mem _ h1)
  · refine ⟨gramR, c0R, c0L, hFT, s • x0, hsx, ?_⟩
    have hsm : (s * k ^ Dg) • (r⁻¹ • y0) = s • y0 := by
      rw [← Nat.cast_smul_eq_nsmul (O i).c'.F, ← Nat.cast_smul_eq_nsmul (O i).c'.F s, smul_smul, Nat.cast_mul,
        Nat.cast_pow, ← hr, mul_assoc, mul_inv_cancel₀ hr0, mul_one]
    refine Eq.trans ?_ hv'c
    rw [hv'eq, ← hsm, map_nsmul, Nat.cast_smul_eq_nsmul]

end GlobalTheory.HarmInCoef
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freeLowerBlockVector_multiple_kernelTranslate : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → ∀ (p : ℕ), (∀ PP ∈ Q, (p : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ x, ((ξ.1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → Formalism.L2.Host.ValLL0 D R.C → ∃ φ₁, VecOf R i Q (omegaFree R i Q ξR (fun PP : Pl D.host.E => Matrix.of fun (a : Fin (Vc D i).rank) (b : Fin (Wc D i).rank) => if (a : ℕ) = (b : ℕ) then (1 : kP PP) else 0)) φ₁ ∧ ∃ k ∈ GfC (Vc D i), ∃ (c : D.what₂.LL) (m : ℕ), φ₁ = D.what₂.embLL c • ω (k, 1) φ ∧ IsIntegral ℤ ((p : D.what₂.LL) ^ m * c) ∧ IsIntegral ℤ ((p : D.what₂.LL) ^ m * c⁻¹) ∧ c ≠ 0 ∧ ∀ h ∈ GfC (Vc D i), ∀ w, InCoefLat R i h w → InCoefLat R i (h * k) (((p : ℂ) ^ m) • w) := by
  first | exact @GlobalTheory.FreeBlockTwist.vecFree_base_translate | exact GlobalTheory.FreeBlockTwist.vecFree_base_translate | (intros; apply GlobalTheory.FreeBlockTwist.vecFree_base_translate <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePlaces_datum_move_to_fullRank : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → ∀ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) → ∀ φ₁, VecOf R i Q (omegaFree R i Q ξR (fun PP : Pl D.host.E => Matrix.of fun (a : Fin (Vc D i).rank) (b : Fin (Wc D i).rank) => if (a : ℕ) = (b : ℕ) then (1 : kP PP) else 0)) φ₁ → ∃ φ', VecOf R i Q (omegaFree R i Q ξR y₀) φ' ∧ ∃ k ∈ GfC (Vc D i), ∃ c : D.what₂.LL, φ' = D.what₂.embLL c • ω (k, 1) φ₁ ∧ IsIntegral ℤ c ∧ IsIntegral ℤ c⁻¹ ∧ c ≠ 0 ∧ ∀ h ∈ GfC (Vc D i), ∀ w, InCoefLat R i h w → InCoefLat R i (h * k) w := by
  first | exact @GlobalTheory.TypeMove.vecFree_typeMove | exact GlobalTheory.TypeMove.vecFree_typeMove | (intros; apply GlobalTheory.TypeMove.vecFree_typeMove <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

namespace GlobalTheory.FreeBlockMove

theorem vecFree_translate : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → ∀ (p : ℕ), (∀ PP ∈ Q, (p : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ x, ((ξ.1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → Formalism.L2.Host.ValLL0 D R.C → ∀ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) → ∃ φ', VecOf R i Q (omegaFree R i Q ξR y₀) φ' ∧ ∃ k ∈ GfC (Vc D i), ∃ (c : D.what₂.LL) (m : ℕ), φ' = D.what₂.embLL c • ω (k, 1) φ ∧ IsIntegral ℤ ((p : D.what₂.LL) ^ m * c) ∧ IsIntegral ℤ ((p : D.what₂.LL) ^ m * c⁻¹) ∧ c ≠ 0 ∧ ∀ h ∈ GfC (Vc D i), ∀ w, InCoefLat R i h w → InCoefLat R i (h * k) (((p : ℂ) ^ m) • w) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i ξ χ ξR Q ω φ hK p hp hξ hV y₀ hy₀
  obtain ⟨φ₁, hφ₁, k₁, hk₁, c₁, m, e₁, i₁, i₁', c₁0, L₁⟩ := GlobalTheory.T.freeLowerBlockVector_multiple_kernelTranslate D G Pl0 T0 A Ks R F hC i ξ χ ξR Q ω φ hK p hp hξ hV
  obtain ⟨φ', hφ', k₂, hk₂, c₂, e₂, i₂, i₂', c₂0, L₂⟩ := GlobalTheory.T.typePlaces_datum_move_to_fullRank D G Pl0 T0 A Ks R F hC i ξ χ ξR Q ω φ hK y₀ hy₀ φ₁ hφ₁
  refine ⟨φ', hφ', k₂ * k₁, mul_mem hk₂ hk₁, c₂ * c₁, m, ?_, ?_, ?_, mul_ne_zero c₂0 c₁0, ?_⟩
  · have hm : ((k₂ * k₁, (1 : GA D (Wc D i))) : GA D (Vc D i) × GA D (Wc D i)) = (k₂, 1) * (k₁, 1) := by
      simp
    rw [e₂, e₁, hm, map_mul ω, Module.End.mul_apply, map_smul, smul_smul, map_mul D.what₂.embLL]
  · have := i₂.mul i₁
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  · have := i₂'.mul i₁'
    simpa [mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  · intro h hh w hw
    have := L₁ (h * k₂) (mul_mem hh hk₂) w (L₂ h hh w hw)
    simpa [mul_assoc] using this

end GlobalTheory.FreeBlockMove
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freeLowerBlockVector_eq_translate_kernelDatum : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → ∀ (p : ℕ), (∀ PP ∈ Q, (p : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ x, ((ξ.1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → Formalism.L2.Host.ValLL0 D R.C → ∀ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) → ∃ φ', VecOf R i Q (omegaFree R i Q ξR y₀) φ' ∧ ∃ k ∈ GfC (Vc D i), ∃ (c : D.what₂.LL) (m : ℕ), φ' = D.what₂.embLL c • ω (k, 1) φ ∧ IsIntegral ℤ ((p : D.what₂.LL) ^ m * c) ∧ IsIntegral ℤ ((p : D.what₂.LL) ^ m * c⁻¹) ∧ c ≠ 0 ∧ ∀ h ∈ GfC (Vc D i), ∀ w, InCoefLat R i h w → InCoefLat R i (h * k) (((p : ℂ) ^ m) • w) := by
  atlas_forward_decl GlobalTheory.FreeBlockMove.vecFree_translate
end

section
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompareOff
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open Formalism.HermitianLatticesTheory (localization₂)

theorem mem_localization_iff {Rr W : Type} [CommRing Rr] [AddCommGroup W] [Module Rr W] (p : Ideal Rr) [p.IsPrime]
    (L : Submodule Rr W) (x : W) : x ∈ localization₂ p L ↔ ∃ s : Rr, s ∉ p ∧ s • x ∈ L :=
  ⟨fun ⟨s, hs, h⟩ => ⟨s, hs, h⟩, fun ⟨s, hs, h⟩ => ⟨s, hs, h⟩⟩

theorem localization_le_of_le_localization' {Rr W : Type} [CommRing Rr] [AddCommGroup W] [Module Rr W] (p : Ideal Rr) [p.IsPrime]
    (L M : Submodule Rr W) (h : L ≤ localization₂ p M) : localization₂ p L ≤ localization₂ p M := by
  intro x hx
  obtain ⟨s, hs, hx⟩ := (mem_localization_iff p L x).1 hx
  obtain ⟨t, ht, hy⟩ := (mem_localization_iff p M _).1 (h hx)
  refine (mem_localization_iff p M x).2 ⟨t * s, fun hm => ?_, by rwa [mul_smul]⟩
  rcases Ideal.IsPrime.mem_or_mem ‹p.IsPrime› hm with h1 | h1
  · exact ht h1
  · exact hs h1

theorem natCast_not_mem {K : Type} [Field K] [NumberField K] (lam : HeightOneSpectrum (𝓞 K)) {p : ℕ} (hp : p.Prime)
    (hne : Formalism.EigenvalueLevelCeiling.plc lam ≠ p) : ((p : 𝓞 K)) ∉ lam.asIdeal := by
  intro hm
  haveI : lam.asIdeal.IsPrime := lam.isPrime
  have h0 : ((p : ℕ) : 𝓞 K ⧸ lam.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk lam.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact hm
  have hd : ringChar (𝓞 K ⧸ lam.asIdeal) ∣ p := ringChar.dvd h0
  rcases (Nat.dvd_prime hp).1 hd with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · exact hne h1

theorem splitOffBad_of_mul {D : D7} {V : HSp D} {a b : ℕ} {h : GA D V} (H : SplitOffBad V (a * b) h) : SplitOffBad V a h := by
  obtain ⟨h1, e, P, h2, h3, h4⟩ := H
  refine ⟨h1, e, P, h2, fun PP hPP hm => h3 PP hPP ?_, h4⟩
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hm

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem singleSeries_transl (R : RealDat D A Ks) (i : Fin D.R.m) {ξ χ ξR Q ω φ} (hK : KerDat R i ξ χ ξR Q ω φ)
    {k : GA D (Vc D i)} (hk : k ∈ GfC (Vc D i)) (c : ℂ) (h : GA D (Vc D i)) (w : (R.cV i).W)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    singleSeries R i ω (c • ω (k, 1) φ) h w v = c • singleSeries R i ω φ (h * k) w v := by
  funext g
  have hθ : IsInfFam R.θ := hK.vec.1.2.inf
  have hth := GlobalTheory.VecTheta.isThetaFunO_thPVec hK.vec
  simp only [singleSeries, Datum.thetaKO, Pi.smul_apply]
  rw [GlobalTheory.FiniteFock.pureTensorO_smul, ← GlobalTheory.OrientedHeis.om_fin_pureTensorO R.ψ _ _ _ _ ω hK.weil R.θ hθ k hk 1
    (one_mem _) _ _ _ _ φ _ hth, map_smul, Pi.smul_apply, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem compareOffOwn_run : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (U : Subgroup G), (∀ u : U, ∀ PP : R.Pg, ((R.eG (u : G) PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1) → ∀ (ψ : U →* D.what₂.LLˣ), CompareOffOwn hT.p fw i ℓ U ψ 1 v (ownAt D v) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hPins hβ hLU hIo hRow hPh hCS v hv hmu hQG hFO hVal hξ hMb hRun ℓ hLev hAct U hdetU ψ
  intro lam hlam
  refine localization_le_of_le_localization' _ _ _ (Submodule.span_le.2 ?_)
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨a, s, f', Λ, h, N, x₀, P, x, hs, hsf, hSplit, hLat, hΛlam, hUni, hTriv, hTrivM, hLevN, hAdm, hP, hx⟩ :=
    GlobalTheory.T.exists_orbit_family_adapted_lattice_split_support D G Pl0 T0 A T R F κ v₀ fw O hT hC i hPins ℓ U lam f hf
  obtain ⟨y, s', hy, hs', hyLat⟩ := GlobalTheory.HarmInCoef.harm_mem_coefLat D G Pl0 T0 A T R F κ v₀ fw O hT hC i hPins Λ h (splitOffBad_of_mul hSplit) hLat lam hΛlam P hP
  obtain ⟨ω, φ, hBase⟩ := GlobalTheory.OnCmp.exists_baseKernel D G Pl0 T0 A T.J.Q.c.F R F hC i v hv hmu
  obtain ⟨χ, ξR, hKer⟩ := GlobalTheory.OnBaseKer.kerDat_of_isBaseKernel D G Pl0 T0 A T.J.Q.c.F R F hC i v hv hmu ω φ hBase
  have hEx := GlobalTheory.T.trace_shortSeries_eq_mul_adelicSeries D G Pl0 T0 A T R F κ v₀ fw O hT hC i hPins hβ hLU hIo hRow hPh hCS v hv hmu
    hQG hFO hVal hξ hMb hRun ℓ hLev hAct U hdetU ψ
  obtain ⟨y₀, c, hy₀, hcInt, hSer⟩ :=
    hEx χ ξR ω φ hKer Λ h hSplit hLat N x₀ P x f' y hUni hTriv hTrivM hLevN hAdm hP hx hy
  obtain ⟨φ', hVec, k, hk, c', m, hφ', hpc, -, hc'0, hLatk⟩ := GlobalTheory.T.freeLowerBlockVector_eq_translate_kernelDatum D G Pl0 T0 A T.J.Q.c.F R F hC i _ χ ξR _ ω φ hKer
    (ownAt D v) (fun PP hPP => by classical exact (Finset.mem_filter.1 hPP).2) hξ hVal y₀ hy₀
  obtain ⟨s'', hs'', hs''c⟩ := hcInt lam hΛlam
  obtain ⟨g', hg'⟩ : ∃ g', g' = ∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • cuspTo hT.p fw i (f' u) := ⟨_, rfl⟩
  rw [← hg'] at hSer
  have hp : (ownAt D v).Prime := by
    rcases hFO.own with e | e <;> rw [e]
    exacts [D.host.pde_prime, D.host.pde'_prime]
  have hpl : ((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ∉ lam.asIdeal := natCast_not_mem lam hp hlam
  have hA : ((s : ℕ) : D.what₂.LL) • (∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • cuspTo hT.p fw i (f u)) =
      algebraMap T.Q.c.F D.what₂.LL (a : T.Q.c.F) • g' := by
    classical
    have e1 : ∀ u, ((s : ℕ) : D.what₂.LL) • cuspTo hT.p fw i (f u) =
        algebraMap T.Q.c.F D.what₂.LL (a : T.Q.c.F) • cuspTo hT.p fw i (f' u) := by
      intro u
      have e2 : ((s : ℕ) : T.J.Q.c.F) • (show ↥(cutR T.J.C ((i : ℕ) + 1) (κ i)) from f u) =
          (show T.J.Q.c.F from (a : T.Q.c.F)) • (show ↥(cutR T.J.C ((i : ℕ) + 1) (κ i)) from f' u) :=
        Subtype.ext (hsf u)
      have e3 := congrArg (cutTo fw i) e2
      rw [map_smul, map_smul] at e3
      rw [← algebraMap_smul D.what₂.LL ((s : ℕ) : T.J.Q.c.F), ← algebraMap_smul D.what₂.LL (show T.J.Q.c.F from (a : T.Q.c.F)),
        map_natCast] at e3
      exact e3
    rw [hg', finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [smul_comm, e1 u, smul_comm]
  have hdet : ∀ x : Fin (R.nW i) → D.what₂.LL,
      (∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, adForm R i x (fun ρ => w ρ) = 0) → x = 0 := by
    intro x hx
    have h4 : (R.FW i).j (sg0 D A) x = 0 := by
      obtain ⟨u, hu, -⟩ := hIo i
      exact GlobalTheory.TraceIncl.eq_of_low (R := R) (i := i) hC.models.HW ⟨u, hu⟩
        (x := (R.FW i).j (sg0 D A) x) (y := 0) fun w => by rw [map_zero]; exact hx w
    by_contra hne
    exact ((hLU i (sg0 D A)).1 1 (fun _ => x) (linearIndependent_unique_iff.2 hne)).ne_zero 0 h4
  by_cases hc : c = 0
  · have hz : g' = 0 := hdet g' fun w => by rw [hSer φ' hVec w, hc, map_zero, zero_smul]
    refine (mem_localization_iff _ _ _).2 ⟨(s : 𝓞 D.what₂.LL), hs, ?_⟩
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul D.what₂.LL, hA, hz, smul_zero]
    exact zero_mem _
  · have hs'n : s' ≠ 0 := by
      rintro rfl
      exact hs' (by simp)
    have hs'0 : (s' : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 hs'n
    have hp0 : ((ownAt D v : ℕ) : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    have hc0 : c ≠ 0 := hc
    have hce : D.what₂.embLL c ≠ 0 := (map_ne_zero _).2 hc
    have hce' : D.what₂.embLL c' ≠ 0 := (map_ne_zero _).2 hc'0
    obtain ⟨e, he⟩ : ∃ e, e = (((ownAt D v : ℕ) : D.what₂.LL) ^ m * (s' : D.what₂.LL) * (c * c')⁻¹) • g' := ⟨_, rfl⟩
    have hmem : e ∈ thetaBase R i U ψ 1 v (ownAt D v) := by
      refine Submodule.subset_span ⟨ω, φ, hKer.isKernel, h * k, mul_mem hSplit.1 hk,
        ((ownAt D v : ℂ)) ^ m • ((s' : ℂ) • (O i).c0' y), hLatk h hSplit.1 _ hyLat, fun w => ?_⟩
      rw [he, adForm_smul, MultilinearMap.smul_apply, hSer φ' hVec w, hφ', singleSeries_transl R i hKer hk,
        singleSeries_smul, singleSeries_smul, map_smul, map_smul, map_smul, one_smul, smul_smul, smul_smul, smul_smul]
      congr 1
      simp only [map_mul, map_inv₀, map_pow, map_natCast]
      field_simp
    have hgg : g' = (c * c' * (((ownAt D v : ℕ) : D.what₂.LL) ^ m * (s' : D.what₂.LL))⁻¹) • e := by
      rw [he, smul_smul]
      conv_lhs => rw [← one_smul D.what₂.LL g']
      congr 1
      field_simp
    have hint : IsIntegral ℤ (algebraMap T.Q.c.F D.what₂.LL (a : T.Q.c.F) * ((s'' : D.what₂.LL) * c) *
        (((ownAt D v : ℕ) : D.what₂.LL) ^ m * c')) :=
      ((RingOfIntegers.isIntegral_coe a).algebraMap.mul hs''c).mul hpc
    have hpr := lam.isPrime
    have ht : ((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ^ m * ((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ^ m * (s' : 𝓞 D.what₂.LL) * s'' * (s : 𝓞 D.what₂.LL) ∉ lam.asIdeal := by
      simp only [Ideal.IsPrime.mul_mem_iff_mem_or_mem hpr, not_or]
      exact ⟨⟨⟨⟨fun h1 => hpl (hpr.mem_of_pow_mem _ h1), fun h1 => hpl (hpr.mem_of_pow_mem _ h1)⟩, hs'⟩, hs''⟩, hs⟩
    refine (mem_localization_iff _ _ _).2 ⟨_, ht, ?_⟩
    have key : (((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ^ m * ((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ^ m * (s' : 𝓞 D.what₂.LL) * s'' * (s : 𝓞 D.what₂.LL)) •
        (∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • cuspTo hT.p fw i (f u)) =
        (⟨_, hint⟩ : 𝓞 D.what₂.LL) • e := by
      rw [← algebraMap_smul D.what₂.LL, ← algebraMap_smul D.what₂.LL (⟨_, hint⟩ : 𝓞 D.what₂.LL)]
      have et : algebraMap (𝓞 D.what₂.LL) D.what₂.LL
          (((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ^ m * ((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ^ m * (s' : 𝓞 D.what₂.LL) * s'' * (s : 𝓞 D.what₂.LL)) =
          ((ownAt D v : ℕ) : D.what₂.LL) ^ m * ((ownAt D v : ℕ) : D.what₂.LL) ^ m * (s' : D.what₂.LL) * (s'' : D.what₂.LL) *
            (s : D.what₂.LL) := by
        simp
      have hsc : ((ownAt D v : ℕ) : D.what₂.LL) ^ m * ((ownAt D v : ℕ) : D.what₂.LL) ^ m * (s' : D.what₂.LL) * (s'' : D.what₂.LL) *
          (algebraMap T.Q.c.F D.what₂.LL (a : T.Q.c.F) * (c * c' * (((ownAt D v : ℕ) : D.what₂.LL) ^ m * (s' : D.what₂.LL))⁻¹)) =
          algebraMap T.Q.c.F D.what₂.LL (a : T.Q.c.F) * ((s'' : D.what₂.LL) * c) * (((ownAt D v : ℕ) : D.what₂.LL) ^ m * c') := by
        field_simp
      rw [et, mul_smul, hA, hgg, smul_smul, smul_smul]
      congr 1
      show _ = algebraMap T.Q.c.F D.what₂.LL (a : T.Q.c.F) * ((s'' : D.what₂.LL) * c) * (((ownAt D v : ℕ) : D.what₂.LL) ^ m * c')
      rw [← hsc]
      ring
    rw [key]
    exact Submodule.smul_mem _ _ hmem

end GlobalTheory.CompareOff
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceLattice_le_span_thetaSeries_awayFromOwnPrime : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (U : Subgroup G), (∀ u : U, ∀ PP : R.Pg, ((R.eG (u : G) PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1) → ∀ (ψ : U →* D.what₂.LLˣ), CompareOffOwn hT.p fw i ℓ U ψ 1 v (ownAt D v) := by
  atlas_forward_decl GlobalTheory.CompareOff.compareOffOwn_run
end

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn

namespace GlobalTheory.BigOn

theorem compareOffOwn_atRuns : (AtRuns fun Fm x _ i p r h => ∀ v ∈ p.R.twPl, ∀ j, letI : Algebra (r.used v).full.J.Q.c.F (Fm.D x i).what₂.LL := p.alg; GlobalTheory.TraceClassRank.CompareOffOwn (T := (r.used v).full) (R := R2 p) (h.laws v).p (fw2 p) j (r.lev j) (F2 p).P0 (F2 p).ψ0⁻¹ 1 v (ownAt (Fm.D x i) v)) := by
  refine (GlobalTheory.T.runNumericalConditions_hold_along_family 0).imp ?_
  intro eps Fm CH _ hN
  obtain ⟨x0, H⟩ := hN
  refine ⟨x0, fun x hx hx0 i p hp hM r h _ v hv j => ?_⟩
  have hn := (H x hx hx0 i).2.2.2.2
  obtain ⟨hw1, hcore, hrec⟩ := hM
  have hL := GlobalTheory.T.second_link_of_weight_rows _ _ _ _ _ _ _ _ _ _ p hp hw1
  obtain ⟨hch, -, hLU, -, -, -, hpins, hph⟩ := hL
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hch.lev, hch.grp, hch.fam, hch.models, hch.chain, hch.thP⟩
  have hio : IoExt (R2 p) := hp.ioExt
  have hone : ∀ k, OneMapRow0 p.T (R2 p) p.κ p.v₀ (om2 p) k := fun k => (hp.oneMap k).1
  have hspan := GlobalTheory.ClassSumSpanCore.classSumsSpan_core _ _ _ _ _ p.T (R2 p) (F2 p) p.κ p.v₀ (om2 p) hn hC ⟨fw2 p⟩ hio j
    (hpins j) (hone j)
  have hdel : ∀ y, ((((R2 p).C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 y : ℂˣ) : ℂ) ∈ (Fm.D x i).what₂.embLL.range := by
    intro y
    obtain ⟨z, hz⟩ := (Formalism.L2.Pj.FO_le _ (hcore.delAt_mem (Formalism.EigenvalueLevelCeiling.plc v) y))
    exact ⟨z, hz⟩
  letI : Algebra (r.used v).full.J.Q.c.F (Fm.D x i).what₂.LL := p.alg
  exact GlobalTheory.T.traceLattice_le_span_thetaSeries_awayFromOwnPrime _ _ _ _ _ (r.used v).full (R2 p) (F2 p) p.κ p.v₀ (fw2 p) (om2 p) (h.laws v) hC j (hpins j) (p.betaStd.1 j) hLU hio
    (hone j) (hph j) hspan v hv hch.tup.mu_on p.qGuard (hcore.fieldAt v) hrec.small.val hdel h.half (h.run v hv j) (r.lev j)
    (h.level v j) (h.action v j) (F2 p).P0
    (GlobalTheory.OneMapExact.det_eq_one_of_mem_base (R2 p) (F2 p) hC.grp) (F2 p).ψ0⁻¹

end GlobalTheory.BigOn
end
