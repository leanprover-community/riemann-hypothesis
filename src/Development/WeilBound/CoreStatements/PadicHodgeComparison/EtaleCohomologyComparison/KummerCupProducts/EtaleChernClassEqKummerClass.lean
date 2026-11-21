import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EvExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchClsCocycleSec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StAdd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCol
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StExOfStCol
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StUniq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StTopOfStCol
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EdgeUniqOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullCZsmul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StairCupFirst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignCancel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EdgeCupOfSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LcCover
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitOneSubPow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemBasicOpenOfIsUnitSub
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPrimitiveCl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIdem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoeffIterateVerschiebung
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumToAcrTeichmuller
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLogUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NatDegreeLgLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorialAcr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisZeroImageDividedPower
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UntiltIterateSymmEpsilon
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdemMulEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LineBC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwUgCompAlgebraMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobIdem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRoot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftEx
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernClassUniqueOfLiftAndLog
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepBasic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepConcOfInputs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEvCongr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepOp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResLoc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompOfCechPt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LineMapExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernClassCompatibleSystem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechTripleSubfaceZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResGenRes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedRootOfRep
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecSubsingleton
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLCRes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KapSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecResMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapNsmulTwGen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsKumPow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecMapRes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EdgeUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KapZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedResMor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecPairApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KapOneEqTwGen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleChernClassEqKummerClass
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowDivPowSucc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullPullOfPullC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeomPtGeomMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullSquare
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LcMorCup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimResZetaX
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VnRed
import BuildAid.D2

section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace CrystallineSemistableComparison.E

open CH

theorem cupLeib : CupLeib.{1} := fun _ _ _ _ _ _ _ P _ _ _ h x y => CrystallineSemistableComparison.P.leibniz P h x y

theorem cupCls : CupCls := fun _ _ _ _ _ _ _ P _ _ _ h x y hx hy => CrystallineSemistableComparison.P.cup_cls P h x y hx hy

theorem cupOne : CupOne := fun _ _ _ _ A p x => ((CrystallineSemistableComparison.P.cup_ring A).1 p x).2

theorem morCup : MorCup := by
  intro R R' _ _ σ C _ A A' m ρ hρ
  refine ⟨?_, fun p q n h x y => ?_⟩
  · refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => ?_))
    exact (hρ _ _).trans (map_one (ρ _))
  · exact CrystallineSemistableComparison.P.cup_pull (mulP A) (mulP A') m.G m.τ m.τ m.τ m.nat m.nat m.nat (fun T (a b : A.obj (m.G.obj T)) => by
      rw [hρ, hρ, hρ]; exact map_mul (ρ T) a b) h x y

end CrystallineSemistableComparison.E
end

section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.E

open CH GlobalTheory.EtC

theorem pull_smul_cls {R' : Type} [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    {F : C ⥤ ModuleCat.{0} R'} (G : C' ⥤ C) (t : R') (y : CH.H F 2)
    (z : Cn (G ⋙ F) 2) (hz : d (G ⋙ F) 2 z = 0) (h : (Mor.restrict F G).pull 2 y = (cx (G ⋙ F)).cls z hz) :
    ∃ hz' : d (G ⋙ F) 2 (t • z) = 0, (cx (G ⋙ F)).cls (t • z) hz' = (Mor.restrict F G).pull 2 (t • y) := by
  refine ⟨by rw [map_smul, hz, smul_zero], ?_⟩
  exact ((((Mor.restrict F G).pull 2).map_smul t y).trans (congrArg (t • ·) h)).symm

theorem pull_cls {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    {L : C ⥤ ModuleCat.{0} R} {F : C' ⥤ ModuleCat.{0} R'} (m : Mor L F σ) (z : Cn L 2) (hz : d L 2 z = 0) :
    ∃ hz' : d F 2 (m.pullC 2 z) = 0, m.pull 2 ((cx L).cls z hz) = (cx F).cls (m.pullC 2 z) hz' :=
  ⟨by rw [m.d_pullC, hz, map_zero], rfl⟩

theorem pull_cls' {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C D T P : Type 1} [Category.{0} C] [Category.{0} D]
    [Category.{0} T] [Category.{0} P] (G : C ⥤ D) (π : D ⥤ T) (ι : T ⥤ P) (A : P ⥤ CommAlgCat.{0} R')
    {L : C ⥤ ModuleCat.{0} R} (m : Mor L (modF (((G ⋙ π) ⋙ ι) ⋙ A)) σ) (z : Cn L 2) (hz : d L 2 z = 0) (a : CH.H L 2)
    (ha : a = (cx L).cls z hz) :
    ∃ hz' : d (G ⋙ modF ((π ⋙ ι) ⋙ A)) 2 (m.pullC 2 z) = 0,
      @Eq (CH.H (G ⋙ modF ((π ⋙ ι) ⋙ A)) 2) (m.pull 2 a) ((cx (G ⋙ modF ((π ⋙ ι) ⋙ A))).cls (m.pullC 2 z) hz') := by
  subst ha
  exact pull_cls m z hz

theorem isUnit_gb {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (M : Model l K) : IsUnit (l : Γ(gb M, ⊤)) := by
  have h : IsUnit (l : PadicAlgCl l) := isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have := h.map (((pullback.snd _ _ : gb M ⟶ Spec (CommRingCat.of (PadicAlgCl l))).appTop.hom).comp (toΓ _))
  rwa [map_natCast] at this

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {C : Type 1} [Category.{0} C]

theorem eG_cls (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (G : C ⥤ El M.P) (n : ℕ)
    (x : Ht (l ^ n) (sch.obj (gb M)) (2 : ℕ) 1) (z : Cn (probe H r (G ⋙ CategoryOfElements.π _) n).L 2)
    (hz : d (probe H r (G ⋙ CategoryOfElements.π _) n).L 2 z = 0)
    (he : (pts H r M G n).et 1 2 x = (cx (probe H r (G ⋙ CategoryOfElements.π _) n).L).cls z hz) :
    ∃ hz' : d (G ⋙ modF (AcrEl M.P n)) 2 (lcCo hN H r G n 2 z) = 0,
      eG hN H r M G n 1 2 x = (cx (G ⋙ modF (AcrEl M.P n))).cls (lcCo hN H r G n 2 z) hz' :=
  pull_cls' G (CategoryOfElements.π _) (testι l) (AcrA l n) (lcMor hN H r (G ⋙ CategoryOfElements.π _) n) z hz _ he

theorem tCo_cls (M : Model l K) (G : C ⥤ El M.P) (n : ℕ) (e : EtFam l K) (v : Hl l (sch.obj (gb M)) (2 : ℕ) 0)
    (z : Cn (G ⋙ modF (AcrEl M.P n)) 2) (hz : d (G ⋙ modF (AcrEl M.P n)) 2 z = 0)
    (h : (Mor.restrict (modF (AcrEl M.P n)) G).pull 2 (e M n 2 (v.1 n)) = (cx (G ⋙ modF (AcrEl M.P n))).cls z hz) :
    ∃ hz' : d (G ⋙ modF (AcrEl M.P n)) 2 (tCo G n 2 z) = 0,
      (cx (G ⋙ modF (AcrEl M.P n))).cls (tCo G n 2 z) hz' = (Mor.restrict (modF (AcrEl M.P n)) G).pull 2 (e.tMul M v n) :=
  pull_smul_cls G _ _ z hz h

theorem res_cls (h6 : FRes) (E : EtIn) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (G : C ⥤ El M.P) (n : ℕ)
    (x : Ht (l ^ n) (sch.obj (gb M)) (2 : ℕ) 1) (v : Ht (l ^ n) (sch.obj (gb M)) (2 : ℕ) 0)
    (hv : eM hN H r M n 0 2 v = eM hN H r M n 1 2 x) (y : CH.H (G ⋙ modF (AcrEl M.P n)) 2) (he : eG hN H r M G n 1 2 x = y) :
    (Mor.restrict (modF (AcrEl M.P n)) G).pull 2 (eM hN H r M n 0 2 v) = y :=
  (congrArg (fun a => (Mor.restrict (modF (AcrEl M.P n)) G).pull 2 a) hv).trans ((h6 E hN l H r K M C G n 1 2 x).trans he)

theorem isFirstChern_of_cocycle {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* OC l} {D : LineData X}
    {y : ∀ n, MH (PX q κ) n 2}
    (h : ∀ (C : Type 1) [Category.{0} C] (G : C ⥤ El (PX q κ)) (Λ : Lift G D) (n : ℕ),
      ∃ (z : Cn (G ⋙ modF (AcrEl (PX q κ) n)) 2), Λ.IsCoc n z ∧ ∃ hz : d (G ⋙ modF (AcrEl (PX q κ) n)) 2 z = 0,
        (cx (G ⋙ modF (AcrEl (PX q κ) n))).cls z hz = (Mor.restrict (modF (AcrEl (PX q κ) n)) G).pull 2 (y n)) :
    IsFirstChernClassOfLineBundle q κ D y := fun C _ G Λ n =>
  (h C G Λ n).elim fun z a => a.2.elim fun hz b => Exists.intro z (Exists.intro hz (And.intro a.1 b))

theorem step (h4 : EtaleFirstChernKummer) (h5 : FKum) (h6 : FRes) (E : EtIn) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K)
    (D : LineData M.X) (D' : LineData (gb M)) (π : D'.Y ⟶ D.Y)
    (hD : D.IsBC (pullback.fst _ _ ≫ pullback.fst _ _ : gb M ⟶ M.X) D' π) (L : cech D'.f ⟶ ofCat (glCat 1)) (hL : D'.IsMap L) (n : ℕ)
    (hI : GlobalTheory.EtC.Inv (l ^ n) (cech D'.f)) (x : Ht (l ^ n) (sch.obj (gb M)) 2 1) (hx : pull _ (cechAug D'.f) _ 2 x = c1 (l ^ n) L)
    (G : C ⥤ El M.P) (Λ : Lift G D) :
    ∃ z : Cn (G ⋙ modF (AcrEl M.P n)) 2, Λ.IsCoc n (tCo G n 2 z) ∧ ∃ hz : d (G ⋙ modF (AcrEl M.P n)) 2 z = 0,
      eG hN H r M G n 1 2 x = (cx (G ⋙ modF (AcrEl M.P n))).cls z hz := by
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  exact (h5 hN l H r K M D D' π hD C G Λ n).elim fun z a => a.1.elim fun k =>
    (h4 E.gen E.kum E.c1 (l ^ n) C _ (gb M) (pts H r M G n) D' L hL hI x hx z k).elim fun hz he =>
      Exists.intro (lcCo hN H r G n 2 z) (And.intro a.2 (eG_cls hN H r M G n x z hz he))

theorem firstChern_family_of_lifts (h1 : LineBC) (h2 : LineMap) (h3 : FirstChernCompatibleSystem) (h4 : EtaleFirstChernKummer) (h5 : FKum) (h6 : FRes) (h7 : FUntw) : FirstChernClassFamily :=
  fun E hN l _ H r K M D => (h1 (gb M) M.X (pullback.fst _ _ ≫ pullback.fst _ _) D).elim fun D' a => a.elim fun π hD =>
    (h2 _ D').elim fun L hL =>
      have b := @h3 E.a2 E.a11 l _ D'.Y (gb M) D'.f D'.sm D'.surj (isUnit_gb M) L
      b.2.elim fun x hx => (h7 E hN l H r K M x).elim fun v hv => Exists.intro v (isFirstChern_of_cocycle fun C _ G Λ n =>
        (step h4 h5 h6 E hN H r M D D' π hD L hL n (b.1 n) (x.1 n) (hx n) G Λ).elim fun z c => c.2.elim fun hz e2 =>
          Exists.intro (tCo G n 2 z) (And.intro c.1 (tCo_cls M G n (eFam hN H r K) v z hz
            (res_cls h6 E hN H r M G n (x.1 n) (v.1 n) (hv n) _ e2))))

end CrystallineSemistableComparison.E
end

section
set_option backward.isDefEq.respectTransparency false

namespace CrystallineSemistableComparison.E.Main

theorem inSch : InSch := GlobalTheory.EtC.sch_cls_cocycle_sec

theorem stAdd : StAdd := GlobalTheory.CompanionTheory.StairAdd.stAdd

theorem stCol : StCol := GlobalTheory.CompanionTheory.EdgeStair.stCol

theorem stEx : StEx := GlobalTheory.CompanionTheory.EdgeStair.stEx_of_stCol stCol

theorem stUniq : StUniq := GlobalTheory.CompanionTheory.EdgeStair.stUniq stCol

theorem stTop : StTop := GlobalTheory.CompanionTheory.EdgeMap.stTop_of_stCol stCol

theorem edgeUniq : EdgeUniq := GlobalTheory.CompanionTheory.EdgeClass.edgeUniq_of stCol stAdd stUniq

theorem edgeMap : EdgeMap := GlobalTheory.CompanionTheory.EdgeMapPull.edgeMap

theorem stCupA : StCupA := GlobalTheory.CompanionTheory.StairCupFirst.stCupA cupLeib

theorem stCupB : StCupB := GlobalTheory.CompanionTheory.Staircase.stCupB cupLeib stCol

theorem edgeCup : EdgeCup := GlobalTheory.CompanionTheory.EdgeMap.edgeCup_of_steps cupCls stTop stCupA stCupB

theorem lcCover : LcCover := GlobalTheory.CompanionTheory.LcCoverProof.lcCover

theorem locSplit : LocSplit := GlobalTheory.CompanionTheory.LocSplitProof.locSplit

theorem primAlg : PrimAlg := GlobalTheory.CompanionTheory.PrimAlgProof.primAlg

theorem rootPow : RootPow := GlobalTheory.CompanionTheory.RootPowLC.rootPow primAlg

theorem rootsEx : RootsEx := GlobalTheory.CompanionTheory.RootsC.rootsEx

theorem lcIdem : LcIdem := GlobalTheory.CompanionTheory.TiltIdem.lcIdem

theorem lcSpec : LcSpec := GlobalTheory.CompanionTheory.LcSp.lcSpec_of_lcIdem lcIdem

theorem lcNat : LcNat := GlobalTheory.CompanionTheory.LcNatProof.lcNat lcIdem lcSpec

theorem logEx : LogEx := GlobalTheory.CompanionTheory.CrisLog.logEx

theorem logAlg : LogAlg := GlobalTheory.CompanionTheory.LogAlgPf.logAlg

theorem logMul : LogMul := GlobalTheory.CompanionTheory.LogMulPf.logMul logAlg logEx

theorem logEps : LogEps := GlobalTheory.CompanionTheory.LogEpsP.logEps

theorem epsRoot : EpsRoot := GlobalTheory.CompanionTheory.EpsRootProof.epsRoot

theorem lcLog : LcLog := GlobalTheory.CompanionTheory.LcLogProof.lcLog lcIdem lcSpec lcCover logEx logMul logEps epsRoot

theorem lineBC : LineBC := GlobalTheory.CompanionTheory.LineBase.lineBC

theorem twUg : TwUg := GlobalTheory.CompanionTheory.TwUg.twUg_prop

theorem fPhi : FPhi := GlobalTheory.CompanionTheory.FrobLc.fPhi

theorem fKum : FKum := GlobalTheory.CompanionTheory.FKum.fKum rootPow lcLog

theorem liftEx : LiftEx := GlobalTheory.CompanionTheory.LineLift.liftEx

theorem firstChern_unique : FirstChernUniqueEtale := GlobalTheory.CompanionTheory.EtChern.chern_class_unique_of_lift_and_log liftEx logEx

theorem repBasic : RepBasic := GlobalTheory.CompanionTheory.EtEdge.repBasic evExt evNat inSch

theorem repConc : RepConc := GlobalTheory.CompanionTheory.EdgeMap.repConc_of_inputs evExt inSch repBasic

theorem repCup : RepCup := GlobalTheory.CompanionTheory.EdgeRep.repCup evExt evNat repBasic repConc inSch

theorem repOp : RepOp := GlobalTheory.CompanionTheory.EdgeRep.repOp evNat repConc repBasic

theorem resLoc : ResLoc := GlobalTheory.CompanionTheory.EdgeMap.resLoc

theorem resZero : ResZero := GlobalTheory.CompanionTheory.EtRes.resZero

theorem cechPt : CechPt := GlobalTheory.CompanionTheory.CechPts.cechPt_spec

theorem lineMap : LineMap := GlobalTheory.CompanionTheory.CechLine.lineMap_exists cechPt

theorem chern_class_compatible_system : FirstChernCompatibleSystem := GlobalTheory.CompanionTheory.ChernSys.chern_class_compatible_system cechPt

theorem firstChern_primitive_kummer : FirstChernCoboundary := GlobalTheory.CompanionTheory.KummerPrimitive.main evExt evNat evDel repConc repBasic cechPt

theorem resSplit : ResSplit := GlobalTheory.CompanionTheory.ResSplitProof.resSplit resLoc locSplit lcCover

theorem repRoot : RepRoot := GlobalTheory.CompanionTheory.EtRoot.repRoot repConc resZero

theorem redRoot : RedRoot := GlobalTheory.CompanionTheory.EdgeMap.redRoot_of_rep repRoot repOp repConc

theorem twZero : TwZero := GlobalTheory.CompanionTheory.TwZeroGen.twZero rootPow lcCover repRoot

theorem kapSpec : KapSpec := GlobalTheory.CompanionTheory.KapSpecProof.kapSpec lcCover repRoot

theorem kapBij : KapBij := GlobalTheory.CompanionTheory.KapBij.kapBij lcCover repRoot kapSpec

theorem kapMul : KapMul := GlobalTheory.CompanionTheory.KapMulE.kapMul_of lcCover repRoot kapSpec

theorem kapRed : KapRed := GlobalTheory.CompanionTheory.CstE.KapRedP.kapRed lcCover repRoot kapSpec

theorem kumPow : KumPow := GlobalTheory.CompanionTheory.KumPowProof.kumPow lcCover repRoot kapSpec primAlg

theorem resGood : ResGood := GlobalTheory.CompanionTheory.EdgeRes.resGood kapSpec kapBij resZero resSplit

theorem etSpec : EtSpec := GlobalTheory.CompanionTheory.EtSpecProof.etSpec resGood stEx edgeUniq repBasic resZero

theorem etNat : EtNat := GlobalTheory.CompanionTheory.EtNatProof.etNat etSpec edgeMap repBasic kapSpec twZero

theorem etRed : EtRed := GlobalTheory.CompanionTheory.EdgeRed.etRed etSpec edgeMap repBasic repOp kapSpec kapRed

theorem etCup : EtCup := GlobalTheory.CompanionTheory.EdgeProduct.etCup etSpec resGood edgeCup repBasic repCup kapMul

theorem etRoot : EtRoot := GlobalTheory.CompanionTheory.EdgeRoot.etRoot_of_spec etSpec repRoot kapSpec

theorem etale_chern_class_eq_kummer_class : EtaleFirstChernKummer := GlobalTheory.CompanionTheory.EtaleChernClass.etale_chern_class_eq_kummer_class etSpec resGood stCol firstChern_primitive_kummer kumPow

theorem fRed : FRed := GlobalTheory.CompanionTheory.EtReduction.fred_of_etRed etRed

theorem fEqui : FEqui := GlobalTheory.CompanionTheory.FEquiProof.fEqui etNat twUg

theorem fNat : FNat := GlobalTheory.CompanionTheory.FNatProof.fNat etNat

theorem fRes : FRes := GlobalTheory.CompanionTheory.FResProof.fRes etNat

theorem fCup : FCup := GlobalTheory.CompanionTheory.EtCupF.fCup etCup morCup lcSpec

theorem fRoot : FRoot := GlobalTheory.CompanionTheory.FRootCls.froot etRoot redRoot morCup lcSpec

theorem fUntw : FUntw := GlobalTheory.CompanionTheory.FUntwPf.main fCup fRoot cupOne

theorem firstChern_family : FirstChernClassFamily := firstChern_family_of_lifts lineBC lineMap chern_class_compatible_system etale_chern_class_eq_kummer_class fKum fRes fUntw

theorem etale_comparison_map : EtaleComparisonMapExists := etale_comparison_map_of_facts rootsEx lcNat fRed fEqui fPhi fNat fCup fRoot firstChern_family

end CrystallineSemistableComparison.E.Main
end
