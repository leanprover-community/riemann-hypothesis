import Formalism.SharpRestriction.GlobalSchurBounds.LinkPk
import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
import Formalism.LocalToGlobal.HermitianColumns.StarConj
import Formalism.LocalToGlobal.HermitianForms.FormsTied
import Formalism.LocalToGlobal.BesselHermitianTheta.Lemmas
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeConventionOfFlags
import Formalism.LocalToGlobal.GlobalTheory.NormSqLatticeFunctionEq
import Formalism.LocalToGlobal.GlobalTheory.PowFourLtCeilThresholdPrime
import Formalism.LocalToGlobal.GlobalTheory.PlacesP
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeConventionOfHermitian
import Formalism.LocalToGlobal.GlobalTheory.GL1.AdelicLatticeLinkFamily
import Formalism.SharpRestriction.SmoothDesignExistence.LinkGLOBALPk
import Formalism.LocalToGlobal.GlobalTheory.FamCol
import Formalism.LocalToGlobal.GlobalTheory.AnalyticConclusionOfProp25

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions.Lnk NumberField

structure GlobalObj (D : D7) where

  host : Formalism.L2.Host.HostTied D

  herm : Formalism.L2.Herm.FullTied D

  forms : ∀ u : D.what₂.Word, Formalism.L2.Forms.FormsTied D u

structure CurveObj (D : D7) where
  δ : ℂ
  delta_pow_twelve_eq_discr : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ
  χ : TaylorLogMetric.IdE D → ℂ
  chi : TaylorLogMetric.IsChi D χ
  e : TaylorLogMetric.FamE D
  M : IntermediateField ℚ ℂ
  [nf : NumberField M]
  eL : D.what₂.LL ≃+* M
  emb : ∀ y, ((eL y : M) : ℂ) = D.what₂.embLL y
  d : D.what₂.Tau → M
  gen : ∀ τ, TaylorLogMetric.ellT D M τ = Submodule.span (𝓞 M) {d τ}

attribute [instance] CurveObj.nf

structure GlobalObjF {eps : ℝ} (Fm : FamP eps) where
  T : ∀ x (i : Fm.Ix x), GlobalObj (Fm.D x i)
  K : ∀ x (i : Fm.Ix x), CurveObj (Fm.D x i)

structure CurveTies (D : D7) (K : CurveObj D) : Prop where
  om : ∀ τ (s : D.what₂.LL →+* ℂ), D.gx.Om τ s =
    (Real.pi * ‖conjOf K.eL s (K.d τ)‖ ^ 2 / TaylorLogMetric.area (TaylorLogMetric.lamConj K.M (conjOf K.eL s) (TaylorLogMetric.lamOf D D.host.ccK K.δ)))⁻¹
  thOne : ∀ s : D.what₂.LL →+* ℂ, ∃ G, IsTheta0 D.host.d (TaylorLogMetric.lamConj K.M (conjOf K.eL s) (TaylorLogMetric.lamOf D D.host.ccK K.δ)) G ∧
    D.gx.thOne s ^ 2 = normSq1 (TaylorLogMetric.lamConj K.M (conjOf K.eL s) (TaylorLogMetric.lamOf D D.host.ccK K.δ)) G
  thFree : ∀ (u : D.what₂.Word) (i : ℕ), i < D.R.m → ∀ (c : (D.mem u).C.cls i) (c' : (D.mem u).C.cls (i + 1)),
    ∃ (L : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin (D.R.N (i + 1)) → D.host.E)),
      TaylorLogMetric.admitted D (D.R.N i) (D.R.N (i + 1)) L L' ∧ TaylorLogMetric.CoefIn D (K.e (D.R.N i) (D.R.N (i + 1)) L L') K.M ∧
      ∀ s : D.what₂.LL →+* ℂ,
        (D.fm u).thFree i s c c' ^ 2 = normConj D K.δ K.e K.M (conjOf K.eL s) (D.R.N i) (D.R.N (i + 1)) L L'

structure GlobalTiesF {eps : ℝ} {Fm : FamP eps} (O : GlobalObjF Fm) : Prop where
  real : ∀ x (i : Fm.Ix x), Formalism.L2.Theta.RealTied (Fm.D x i)
  curve : ∀ x (i : Fm.Ix x), CurveTies (Fm.D x i) (O.K x i)
  extra : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.L2.Herm.ExtraTied (O.T x i).herm (Fm.ex x hx i)

structure GlobalChoicesF {eps : ℝ} {Fm : FamP eps} (O : GlobalObjF Fm) : Prop where
  dataIn : ∀ x (i : Fm.Ix x), TaylorLogMetric.DataIn (Fm.D x i) (TaylorLogMetric.tor0 (Fm.D x i) (Fm.D x i).host.ccK (O.K x i).δ) (O.K x i).M
  kRat : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, flipTwoThree.adm7 (Fm.D x i)

structure CurveClaims (D : D7) (C : ℝ) (K : CurveObj D) : Prop where
  cl22 : Cl22 D C D.host.ccK K.δ K.χ K.e
  thPow : GL3Theta.thPow D D.host.ccK K.δ K.e

structure PendClaims (D : D7) : Prop where

  colVal : flipTwoThree.adm3 D → ∀ u, Nonempty (flipTwoThree.ColVal D u)

  UpDownIncidenceInverse : ∀ u, product_first_zeroth_parts.UpDownIncidenceInverse D u

  admT : ∀ u, product_first_zeroth_parts.admT D u

  br : ∀ u, ∃ P : product_first_zeroth_parts.Pend D u, product_first_zeroth_parts.ArchimedeanSignatureMatching P

structure GlobalClaimsF {eps : ℝ} {Fm : FamP eps} (O : GlobalObjF Fm) (C : ℝ) : Prop where
  curve : ∀ x (i : Fm.Ix x), CurveClaims (Fm.D x i) C (O.K x i)
  pend : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, PendClaims (Fm.D x i)

def GlobalTiedF {eps : ℝ} (Fm : FamP eps) (C : ℝ) : Prop :=
  ∃ O : GlobalObjF Fm, GlobalTiesF O ∧ GlobalChoicesF O ∧ GlobalClaimsF O C











theorem GlobalTiedF.kRat {eps : ℝ} {Fm : FamP eps} {C : ℝ} (h : GlobalTiedF Fm C) : flipTwoThree.admF7 Fm := by
  obtain ⟨O, -, hK, -⟩ := h
  exact ⟨0, fun x _ hx i => hK.kRat x hx i⟩

theorem GlobalTiedF.colVal {eps : ℝ} {Fm : FamP eps} {C : ℝ} (h : GlobalTiedF Fm C) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) :
    flipTwoThree.adm3 (Fm.D x i) → ∀ u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u) := by
  obtain ⟨O, -, -, hC⟩ := h
  exact (hC.pend x hx i).colVal

theorem GlobalTiedF.pend {eps : ℝ} {Fm : FamP eps} {C : ℝ} (h : GlobalTiedF Fm C) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) :
    flipTwoThree.adm7 (Fm.D x i) ∧ (flipTwoThree.adm3 (Fm.D x i) → ∀ u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u)) := by
  obtain ⟨O, -, hK, hC⟩ := h
  exact ⟨hK.kRat x hx i, (hC.pend x hx i).colVal⟩


end Formalism.L2.GlobalTheoryTheory

end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.ConcTop

section Part1

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions.Lnk Formalism.MainNotions.Pk Formalism.L2.GlobalTheoryTheory NumberField

def ObjSel (𝒞 : FamClass) := ∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → GlobalObjF Fm

def RowReal (𝒞 : FamClass) : Prop :=
  Closed 𝒞 fun Fm _ => ∀ x (i : Fm.Ix x), Formalism.L2.Theta.RealTied (Fm.D x i)

def RowCurveTies (𝒞 : FamClass) (O : ObjSel 𝒞) : Prop :=
  Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm, ∀ x (i : Fm.Ix x), CurveTies (Fm.D x i) ((O Fm hc).K x i)

def RowExtra (𝒞 : FamClass) (O : ObjSel 𝒞) : Prop :=
  Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm, ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
    Formalism.L2.Herm.ExtraTied ((O Fm hc).T x i).herm (Fm.ex x hx i)

def RowDataIn (𝒞 : FamClass) (O : ObjSel 𝒞) : Prop :=
  Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm, ∀ x (i : Fm.Ix x),
    TaylorLogMetric.DataIn (Fm.D x i) (TaylorLogMetric.tor0 (Fm.D x i) (Fm.D x i).host.ccK ((O Fm hc).K x i).δ) ((O Fm hc).K x i).M

def RowKRat (𝒞 : FamClass) : Prop :=
  Closed 𝒞 fun Fm _ => ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, flipTwoThree.adm7 (Fm.D x i)

def ThetaObjectClauses (𝒞 : FamClass) (O : ObjSel 𝒞) (C : ℝ) : Prop :=
  Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm, ∀ x (i : Fm.Ix x),
    Cl22 (Fm.D x i) C (Fm.D x i).host.ccK ((O Fm hc).K x i).δ ((O Fm hc).K x i).χ ((O Fm hc).K x i).e

def RowThPow (𝒞 : FamClass) (O : ObjSel 𝒞) : Prop :=
  Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm, ∀ x (i : Fm.Ix x),
    GL3Theta.thPow (Fm.D x i) (Fm.D x i).host.ccK ((O Fm hc).K x i).δ ((O Fm hc).K x i).e

def RowColVal (𝒞 : FamClass) : Prop :=
  Closed 𝒞 fun Fm _ => ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, flipTwoThree.adm3 (Fm.D x i) → ∀ u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u)

def RowAdm0 (𝒞 : FamClass) : Prop :=
  Closed 𝒞 fun Fm _ => ∀ x, Fm.x1 < x → ∀ (i : Fm.Ix x) u, product_first_zeroth_parts.UpDownIncidenceInverse (Fm.D x i) u

def RowAdmT (𝒞 : FamClass) : Prop :=
  Closed 𝒞 fun Fm _ => ∀ x, Fm.x1 < x → ∀ (i : Fm.Ix x) u, product_first_zeroth_parts.admT (Fm.D x i) u

def RowBr (𝒞 : FamClass) : Prop :=
  Closed 𝒞 fun Fm _ => ∀ x, Fm.x1 < x → ∀ (i : Fm.Ix x) u, ∃ P : product_first_zeroth_parts.Pend (Fm.D x i) u, product_first_zeroth_parts.ArchimedeanSignatureMatching P

def ClosedStandardLatticeFamilyAssumption (𝒞 : FamClass) : Prop := Closed 𝒞 fun Fm _ => StandardLattice.FamilyTheoremThreeAdmitted Fm

def ClosedThetaFamilyConstant (𝒞 : FamClass) (C22 : ℝ) : Prop := Closed 𝒞 fun Fm _ => TaylorLogMetric.StatementFamilyConstant Fm C22
def ClosedKudlaFamilyConstantFree (𝒞 : FamClass) : Prop := Closed 𝒞 fun Fm _ => flipTwoThree.KudlaFamilyStatement Fm
def ClosedKudlaFamilyStandardLattice (𝒞 : FamClass) (C3 : ℝ) : Prop := Closed 𝒞 fun Fm _ => StandardLattice.KudlaFamilyStatement Fm C3
def ClosedPacketCrystallineStatement (𝒞 : FamClass) (crystallineComparison : ℝ) : Prop := Closed 𝒞 fun Fm _ => product_first_zeroth_parts.KudlaFamilyStatement Fm crystallineComparison

def LinkClosed (𝒞 : FamClass) (Cabs C0 eL : ℝ) : Prop :=
  Closed 𝒞 fun Fm CH => Fm.CoverAll → TuSize Fm → DGamSize Fm → LinkGLOBAL Fm Cabs CH C0 Cabs eL

def ClosedCompatible (𝒞 : FamClass) (C22 : ℝ) : Prop := Closed 𝒞 fun Fm _ => GlobalTiedF Fm C22

def WithCompatibility (𝒞 : FamClass) (C22 : ℝ) : FamClass := fun Fm => 𝒞 Fm ∧ GlobalTiedF Fm C22

def objOfCompatible (𝒞 : FamClass) (C22 : ℝ) : ObjSel (WithCompatibility 𝒞 C22) := fun _ hc => Classical.choose hc.2

end Part1

section Part2

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LBr2 Formalism.LFunctionChainParameters.LBrDiv Formalism.LFunctionChainParameters.SectionsFourToSixTransfer Formalism.LFunctionChainParameters.LChain6
  Formalism.L2.GlobalTheoryTheory.MergeGL2

def ConcCoreAt (q d : ℕ) [Fact q.Prime] [Fact d.Prime] (A c' Cord eD eL K cHH eK eW KW ε x : ℝ) : Prop :=
  ∃ (e : ℕ) (Ω : Type) (_ : Fintype Ω)
    (W : Ω → HA e → Type) (_ : ∀ o u0, Fintype (W o u0)) (_ : ∀ o u0, Nonempty (W o u0)) (m : ℕ)
    (G : Glob) (C : Consts) (N : ℕ)
    (TT T2 : Finset (HA e)) (a : Ω → HA e → ℝ) (w : Ω → HA e → Fin m → E0 × HA e → ℝ)
    (Q : ∀ o u0, FamCol.Pt (W o u0)) (Rw : ∀ o u0, Formalism.LFunctionChainParameters.LChain6.Rows ((Q o u0).fam m))
    (O : ∀ o, Formalism.LFunctionChainParameters.LChain6.SizeCountLevelObjects (HA e) (W o) m TT)
    (Lp : HA e → Ω → LossP (HA e) m)
    (P : Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.Par) (π : Ω → ℝ) (s sB : Finset ℕ) (BAD : ℕ → HA e → Prop) (Sig : ℕ → Ω → ℝ) (η : ℝ)
    (g₁ g₂ : ℕ) (logOm C0 cZ cL cE5 c5 : ℝ),
    G.x = x ∧ G.ε = ε ∧ C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ C.cHH ≤ cHH ∧ P.e₂ = e ∧
    ((2 ^ e : ℕ) : ℝ) ≤ x ^ A ∧
    G.v = hostV e q d ∧ g₁.Prime ∧ g₂.Prime ∧ G.lg = Real.log ((g₁ : ℝ) * (g₂ : ℝ)) ∧
    PerHost e q d logOm ∧
    LossHyp (hostData e q d) G C N TT a w (fun o u0 => (Q o u0).fam m) Lp P π s sB BAD Sig Cord eW KW ∧
    ∀ o, 0 < π o →
      (∀ u0, (Q o u0).OkIn m (PhiSet (H := HA e)).card g₁ g₂ (XppH (HA e) G)) ∧
      FamCol.RemainingInputsAfter (hostData e q d) (hostEll e q d) G C N TT T2 (a o) (w o) (Q o) (Rw o) (O o) η
        (Real.exp (-c' * x ^ (ε / 8))) eK K logOm C0 cZ cL cE5 c5 g₁ g₂

def ConcreteMainReduction : Prop :=
  ∃ Cord c' : ℝ, 0 ≤ Cord ∧ 0 < c' ∧ ∀ eD eL ε₁ : ℝ, 0 < ε₁ →
    (∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ A K cHH eK eW KW x₀ : ℝ, 0 < A ∧ ∀ x : ℝ, x₀ ≤ x →
        ∀ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime),
          ConcCoreAt (q1At ε x) (dAt ε x) A c' Cord eD eL K cHH eK eW KW ε x) →
    RiemannHypothesis

end Part2

end Formalism.L2.GlobalTheoryTheory.ConcTop

end
end
