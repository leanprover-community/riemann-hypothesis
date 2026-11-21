import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NcardPrimesOverOfSplitsCompl
import Formalism.SharpRestriction.CuspSpanNormBounds.UniformConstantsAndStatements
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

section P29cRecord

variable (D : D7)

def ngLoop (u u' : D.what₂.Word) : Set (D.s.Pair u u') :=
  {p | p ∈ pairsIn D.s (famNG D.s) ∧ 2 ≤ D.s.s0 p}

def ngOne (u u' : D.what₂.Word) : Set (D.s.Pair u u') :=
  {p | p ∈ pairsIn D.s (famNG D.s) ∧ D.s.s0 p < 2}






def NGOneAt (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C : ℝ) : Prop :=
  Summable (fun p : ngOne D u u' => ‖D.s.pval p.1‖) ∧
  gaG D * (∑' p : ngOne D u u', D.s.pval p.1).re ≤
    (2 : ℝ) ^ (-((D.R.k : ℝ) - 2 * (D.R.rS : ℝ) - 5)) *
      Real.exp (C * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L) *
      ((D.duS u : ℝ) * (D.duS u' : ℝ)) / D.what₂.Dstar











end P29cRecord

section Chain

open scoped ENNReal



variable (D : D7)

abbrev PtB (u u' : D.what₂.Word) : Type :=
  {γ : Point D.host.E (D.R.rS + 1) // ThB.IsBPt D (Lat.Tu D u) (Lat.Tu D u') γ}

structure NGObj (u u' : D.what₂.Word) : Type 1 where
  Cls : Type
  wC : Cls → ℝ≥0∞
  t : Cls → PtB D u u' → ℝ≥0∞
  a : Cls → PtB D u u' → ℝ≥0∞
  nu : PtB D u u' → ℝ≥0∞
  Jsq : PtB D u u' → ℝ≥0∞

variable {D} {u u' : D.what₂.Word}

def StepClass (O : NGObj D u u') (S : ℝ) : Prop :=
  ENNReal.ofReal S ≤ ∑' c, O.wC c * (∑' γ, O.t c γ) ^ 2 ∧ ∀ c γ, O.t c γ ^ 2 ≤ O.nu γ * O.a c γ * O.Jsq γ

def StepMean (O : NGObj D u u') (G1 cc p : ℝ) : Prop :=
  ∀ γ : PtB D u u', O.nu γ * ∑' c, O.wC c * O.a c γ ≤
    ENNReal.ofReal (G1 * cc * (ptWeightG D (rhoReal D) (Lat.Tu D u) (Lat.Tu D u') γ.1.1 *
      ThB.normWt D (Lat.Tu D u) (Lat.Tu D u') γ.1 ^ p))

def StepB (O : NGObj D u u') (p B2 : ℝ) (MM : ℝ≥0∞) : Prop :=
  ∑' γ : PtB D u u', ENNReal.ofReal (ThB.wPt D γ.1 * ptWeightG D (rhoReal D) (Lat.Tu D u) (Lat.Tu D u') γ.1.1 *
      ThB.normWt D (Lat.Tu D u) (Lat.Tu D u') γ.1 ^ p) * O.Jsq γ ≤ ENNReal.ofReal B2 * MM


end Chain

section Assembly

open scoped ENNReal
open IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def MainCount (D : D7) (u u' : D.what₂.Word) (C cInf : ℝ) (constP : HeightOneSpectrum (𝓞 D.host.F) → ℝ)
    (dens : Cnt.GramM D → HeightOneSpectrum (𝓞 D.host.F) → ℝ) : Prop :=
  0 < cInf ∧ (∀ p, 0 < constP p) ∧ Multipliable constP ∧ 0 < ∏' p, constP p ∧
  (∀ Z p, |dens Z p - 1| ≤ C * (Ideal.absNorm p.asIdeal : ℝ) ^ (-((D.R.k : ℝ) - 2 * D.R.rS - 3))) ∧
  (∀ F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
    ∀ what₂ : Finset (Cnt.LatV D), IsRowReps D F0 what₂ →
    ∀ Z : Cnt.GramM D, (∀ τ, 0 < Cnt.Gz D (Tr D u) (Tr D u') Z τ) →
      (∃ Λ ∈ what₂, ∃ F' : Cnt.FlagU D u', UniformConstantsAndStatements.IsNormFrame D Λ (lf D F0) F' ∧ Lat.ZhatL (lf D F0) F' = Z) →
      Multipliable (dens Z) ∧
      UniformConstantsAndStatements.nuTot D u u' F0 what₂ Z =
        ENNReal.ofReal (cInf * (∏' p, constP p) * (∏' p, dens Z p) *
          ∏ τ, Cnt.Gz D (Tr D u) (Tr D u') Z τ ^ ((D.R.k : ℝ) - 1)))





end Assembly

section P29cFamily

variable {eps : ℝ} (Fm : FamP eps) (g : UniformConstantsAndStatements.Given)


def NGOneF (C : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => UniformConstantsAndStatements.Hyp (Fm.D x i) (Fm.L x i) (g.wth C' Cl) →
    ∀ u u', NGOneAt (Fm.D x i) (Fm.L x i) u u' C




def NGOneBdF (C : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => UniformConstantsAndStatements.Hyp (Fm.D x i) (Fm.L x i) (g.wth C' Cl) → ∀ u u' : (Fm.D x i).what₂.Word,
    gaG (Fm.D x i) * (∑' p : ngOne (Fm.D x i) u u', (Fm.D x i).s.pval p.1).re ≤
      (2 : ℝ) ^ (-(((Fm.D x i).R.k : ℝ) - 2 * ((Fm.D x i).R.rS : ℝ) - 5)) *
        Real.exp (C * ((Fm.D x i).R.m : ℝ) ^ 5 * ((Fm.D x i).R.f : ℝ) * (Fm.L x i).sc.L) *
        (((Fm.D x i).duS u : ℝ) * ((Fm.D x i).duS u' : ℝ)) / (Fm.D x i).what₂.Dstar

def SecondPacketFamilyInequality (C : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => UniformConstantsAndStatements.Hyp (Fm.D x i) (Fm.L x i) (g.wth C' Cl) → ∀ u : (Fm.D x i).what₂.Word,
    ‖(gaG (Fm.D x i) : ℂ) * ∑' p : UnitaryVolumeMass.scalG (Fm.D x i) u u, (Fm.D x i).s.pval p.1‖ ≤
      Real.exp (C * ((Fm.D x i).R.m : ℝ) ^ 5 * ((Fm.D x i).R.f : ℝ) * (Fm.L x i).sc.L) *
        ((Fm.D x i).duS u : ℝ) ^ 2 / (Fm.D x i).what₂.Dstar





def FirstPacketRemainder (a : UniformConstantsAndStatements.AdmC) (C : ℝ) : Prop := UniformConstantsAndStatements.FirstFiltrationHypotheses Fm g a → NGOneF Fm g C

def SecondPacketRemainder (a : UniformConstantsAndStatements.AdmC) (C : ℝ) : Prop := UniformConstantsAndStatements.SecondFiltrationHypotheses Fm g a → SecondPacketFamilyInequality Fm g C





end P29cFamily


end Formalism.MainNotions.BridgeLemma

end
