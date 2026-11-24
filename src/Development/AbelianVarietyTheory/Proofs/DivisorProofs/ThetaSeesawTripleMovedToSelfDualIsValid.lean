module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MoveTriLat
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFrameFinitePartMulOfCarriesLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarFundamentalDomainRightTranslateUnitaryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedFiniteDatumNegHomEqStandardPairFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedVacuumHomEqVacuumMovedLattices
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedVacuumNegHomEqVacuumMovedLattices
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedFiniteDatumEqStandardPairSecondMemberStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Grid Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Mult MeasureTheory

noncomputable section

namespace GlobalTheory.BotMove

theorem rig_move {D : D7} {V : HSp D} (rr : Rig V) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (g : GA D V)
    (hr : rr.Is) (hΛ : IsSelfDualC V Λ) (hm : GlobalTheory.FinPl.Moves V g rr.Λ Λ (fun _ => True)) :
    Rig.Is (⟨Λ, Lev.finE V g * rr.β, rr.s, rr.B⟩ : Rig V) :=
  ⟨hΛ, GlobalTheory.Core.Mi.FrameMove.isFrame_of_moves D V g rr.Λ Λ rr.β hm hr.2.1, hr.2.2⟩

theorem moveTri_is : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    ∀ g ∈ GfC A, ∀ g' ∈ GfC A', ∀ h ∈ GfC WW,
    GlobalTheory.FinPl.Moves A g Y.rA.Λ ΛA (fun _ => True) → GlobalTheory.FinPl.Moves A' g' Y.rA'.Λ ΛA' (fun _ => True) →
    GlobalTheory.FinPl.Moves WW h Y.rW.Λ ΛW (fun _ => True) →
    ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r t ≠ 0 ∧ r' t ≠ 0) →
    (∀ t, Y.ω t (g, h) Y.vac = r t • Y.ω t₀ (g, h) Y.vac) → (∀ t, Y.ω' t (g', h) Y.vac' = r' t • Y.ω' t₀ (g', h) Y.vac') →
    (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').Is ψ θ α β νH S := by
  intro D T A A' WW Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mA mA' mW t₀ r r' hr hv hv'
  exact ⟨hY.rank, rig_move _ _ _ hY.rigA hA mA, rig_move _ _ _ hY.rigA' hA' mA', rig_move _ _ _ hY.rigW hW mW, hY.weil,
    hY.weil', GlobalTheory.T.movedVacuum_negHom_eq_vacuum_movedLattices Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mA mA' mW t₀ r r' hr hv hv', GlobalTheory.T.movedVacuum_hom_eq_vacuum_movedLattices Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mA mA' mW t₀ r r' hr hv hv', hY.idem, hY.expo, GlobalTheory.T.movedFiniteDatum_negHom_eq_standardPair_first Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mA mA' mW t₀ r r' hr hv hv',
    GlobalTheory.T.translated_finite_datum_eq_standardPairSecondMember Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mA mA' mW t₀ r r' hr hv hv', GlobalTheory.T.haar_fundamentalDomain_rightTranslate_unitary _ _ g hY.meas.1 hY.meas.2, GlobalTheory.T.haar_fundamentalDomain_rightTranslate_unitary _ _ g' hY.meas'.1 hY.meas'.2⟩

end GlobalTheory.BotMove

end
