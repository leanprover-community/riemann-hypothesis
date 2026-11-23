module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompOfOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockDiagonalWithIdentity
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjParahoricBlockLift
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

theorem _root_.GlobalTheory.T.exists_conj_parahoric_block_lift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (k : Fin D.R.m) (s : T)
  (P : Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc D k) D.R.nV) (L : G0g D.nd → Formalism.AUTREP.GAf D.host.E D.R.nV),
  (∀ g, L g ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV) →
  (∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV, Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc D k) (P.ψ κ) ∈ Formalism.L2.DIV.St (R.βV k)) →
  (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q s → ∃ (s' : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w)
      (b : GL (Fin D.R.nV) (Formalism.L2.DIV.kP s'.w)), s'.w = PP ∧ GlobalTheory.CenFrame.IsResidue s' φ ∧
        GlobalTheory.CenFrame.FrameRed (GlobalTheory.FrameBlockDiagonal.rankV D k) P (R.βV k) s' φ b ∧ (PP ∈ R.Pg → b ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 D.R.r))) →
  (∀ g (s' : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w), GlobalTheory.CenFrame.IsResidue s' φ →
      (s'.w ∈ R.Q s → ∃ y, GlobalTheory.CenFrame.IsCompOf s' (L g) y ∧ Matrix.GeneralLinearGroup.map φ y = 1) ∧
      ∀ hP : s'.w ∈ R.Pg, ∃ y, GlobalTheory.CenFrame.IsCompOf s' (L g) y ∧
        GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity (R.eG ((R.eG.trans cG).symm g) ⟨s'.w, hP⟩) (Matrix.GeneralLinearGroup.map φ y)) →
  ∃ c : G, ∀ g : G,
    Formalism.IndefR.Lev.IsLevelLift (Formalism.IndefR.Links.Vc D k) (R.βV k) (R.datVt k s) (R.eG g) (P.ψ (L ((R.eG.trans cG) (c * g * c⁻¹)))) ∧
    Formalism.IndefR.Lev.levChi (Formalism.IndefR.Links.Vc D k) (R.βV k) (Formalism.IndefR.Lev.flagL (R.datVt k s)) (P.ψ (L ((R.eG.trans cG) (c * g * c⁻¹)))) = 1 := by
  first | exact @GlobalTheory.ParahLift.exists_conj_parahoric_lift | exact GlobalTheory.ParahLift.exists_conj_parahoric_lift | (intros; apply GlobalTheory.ParahLift.exists_conj_parahoric_lift <;> assumption)
