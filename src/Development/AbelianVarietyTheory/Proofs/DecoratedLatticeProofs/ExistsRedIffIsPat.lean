module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedBy
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPatOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReduction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReductionIffPattern
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevZero

theorem exists_red_iff_isPat : ∀ {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt G.q.e PP → ∀ g : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP), (∃ x, GlobalTheory.LevZero.Red G PP x g) ↔ GlobalTheory.SymRes.IsPat D.R.rS D.R.k g := by
  intro D c v G PP hidem g
  obtain ⟨π', h1, h2, -⟩ := GlobalTheory.FinPl.SplitPt.exists_lift_isRed D G.k G.q PP hidem
  have hr : D.R.r = D.R.k + (G.s + 1) := by
    have := G.hs
    unfold Ranks.r
    omega
  have hρ : D.R.rS = G.S.ρ := by
    have := G.hs
    have := G.S.odd
    unfold Ranks.rS
    omega
  let π : 𝓞 D.host.E →+* G.k :=
    (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype).comp (oToS D.host.F D.host.E)
  have hπ : ∀ z : 𝓞 D.host.E, π z = (GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E) := fun z =>
    h1 (incA D (z : D.host.E))
  have h : GlobalTheory.FunObj.Comparison₂.IsRed (Ideal.Quotient.mk PP.asIdeal) π :=
    ⟨h2.field, fun z => h2.int _, fun z => (iff_of_eq (congrArg (· = 0) (resS_oToS (F := D.host.F) PP z).symm)).trans (h2.ker _)⟩
  have := GlobalTheory.SymRes.exists_red_iff_isPat PP.asIdeal π h hr G.S g
  simp only [hπ] at this
  rw [hρ]
  exact this

end GlobalTheory.LevZero
