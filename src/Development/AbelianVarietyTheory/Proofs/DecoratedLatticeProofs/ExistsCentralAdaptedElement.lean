module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedBy
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastWittLineOfBesselJacobiLatticesGoodStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedLatticeIndexZeroNormalFrameComponentStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulMulDivCancelLeft
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StabMatch
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.LevZero.StabMatch

variable {D : D7}

def Facts {c : Comm D} {v : VCom c} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ι : Type} (o : TDat c k ι) {n : ℕ} (G : Fin n → GLoc v) (Lm : Lat (c.V 0)) (b : BesAt (c.V 0) (c.X 0) D.R.rS) : Prop :=
  ∃ M : Lat b.V₀,
    (∀ p, IsSelfDualC b.V₀ M ∧ MonoAt b.d (v.N 0) M p ∧ PrimAt c.ψ b.d (v.N 0) p ∧ LastAt c.ψ b.d (vecB b.o b.ζ) (v.N 0) M p) ∧
    (∀ p, p ∉ v.tP → ∃ LL, IsSelfDualC b.L LL ∧ OrthAt b.o M (c.x 0).L LL p) ∧
    (∀ i, ∃ β₀ : GlobalTheory.FinPl.Frame (o.p i) b.V₀ (Fin (c.X 0).rank ⊕ Fin 1), IsSumFrame b.o b.ζ (o.β 0 i) β₀ ∧
      β₀.IsLat M (GlobalTheory.LatPair.gluedS o.q 1 (o.Q 0 i).ker (o.Q 0 i).vec)) ∧
    ∀ i, valuation (G i).k ((G i).q.pr (incA D (star b.ζ ⬝ᵥ b.L.gram *ᵥ b.ζ))) = 1 ∧
      WShape (G i).q b.d b.o b.ζ Lm (fun j => ((((G i).S.ϖ : (G i).kˣ) : (G i).k) ^ (j.1 + 1))⁻¹)
        (fun j => ((((G i).S.ϖ : (G i).kˣ) : (G i).k) ^ (2 * D.R.rS - j.1 + 1))⁻¹)
        (((((G i).S.ϖ : (G i).kˣ) : (G i).k) ^ (D.R.rS + 1))⁻¹) 1 (c.x 0).L

theorem facts {c : Comm D} {v : VCom c} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ι : Type} (o : TDat c k ι) {n : ℕ} (G : Fin n → GLoc v) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) (hc : c.Is) (hS : ShapeOff v o)
    (PP : Fin n → Formalism.L2.DIV.Pl D.host.E) (b : GA D (c.V 0)) (β : GL (Fin (c.V 0).rank) (Lev.EAf D))
    (hloc : ∀ i, LocAt (G i) (PP i) b β) (Λ Lm : Lat (c.V 0)) (hfr : Formalism.L2.DIV.IsFrame β Λ) (hmv : ∀ P, Moves (c.V 0) b Λ Lm P) :
    Facts o G Lm (c.bes 0 D.R.rS h0) :=
  ⟨o.M 0 _ h0, fun p => ⟨((hS.good p).bf 0 _ h0).sdV₀, ((hS.good p).bf 0 _ h0).monoV, ((hS.good p).bf 0 _ h0).prim,
      GlobalTheory.T.lastWittLine_of_besselJacobiLatticesGood D _ hc.std _ _ _ _ _ _ _ p ((hS.good p).bf 0 _ h0)⟩,
    fun p hp => (hS.split p hp).core 0 _ h0, fun i => ⟨_, (hS.glued 0 _ h0 i).sum, (hS.glued 0 _ h0 i).lat⟩,
    fun i => ⟨(G i).hz_unit 0 _ h0, GlobalTheory.LevZero.wShape_of_besFrame_loc (G i) _ h0 Lm
      (GlobalTheory.T.movedLattice_indexZero_normalFrame_component (G i) (PP i) b β (hloc i) ((G i).s + 1) (zero_add _) Λ Lm hfr (hmv _))⟩⟩

theorem sMoves_of_moves {S : HSp D} {t g : GA D S} {Λ L L' M : Lat S} {p : GlobalTheory.FinPl.Pl D} {c : AE D}
    (h : Moves S t Λ L (· = p)) (h' : Moves S t Λ L' (· = p)) (hs : SMoves S c g L M p) : SMoves S c g L' M p := by
  intro y hy
  have := moves_trans (moves_symm h') h y hy
  rw [mul_inv_cancel, mt_one', Matrix.one_mulVec] at this
  exact this.trans (hs y hy)


end GlobalTheory.LevZero.StabMatch

end
