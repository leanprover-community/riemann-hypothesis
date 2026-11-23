module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChartZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinkZeroOfChartZero
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm

@[expose] public section



section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory.MiTop
theorem linkZero_of_chartZero_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (d : _root_.GlobalTheory.MiTop.BottomData W u), _root_.GlobalTheory.MiTop.ChartAtZeroCondition f → (∀ h₀ : 0 + 2 * D.R.rS + 2 = D.R.m, d.B.lev = f.c.B 0 D.R.rS h₀) → d.b = (show GA D (D.sp.Y 0) from f.g.b 0) → _root_.GlobalTheory.MiTop.LinkVanishes f d := by
  intro D L hT Gi Gl Kc Yd cX ex W u f d hc hl hb n h₀ t φ
  obtain ⟨α₀, h1, h2, h3, -⟩ := hc t
  refine ⟨(h3 φ).1, fun G y v => ?_⟩
  obtain rfl : n = D.R.rS := by
    have : D.R.rS = D.R.m / 2 - 1 := rfl
    omega
  have e : ∀ g : GA D (Yc D 0) → ℂ, trc (Finsupp.single (f.g.b 0) 1) g = rTrans (f.g.b 0) g := fun g => by
    unfold trc
    rw [Finsupp.support_single _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]
  unfold _root_.GlobalTheory.MiTop.BottomData.per Tup.per Tup.perF
  rw [Finset.sum_eq_single α₀ (fun b _ hb => absurd (h1 b) hb) (by simp)]
  beta_reduce
  rw [h2, (h3 φ).2 y, hb]
  exact besLev_per_congr (hl h₀).symm _ HEq.rfl (heq_of_eq (e _))
end GlobalTheory.MiTop
end
