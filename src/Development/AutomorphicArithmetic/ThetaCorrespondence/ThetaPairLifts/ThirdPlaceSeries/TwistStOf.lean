module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TupleReadBaseTupleEqFamily
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section



section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BigOn.TwistBoundAtPlace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
end Point
theorem twistSt_of_alt (hE : _root_.GlobalTheory.BigOn.ExportedStatement) (hG : _root_.GlobalTheory.BigOn.GeometricStatement')
    (hK : _root_.GlobalTheory.BigOn.ForallRecordObjects fun _ _ _ _ _ _ O => GlobalTheory.TraceClassRank.RankAtPlaces O) : _root_.GlobalTheory.BigOn.TwistStatement' := by
  obtain ⟨a, ha, H⟩ := (hE.and hG).and hK
  refine ⟨a, ha, fun e he hle => ?_⟩
  obtain ⟨K, hK'⟩ := H e he hle
  refine ⟨K, fun Fm CH hc hL => ?_⟩
  obtain ⟨⟨⟨x1, E1⟩, ⟨c1, G1⟩⟩, ⟨c2, K1⟩⟩ := hK' Fm CH hc hL
  obtain ⟨x0, T0⟩ := hc.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨max c1 c2, fun c hcC hb => ?_⟩
  obtain ⟨x2, G2⟩ := G1 c ((le_max_left _ _).trans hcC) hb
  obtain ⟨x3, K2⟩ := K1 c ((le_max_right _ _).trans hcC) hb
  refine ⟨max (max x0 x1) (max x2 x3), fun x hx hle i p hp hM r O hR => ?_⟩
  have h0 : x0 ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hle)
  have h1 : x1 ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hle)
  have h2 : x2 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hle)
  have h3 : x3 ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hle)
  obtain ⟨-, N0, S, hTG⟩ := T0 x h0 hx i
  exact hasTwistBound_at p hR (E1 x hx h1 i p hp hM) (G2 x hx h2 i p hp hM r O hR).1 (K2 x hx h3 i p hp hM r O hR) hTG
end GlobalTheory.BigOn.TwistBoundAtPlace
end
end
