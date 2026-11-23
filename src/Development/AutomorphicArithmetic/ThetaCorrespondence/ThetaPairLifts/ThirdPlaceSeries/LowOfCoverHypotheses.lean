module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerBoundOfAllEstimates
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

noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CovTop.LowCover
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
theorem low_of_cover_hypotheses : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.LowDefectCondition → _root_.GlobalTheory.CovTop.DeepExistence → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.RingCondition → _root_.GlobalTheory.CovTop.MapsCondition → _root_.GlobalTheory.CovTop.CoverRank → _root_.GlobalTheory.CovTop.MinimalGenerator → _root_.GlobalTheory.CovTop.FlatnessCondition → _root_.GlobalTheory.CovTop.UniformLowerBound → _root_.GlobalTheory.CovTop.LiftLowBound := by
  intro hS hD hE hG hR hM hK hGm hF hU
  refine Closed.imp (((((((((hS.and hD).and hE).and hG).and hR).and hM).and hK).and hGm).and hF).and hU) ?_
  intro eps Fm CH _ hh
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨CS, -, aS⟩, CD, -, aD⟩, _, -, aE⟩, _, -, aG⟩, _, -, aR⟩, _, -, aM⟩, _, -, aK⟩, _, -, aGm⟩,
    CF, hCF, aF⟩, CU, hCU, aU⟩ := hh
  refine ⟨max CD (2 * (CF + CU) + 9), le_max_of_le_right (by linarith), ?_⟩
  obtain ⟨x0, h⟩ := ((((((((aS.and aD).and aE).and aG).and aR).and aM).and aK).and aGm).and aF).and aU
  refine ⟨x0, fun x hx hle ι p hp i => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨bS, bD⟩, bE⟩, bG⟩, bR⟩, bM⟩, bK⟩, bGm⟩, bF⟩, bU⟩ := h x hx hle ι p hp
  have hS' := bS i
  have hE0 : 0 ≤ unitE p := by obtain ⟨a, b, -⟩ := hS'; linarith
  rcases (Nat.succ_le_of_lt i.isLt).eq_or_lt with heq | hlt
  · exact lowAt_mono (bD i heq) (le_max_left _ _) hE0
  · obtain ⟨Y, hY⟩ := bE i hlt
    exact lowAt_mono (lowAt_of_cover p i _ CS CF CU hCF hCU hS' Y (bG i hlt Y hY) (bR i hlt Y hY) (bM i hlt Y hY)
      (bK i hlt Y hY) (bGm i hlt Y hY) (bF i hlt Y hY) (bU i hlt Y hY)) (le_max_right _ _) hE0
end GlobalTheory.CovTop.LowCover
end
end
