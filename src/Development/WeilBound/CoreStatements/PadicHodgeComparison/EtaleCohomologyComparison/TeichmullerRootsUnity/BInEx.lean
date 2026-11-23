module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.TeichmullerRootsUnity.TUnit
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.AtlasOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.ExistsEpsPeriodTUnit
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.LimSurjFil
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FirstChernCompatibleL
import GroundTheory.PAdicHodge.FontaineLemmaPeriod
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

@[expose] public section



set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison

namespace CrystallineSemistableComparison.crystallineComparison

theorem bInEx : BInEx := by
  intro l _ K _ M hM j
  obtain ⟨d, hA⟩ := GlueB'.atlas_of hM
  obtain ⟨N, hN⟩ := B.main l d j
  obtain ⟨v, -, e⟩ := ACris.exists_periodT_eq_mu_mul_unit (K := ℂ_[l]) (p := l) (untilt_epsilon (p := l))
    untilt_frobeniusEquiv_symm_epsilon_ne_one
  have ht : tA l = (GlueBE.eps l).μ * v := by rw [GlueBE.eps_μ]; exact e
  have hC := B.compat l
  have hup := fun n : ℕ =>
    (hN (B.schFn M.p) (okToOC l K) (GlueBE.eps l) hA.some n).1 true
  refine ⟨⟨2 * N, fun y => ?_, fun x hx => ?_⟩, fun x n => ?_, fun g x n => ?_⟩
  · obtain ⟨x, hx⟩ := GlueBL.lim_surj (GlueB'.βS hC (B.schFn M.p) (okToOC l K) true j) _ v (tA l) N ht hup y
    exact ⟨x, fun n => congrArg (fun z => z.1 n) hx⟩
  · exact GlueBL.lim_inj (GlueB'.βS hC (B.schFn M.p) (okToOC l K) true j) _ v (tA l) N ht hup x (Subtype.ext (funext hx))
  · exact hC.phi (B.schFn M.p) (okToOC l K) n j _
  · exact hC.gal (B.schFn M.p) (okToOC l K) (IntermediateField.fixingSubgroupEquiv K g) (galOC_okToOC _) true n j _

end CrystallineSemistableComparison.crystallineComparison

end
