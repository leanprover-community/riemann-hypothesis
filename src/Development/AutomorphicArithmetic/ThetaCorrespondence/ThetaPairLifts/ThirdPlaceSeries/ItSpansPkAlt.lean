module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsKFinOfMemKfin
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteSpanLeSpanRealIntertwinerValues
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Core.Mi.SpanY
theorem itSpans_pk_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ j, j + 1 < D.R.m → GlobalTheory.Core.Mi.ItSpans ((_root_.GlobalTheory.Fam.pk_z W).MY j) ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ItY j) := by
  intro hDS hHC D L hT Gi Gl Kc Yd cX ex W hP j hj
  have hC := hP.bot.hyp.2.2.2.1
  have hok := GlobalTheory.Chain.StepVac.stepsOK _ _ _ _ _ _ _ hC.lev hC.models.inf hC.chain.ωY hC.chain.ωX hC.chain.vY hC.chain.vX
  obtain ⟨hw, hv⟩ := hok.1 W.P.A3.A.μ0 ⟨j, by omega⟩ hj
  have hle := GlobalTheory.ItOnto.kfinSpan_le_span_it hDS hHC D _ _ _ _ ((_root_.GlobalTheory.Fam.pk_z W).MY j) ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).θ (_root_.GlobalTheory.Fam.pk_z W).ψ _ _
    ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j) ((_root_.GlobalTheory.Fam.pk_z W).vY W.P.A3.A.μ0 j) ((_root_.GlobalTheory.Fam.pk_z W).ItY j) hC.models.inf hw hv (hC.chain.ItY W.P.A3.A.μ0 j hj)
  intro v hv
  have hv' := hle (Submodule.subset_span ⟨v, fun τ => Submodule.subset_span (hv τ), rfl⟩)
  refine (Submodule.span_le.2 ?_) hv'
  rintro w ⟨P, u, hu, rfl⟩
  have hu' : u ∈ Submodule.comap ((_root_.GlobalTheory.Fam.pk_z W).ItY j P) (Submodule.span ℂ
      {x | ∃ (P : PolF D (Yc D (j + 1)).rank (Yc D j).rank) (y : ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)).Vec), KVecP ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) y ∧
        x = (_root_.GlobalTheory.Fam.pk_z W).ItY j P (PiTensorProduct.tprod ℂ y)}) := by
    refine (Submodule.span_le.2 ?_) hu
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨P, y, fun τ => GlobalTheory.Core.Mi.StepSpans.isKFin_of_mem_kfin _ _ (hy τ), rfl⟩
  exact hu'
end GlobalTheory.Core.Mi.SpanY
end
end
