module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BareStatementOfDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDivStageOfPk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSStageTrue
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FittingLaterStagesRowIsConstructionStateStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasBareOfHasPk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroColumnsClassSumFormPosDef
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.Mem.R3.Rw.Bare
open GlobalTheory.MemN GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.Mem.TypePl Polynomial
attribute [local instance] GlobalTheory.Mem.Top.factType
variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
end GlobalTheory.Mem.R3.Rw.Bare
namespace GlobalTheory.HeightCounting.Up
open Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice GlobalTheory.Mem.R3.Rw.Bare

theorem minimal_ktype_of_local_components_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → GlobalTheory.Published.DiscreteSeriesExists → BareK := by
  intro hP hD
  refine StepW.of_all fun K B' f' T' w' hO _ _ P' X f hB hf hg => ?_
  obtain ⟨B₀, C₀, W₀, V₀, S₀, N₀, G₀⟩ := X
  cases B'
  cases B₀
  dsimp only at hB
  subst hB
  obtain rfl := eq_of_heq hf
  obtain ⟨N, hE, hN, hN', hL, h1, h2, h3, h4, h5, h6⟩ := exists_bare_over P' N₀.nd N₀.naut hg.pl N₀.toLocStage
  obtain ⟨V, hV, -, -, hη, -, hB⟩ := exists_divStage_of_pk _ w'.C (Gc _ w'.px) P'.q.p P'.q.e P'.q.W₀ P'.q.n
    (fun _ _ => 0) (fun _ _ => le_rfl) (frames_unit P'.q.t) (fun u => ((w'.C.fm u).lat 0).L) (fun _ => 0)
    (6 * K.s.x ^ (-K.C.P.CF))
  obtain ⟨S, -⟩ := GlobalTheory.Mem.SProv.exists_sStage_true K _ w'.C (P'.q.W (fun _ _ => 0) fun _ _ => le_rfl) P'.Z₀.G.cd hO
    (GlobalTheory.Mem.Df.cols_pos w'.I w'.ok w'.pins w'.l P'.hX) (rows_le P'.q.t)
  obtain ⟨x, hx⟩ := GlobalTheory.T.fittingLaterStages_row_is_constructionState GlobalTheory.weilRepresentationUnitaryPair hD hP.hc hP.decay K _ _ T' w' P' ⟨_, _, V, S, N, P'.Z₀.G⟩
    ⟨hV, hN, (hN' V S P'.Z₀.G).1, (hN' V S P'.Z₀.G).2⟩ rfl hη (fun hr => hB hr)
  have hDx : Dof x = (w'.st (RowPk.Over.Z (q := P'.q) ⟨_, _, V, S, N, P'.Z₀.G⟩)).toD7 := by
    unfold Dof
    rw [hx]
  have hE' : IsEmpty x.o.N.nd.Loc := by
    rw [hx]
    exact hE
  refine ⟨x, hE', ?_⟩
  rw [hDx]
  exact ⟨⟨rfl, HEq.rfl, congrArg LocStage.loc hL.symm, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm⟩, h6.symm⟩
end GlobalTheory.HeightCounting.Up
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.bareK_of_discreteSeriesExists : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → GlobalTheory.Published.DiscreteSeriesExists → BareK := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.minimal_ktype_of_local_components_alt | exact _root_.GlobalTheory.HeightCounting.Up.minimal_ktype_of_local_components_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.minimal_ktype_of_local_components_alt <;> assumption)
end
end
