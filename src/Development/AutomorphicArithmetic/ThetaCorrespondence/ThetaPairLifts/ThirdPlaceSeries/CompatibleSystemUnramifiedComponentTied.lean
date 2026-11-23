module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTied
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.E0ReadOfEigenLabeling
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemOfForall
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
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading
noncomputable section
namespace GlobalTheory.HeightCounting.Up.IdempotentAdelicReading
theorem unramified_component_at_member_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ T w Z Wt _ t nch n c => ∀ (hC : t.r.z.R.C = TC.cf w.I w.l Z) (Xd : DivX (w.D Z)) (E : EigIdx (w.D Z) Xd) (labPi : E.Pi → (famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).A.fam.base.Ix) hb htup hg hf, GlobalTheory.NRows.GoodIdempotentReadsAsGoodTypeProjector (realOfRead t.r.z.R.toRealDat t.r.z.F.lv2 t.r.Y n.tp hC Xd E labPi hb htup hg hf) := by
  intro _ hL
  exact _root_.GlobalTheory.HeightCounting.Up.CoefficientAgreement.atMem_of_forall' fun _ _ _ _ _ _ _ _ t _ _ _ _ _ _ _ _ _ _ _ =>
    goodIdempotent_eq_goodProjector_adelicReading _ _ _ _ _ _ _ _ _ _ _ _ t.r.intersectionNumber_baseChange.ok.ok2
end GlobalTheory.HeightCounting.Up.IdempotentAdelicReading
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading

theorem _root_.GlobalTheory.T.good_idempotent_reads_as_type_projector_at_member : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ T w Z Wt _ t nch n c => ∀ (hC : t.r.z.R.C = TC.cf w.I w.l Z) (Xd : DivX (w.D Z)) (E : EigIdx (w.D Z) Xd) (labPi : E.Pi → (famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).A.fam.base.Ix) hb htup hg hf, GlobalTheory.NRows.GoodIdempotentReadsAsGoodTypeProjector (realOfRead t.r.z.R.toRealDat t.r.z.F.lv2 t.r.Y n.tp hC Xd E labPi hb htup hg hf) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.IdempotentAdelicReading.unramified_component_at_member_alt | exact _root_.GlobalTheory.HeightCounting.Up.IdempotentAdelicReading.unramified_component_at_member_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.IdempotentAdelicReading.unramified_component_at_member_alt <;> assumption)
end
end
