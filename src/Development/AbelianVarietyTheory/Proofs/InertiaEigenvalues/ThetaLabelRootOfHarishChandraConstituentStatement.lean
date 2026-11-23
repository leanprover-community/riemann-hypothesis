module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLabelRootOfHarishChandraConstituent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.thetaLabel_root_of_harishChandraConstituent : ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (r a c : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (u : ZMod p) (f : Polynomial (ZMod p)) (ψ : GlobalTheory.GLq.Gn p r → ℂ) (α : GlobalTheory.GLq.Gn p (a + 1) → ℂ) (β : GlobalTheory.GLq.Gn p c → ℂ) (σ : GlobalTheory.GLq.Gn p a → ℂ), r = a + 1 + c → GlobalTheory.GLq.IsIrr ψ → GlobalTheory.GLq.IsIrr α → GlobalTheory.GLq.IsIrr β → GlobalTheory.GLq.IsIrr σ → GlobalTheory.GLq.HasLabel L ψ f → GlobalTheory.GLp.IsCharLab L θ u → GlobalTheory.GLq.ip ψ (GlobalTheory.GLq.hc (a + 1) c α β r) ≠ 0 → GlobalTheory.GLq.ip α (GlobalTheory.GLq.hc a 1 σ (fun y : GlobalTheory.GLq.Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (a + 1)) ≠ 0 → f.IsRoot u := by
  first | exact @GlobalTheory.GLq.DetSplit.root_of_constituent | exact GlobalTheory.GLq.DetSplit.root_of_constituent | (intros; apply GlobalTheory.GLq.DetSplit.root_of_constituent <;> assumption)
