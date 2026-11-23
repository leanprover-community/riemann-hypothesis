module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiMeasureUnitriangularCoordinates
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
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

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.QKAvg

theorem isClosed_radN : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t),
    IsClosed (radN d : Set (GlobalTheory.RegSW.stab d)) := by
  intro D B W t d
  have e : (radN d : Set (GlobalTheory.RegSW.stab d)) =
      (Subtype.val : GlobalTheory.RegSW.stab d → GA D B) ⁻¹' (GlobalTheory.MixPer.radX d : Set (GA D B)) := by
    ext q
    constructor
    · rintro ⟨c, b, h⟩
      exact (GlobalTheory.MixPer.Decomp.mem_radX_iff d).2 ⟨b, c, h.trans (d.nC_mul_nB b c)⟩
    · intro h
      obtain ⟨b, c, h⟩ := (GlobalTheory.MixPer.Decomp.mem_radX_iff d).1 h
      exact ⟨c, b, h.trans (d.nC_mul_nB b c).symm⟩
  rw [e]
  exact (GlobalTheory.JacMeas.isClosed_radX d).preimage continuous_subtype_val

end GlobalTheory.CompanionTheory.QKAvg
