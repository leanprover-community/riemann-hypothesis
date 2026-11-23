module

public import Formalism.LocalToGlobal.Divisibility.QLocTied
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NrmAbsOfValuationEqExp
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins

@[expose] public section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.Mem.NrmCompl

theorem isNrm_nrmAbs {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) : IsNrm P (nrmAbs P) := by
  intro x
  refine ⟨fun hx => (nrmAbs_eq_one_iff P (x : P.adicCompletion L)).2 hx, fun hx => ?_⟩
  have h : Valued.v (x : P.adicCompletion L) = WithZero.exp (-1 : ℤ) := hx
  rw [nrmAbs_of_valuation_eq_exp P h, _root_.zpow_neg_one]
  rfl

theorem exists_isNrm : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)),
    ∃ nrm : AbsoluteValue (P.adicCompletion L) ℝ, IsNrm P nrm :=
  fun _ _ _ P => ⟨nrmAbs P, isNrm_nrmAbs P⟩

end GlobalTheory.Mem.NrmCompl
