module

public import Formalism.LocalRingCardinality.DataSpaces
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPositiveAdd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameOfHasSignature
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.StdDefinite

open GlobalTheory.AutInhab

theorem cmData_maximalRealSubfield {K : Type} [Field K] [NumberField K] [StarRing K]
    (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) : Formalism.BasicNotions.CMData (maximalRealSubfield K) K := by
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hne : ∃ z : K, star z ≠ z := by
    by_contra hcon
    push Not at hcon
    haveI := hK.1
    refine IsTotallyComplex.complexEmbedding_not_isReal σ ?_
    rw [ComplexEmbedding.isReal_iff]
    ext z
    rw [ComplexEmbedding.conjugate_coe_eq, ← hK.2.1, hcon]
  haveI : IsCMField K := GlobalTheory.LeastExponentCompare.isCMField_of_conj K star hK.2.1 hne
  refine ⟨hK, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _, fun a => ⟨fun h => ?_, ?_⟩⟩
  · refine ⟨⟨a, fun φ => ?_⟩, rfl⟩
    have := hK.2.1 φ a
    rw [h] at this
    exact this.symm
  · rintro ⟨b, rfl⟩
    apply σ.injective
    rw [hK.2.1]
    exact b.2 σ

end GlobalTheory.StdDefinite
