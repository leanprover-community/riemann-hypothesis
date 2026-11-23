module

public import GroundTheory.HeightsAndTheta.Heights.HermitianTensor
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PDiagonalChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.ArithDegree

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField TensorProduct ComplexAt

noncomputable section

namespace FibreMahlerForms

section Dual

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*} [Fintype ι]

end Dual

section Mahler

variable {d : ℕ}

end Mahler

section Fibre

variable {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (𝓞 F) W]
  [Module.Finite (𝓞 F) W] [Module.Projective (𝓞 F) W]

theorem finrank_fibreSpace (h : HermitianMetric F W) (σ : F →+* ℂ) :
    Module.finrank ℂ (FibreSpace h σ) = Module.finrank (𝓞 F) W := by
  obtain ⟨s, hs⟩ := exists_linearIndependent_fin (K := F) (E := W)
  let b := Module.Basis.mk (linearIndependent_fibreVec h σ hs)
    (LatticeLemmas.span_fibreVec_eq_top h σ hs (Fintype.card_fin _)).ge
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin]

variable {K : Type} [Field K] [NumberField K] [Algebra F K]

end Fibre

end FibreMahlerForms


end

end GroundTheory.Heights₂.Heights
