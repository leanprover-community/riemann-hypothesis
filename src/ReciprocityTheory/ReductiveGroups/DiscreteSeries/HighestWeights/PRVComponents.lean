module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary
public import Formalism.RealPlaceAnalysis.StatementKT
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PRVComponents.CompactRelationsApplyComm
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PRVComponents.ParthasarathyTensorMatrix
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem parthasarathy_tensor_matrix (ε : Fin n → Bool) {M : Type*} [AddCommGroup M] [Module ℂ M]
    {F : Fin n → Fin n → Module.End ℂ M} (hF : Formalism.REAL.KRel ε F)
    {Λ : Fin n → ℝ} {V : Submodule ℂ M} (hV : IsKIrrHW ε F Λ V)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Fin n → Fin n → Matrix ι ι ℂ} (hG : Formalism.REAL.KRel ε G)
    (hGu : ∀ a b, ε a = ε b → G b a = (G a b)ᴴ)
    {ν : Fin n → ℝ} {f : ι → ℂ} (hf0 : f ≠ 0) (hfw : ∀ a, G a a *ᵥ f = ((ν a : ℝ) : ℂ) • f)
    (hfl : ∀ a b, b < a → ε a = ε b → G a b *ᵥ f = 0)
    (hdom : ∀ a b, a < b → ε a = ε b → (Λ + ν) b ≤ (Λ + ν) a) :
    ∃ x : ι → M, (∀ i, x i ∈ V) ∧ x ≠ 0 ∧
      (∀ a i, F a a (x i) + ∑ j, G a a i j • x j = (((Λ + ν) a : ℝ) : ℂ) • x i) ∧
      ∀ a b, a < b → ε a = ε b → ∀ i, F a b (x i) + ∑ j, G a b i j • x j = 0 :=
  parthasarathy_tensor_matrix_alt ε hF hV hG hGu hf0 hfw hfl hdom

theorem kIrrHW_int (ε : Fin n → Bool) {M : Type*} [AddCommGroup M] [Module ℂ M]
    {F : Fin n → Fin n → Module.End ℂ M} (hF : Formalism.REAL.KRel ε F) {Λ : Fin n → ℝ} {V : Submodule ℂ M}
    (hV : IsKIrrHW ε F Λ V) : ∀ a b, a < b → ε a = ε b → ∃ m : ℕ, Λ a - Λ b = m :=
  kIrrHW_int' ε hF hV

end ReciprocityTheory.ChartRestriction.DS.HW
