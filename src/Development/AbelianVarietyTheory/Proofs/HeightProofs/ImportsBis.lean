module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.MiscellaneousLemmas

open scoped TensorProduct

theorem main : ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E] [inst_5 : StarRing E] (V : Formalism.BasicNotions.HSpace E) {k : ℕ} (x : Fin k → Formalism.BasicNotions.HSpace.V V), (∀ w ∈ Formalism.BasicNotions.HSpace.L0 V, ∃ (n : Fin k → ℤ), w = ∑ j : Fin k, n j • x j) → ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), ∀ y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc V v, ∃ (a : Fin k → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v), (∀ (j : Fin k), a j ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v) ∧ ∀ (i : Fin (Formalism.BasicNotions.HSpace.rank V)), y i = ∑ j : Fin k, a j ⊗ₜ[F] ((Module.Basis.repr (Formalism.BasicNotions.HSpace.frame V) : Formalism.BasicNotions.HSpace.V V → Fin (Formalism.BasicNotions.HSpace.rank V) →₀ E) (x j) : Fin (Formalism.BasicNotions.HSpace.rank V) → E) i := by
  intro F E _ _ _ _ _ _ V k x hx v y hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, w, hw, rfl⟩ := hy
    obtain ⟨n, rfl⟩ := hx w hw
    refine ⟨fun j => n j • a, fun j => zsmul_mem ha _, fun i => ?_⟩
    change a ⊗ₜ[F] (V.frame.repr (∑ j, n j • x j) i) = _

    simp only [map_sum, map_zsmul, Finsupp.finsetSum_apply, Finsupp.smul_apply, TensorProduct.tmul_sum, TensorProduct.smul_tmul]
  | zero => exact ⟨0, fun j => zero_mem _, fun i => by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, h⟩ := hy
    obtain ⟨b, hb, h'⟩ := hz
    exact ⟨a + b, fun j => add_mem (ha j) (hb j), fun i => by
      simp [h i, h' i, TensorProduct.add_tmul, Finset.sum_add_distrib]⟩
  | neg y _ hy =>
    obtain ⟨a, ha, h⟩ := hy
    exact ⟨-a, fun j => neg_mem (ha j), fun i => by
      simp [h i, TensorProduct.neg_tmul, Finset.sum_neg_distrib]⟩

end GlobalTheory.MiscellaneousLemmas
