module

public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory

theorem exists_inverse_conj_mem_closure_of_isCompact :
    ∀ (X : Type) [Monoid X] [TopologicalSpace X] [ContinuousMul X] [T2Space X] (H C : Set X),
      IsCompact C → ∀ g : X, (∀ W ∈ 𝓝 g, ∃ c ∈ C, ∃ c' ∈ C, c * c' = 1 ∧ c' * c = 1 ∧
        ∃ w ∈ W, c * w * c' ∈ H) →
      ∃ c ∈ C, ∃ c' ∈ C, c * c' = 1 ∧ c' * c = 1 ∧ c * g * c' ∈ closure H := by
  intro X _ _ _ _ H C hC g hW
  let K : Set (X × X) := (C ×ˢ C) ∩ {p | p.1 * p.2 = 1 ∧ p.2 * p.1 = 1}
  have hK : IsCompact K := by
    refine (hC.prod hC).inter_right ?_
    exact (isClosed_eq (continuous_fst.mul continuous_snd) continuous_const).inter
      (isClosed_eq (continuous_snd.mul continuous_fst) continuous_const)
  by_contra hne
  push_neg at hne
  have hcont : Continuous fun z : X × (X × X) => z.2.1 * z.1 * z.2.2 :=
    ((continuous_snd.fst).mul continuous_fst).mul continuous_snd.snd
  have hP : ∀ y ∈ K, ∀ᶠ z : X × (X × X) in 𝓝 (g, y), z.2.1 * z.1 * z.2.2 ∈ (closure H)ᶜ := by
    intro y hy
    apply hcont.continuousAt.preimage_mem_nhds
    apply isClosed_closure.isOpen_compl.mem_nhds
    exact hne y.1 hy.1.1 y.2 hy.1.2 hy.2.1 hy.2.2
  have hev := hK.eventually_forall_of_forall_eventually (x₀ := g)
    (P := fun w (y : X × X) => y.1 * w * y.2 ∈ (closure H)ᶜ) hP
  obtain ⟨c, hc, c', hc', h1, h2, w, hw, hH⟩ := hW _ hev
  exact hw (c, c') ⟨⟨hc, hc'⟩, h1, h2⟩ (subset_closure hH)

end GlobalTheory
