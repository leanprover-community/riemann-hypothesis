module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.MonomialOfComm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.MonomialRed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.PermChar
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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

open IsLocalRing Polynomial Matrix UpperTheory.V

theorem UpperTheory.V.Ws.exists_noncommuting_images_in_finiteIndex_normal_subgroup :
    ∀ (K k B G : Type) [Field K] [IsAlgClosed K] [Field k] [CommRing B] [Group G] (r : G →* Matrix (Fin 4) (Fin 4) K)
      (j : B →+* K) (φ : B →+* k) (χ : Fin 4 → G →* kˣ), Function.Injective j →
      (∀ g, ∃ p : B[X], p.map j = (r g).charpoly ∧ p.map φ = ∏ i, (X - C (χ i g : k))) →
      Submodule.span K (Set.range r) = ⊤ → (∃ s t, ∀ n : ℕ, 0 < n → n ≤ 4 → (χ s / χ t) ^ n ≠ 1) →
      ∀ (Z : Subgroup G) [Z.Normal] (u : G), u ∈ Z → (∀ d : ℕ, 0 < d → (r u ^ d).charpoly.Separable) →
      ∀ N : Subgroup Z, N.Normal → N.FiniteIndex → ∃ g ∈ N, ∃ h ∈ N, r g * r h ≠ r h * r g := by
  intro K k B G _ _ _ _ _ r j φ χ hj hpoly hspan hst Z _ u huZ hsep N hN hfi
  haveI := hN
  by_contra hcon
  push_neg at hcon
  have hd0 : 0 < N.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  let N' : Subgroup G := N.map Z.subtype
  have hcore : u ^ N.index ∈ N'.normalCore := by
    show ∀ c : G, c * u ^ N.index * c⁻¹ ∈ N'
    intro c
    have hz : c * u * c⁻¹ ∈ Z := ‹Z.Normal›.conj_mem u huZ c
    have hp := N.pow_index_mem ⟨c * u * c⁻¹, hz⟩
    refine ⟨_, hp, ?_⟩
    simp [conj_pow]
  have hcomm : ∀ g ∈ N'.normalCore, ∀ h ∈ N'.normalCore, r g * r h = r h * r g := by
    intro g hg h hh
    obtain ⟨g', hg', rfl⟩ := N'.normalCore_le hg
    obtain ⟨h', hh', rfl⟩ := N'.normalCore_le hh
    exact hcon g' hg' h' hh'
  obtain ⟨b, π, _, hmono, htrans⟩ := AlgebraTools.monomialOfComm K G 4 r hspan N'.normalCore hcomm
    ⟨u ^ N.index, hcore, by rw [map_pow]; exact hsep _ hd0⟩
  have hred := AlgebraTools.monomialRed K k B G 4 r j φ χ hj hpoly b π hmono htrans
  obtain ⟨s, t, hst'⟩ := hst
  have hle : π.ker ≤ (χ s / χ t).ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    simp [hred g hg s t]
  obtain ⟨h1, h2⟩ := AlgebraTools.permChar G k π (χ s / χ t) hle
  exact hst' _ h1 h2 (pow_orderOf_eq_one _)
