module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
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

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.prokerPL :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (I : Type) [Group I] [TopologicalSpace I] [IsTopologicalGroup I] (f : I →* Γ) (H : Subgroup Γ), Continuous f → (∀ g, f g ∈ H) → ∀ g ∈ GlobalTheory.TameQuot.proKer l I, f g ∈ PL l H := by
  intro l _ Γ _ _ _ _ _ I _ _ _ f H hf hfH g hg
  unfold PL
  simp only [Subgroup.mem_iInf]
  intro U hU
  let φ : I →* Γ ⧸ U.toSubgroup := (QuotientGroup.mk' U.toSubgroup).comp f
  haveI : Finite (Γ ⧸ U.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ U.isOpen
  have hp : IsPGroup l φ.range := by
    rintro ⟨y, x, rfl⟩
    obtain ⟨e, he⟩ := hU (f x) (hfH x)
    refine ⟨e, Subtype.ext ?_⟩
    show φ x ^ l ^ e = 1
    rw [← map_pow]
    show (QuotientGroup.mk (f (x ^ l ^ e)) : Γ ⧸ U.toSubgroup) = 1
    rw [QuotientGroup.eq_one_iff, map_pow]
    exact he
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hp
  have hker : φ.ker = U.toSubgroup.comap f := by
    ext x
    simp [φ, QuotientGroup.eq_one_iff]
  have hopen : IsOpen (φ.ker : Set I) := by
    rw [hker]
    exact U.isOpen.preimage hf
  have h2 := GlobalTheory.TameQuot.mem_proKer.1 hg φ.ker inferInstance hopen
    ⟨n, by rw [Subgroup.index_ker, hn]⟩
  rw [hker] at h2
  exact h2
