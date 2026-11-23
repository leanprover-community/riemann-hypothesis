module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Instances.ZMod
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsZmodPowCoboundaryOfRationalCoboundary
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.exists_zmod_pow_coboundary_of_rational_coboundary' : ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (l : ℕ) [Fact l.Prime] (ε : Γ → ℤ_[l]) (O L : Type) [CommRing O] [Algebra ℤ_[l] O] [Field L] [TopologicalSpace L] [IsTopologicalRing L] (ι : O →+* L), Function.Injective ι → IsOpen (Set.range ι) → (l : L) ≠ 0 → (∀ x : L, ∃ n : ℕ, (l : L) ^ n * x ∈ Set.range ι) → ∀ (β : O →+ ZMod (l ^ 1)) (z : Γ → Γ → O) (f : Γ → L), Continuous f → (∀ g h, ι (z g h) = ι (algebraMap ℤ_[l] O (ε g)) * f h - f (g * h) + f g) → ∃ (n : ℕ) (a : Γ → ZMod (l ^ (n + 1))), Continuous a ∧ ∀ g h, PadicInt.toZModPow (n + 1) (ε g) * a h - a (g * h) + a g = ((l ^ n * (β (z g h)).val : ℕ) : ZMod (l ^ (n + 1))) := by
  first | exact @GlobalTheory.exists_zmod_pow_coboundary_of_rational_coboundary | exact GlobalTheory.exists_zmod_pow_coboundary_of_rational_coboundary | (intros; apply GlobalTheory.exists_zmod_pow_coboundary_of_rational_coboundary <;> assumption)
