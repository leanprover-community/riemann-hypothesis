module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Instances.ZMod
public import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModLThreeCocycleCondition
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
import Formalism.ConjugateSelfDual.Statement
import Formalism.GaloisCohomology.StatementLoc

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

theorem _root_.GlobalTheory.T.mod_l_three_cocycle_condition : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [ContinuousMul Γ] (ρ : Representation ℤ_[l] Γ ℤ_[l]), ContAction ρ → ∀ (ρ1 : Representation (ZMod (l ^ 1)) Γ (ZMod (l ^ 1))), (∀ g x, PadicInt.toZModPow 1 (ρ g x) = ρ1 g (PadicInt.toZModPow 1 x)) → (∀ c : Γ × Γ × Γ → ZMod (l ^ 1), Continuous c → (∀ g h k m, ρ1 g (c (h, k, m)) - c (g * h, k, m) + c (g, h * k, m) - c (g, h, k * m) + c (g, h, k) = 0) → ∃ u : Γ × Γ → ZMod (l ^ 1), Continuous u ∧ ∀ g h k, ρ1 g (u (h, k)) - u (g * h, k) + u (g, h * k) - u (g, h) = c (g, h, k)) → ∀ (r : ℕ) (ρr : Representation (ZMod (l ^ r)) Γ (ZMod (l ^ r))), (∀ g x, PadicInt.toZModPow r (ρ g x) = ρr g (PadicInt.toZModPow r x)) → ∀ y ∈ Z2 ρr, ∃ z ∈ Z2 ρ, ∀ p, PadicInt.toZModPow r (z p) = y p := by
  first | exact @GlobalTheory.PadicCocycleLift.twoCocycle_lift | exact GlobalTheory.PadicCocycleLift.twoCocycle_lift | (intros; apply GlobalTheory.PadicCocycleLift.twoCocycle_lift <;> assumption)
