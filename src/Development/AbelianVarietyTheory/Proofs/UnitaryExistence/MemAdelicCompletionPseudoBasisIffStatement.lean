module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemAdelicCompletionPseudoBasisIff
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

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.mem_adelicCompletion_pseudoBasis_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (e : Module.Basis (Fin n) E (Fin n → E)) (cI : Fin n → FractionalIdeal (𝓞 E)⁰ E), (∀ v, v ∈ L ↔ ∀ a, e.repr v a ∈ cI a) → ∀ z : Fin n → RA F E, (∑ a, z a • fv F (e a)) ∈ (hat F (L : Set (Fin n → E))) ↔ ∀ a, z a ∈ hat1 F (cI a : Set E) := by
  first | exact @GlobalTheory.AdLat.mem_hat_pseudoBasis_iff | exact GlobalTheory.AdLat.mem_hat_pseudoBasis_iff | (intros; apply GlobalTheory.AdLat.mem_hat_pseudoBasis_iff <;> assumption)
