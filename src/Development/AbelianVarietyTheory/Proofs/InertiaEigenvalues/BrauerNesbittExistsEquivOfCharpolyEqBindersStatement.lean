module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RepresentationTheory.Semisimple
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BrauerNesbittExistsEquivOfCharpolyEqHypotheses
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

open scoped BigOperators

theorem _root_.GlobalTheory.T.brauerNesbitt_exists_equiv_of_charpoly_eq' : ∀ {k Γ V W : Type} [Field k] [Monoid Γ] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] [FiniteDimensional k V] [FiniteDimensional k W] (ρ : Representation k Γ V) (σ : Representation k Γ W), ρ.IsSemisimpleRepresentation → σ.IsSemisimpleRepresentation → (∀ a : MonoidAlgebra k Γ, LinearMap.charpoly (ρ.asAlgebraHom a) = LinearMap.charpoly (σ.asAlgebraHom a)) → ∃ e : V ≃ₗ[k] W, ∀ g v, e (ρ g v) = σ g (e v) := by
  first | exact @GlobalTheory.CharpolyIso.exists_equiv_of_charpoly_eq' | exact GlobalTheory.CharpolyIso.exists_equiv_of_charpoly_eq' | (intros; apply GlobalTheory.CharpolyIso.exists_equiv_of_charpoly_eq' <;> assumption)
