module

public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsInvariantSubspace
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

private theorem UpperTheory.Reformulated.B.Gc1.kset_subset {n : ℕ} (ε : Fin n → Bool) :
    PI.UpqRep.Kset ε ⊆ PI.UpqRep.UJset ε := by
  intro g hg
  have h1 : star g * g = 1 := (Matrix.mem_unitaryGroup_iff' ).1 hg.1
  show g.conjTranspose * PI.UpqRep.Jm ε * g = PI.UpqRep.Jm ε
  rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, h1, Matrix.one_mul]

theorem UpperTheory.Reformulated.B.Gc1.kFinStab :
    CompanionTheory.D.DSIC.KFinStab := by
  intro n ε H _ _ σ S E _ hS
  obtain ⟨V₀, h1, h2⟩ := UpperTheory.exists_invariant_subspace H (Matrix (Fin n) (Fin n) ℂ) (Fin n × Fin n) (PI.UpqRep.Kset ε)
    (fun g => (σ g : H →ₗ[ℂ] H)) S (fun p => E p.1 p.2)
    (fun g p q => g q.1 p.1 * g⁻¹ p.2 q.2)
    (fun g hg v hv => hS.stab g (UpperTheory.Reformulated.B.Gc1.kset_subset ε hg) v hv)
    (fun g hg p v w hw => by
      rw [Fintype.sum_prod_type]
      exact hS.conj g (UpperTheory.Reformulated.B.Gc1.kset_subset ε hg) p.1 p.2 v w hw)
  exact ⟨V₀, h1, fun a b => h2 (a, b)⟩
