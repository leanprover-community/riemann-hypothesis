module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KernelRankBoundNormValuation
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

open NumberField

theorem _root_.GlobalTheory.T.exists_free_basis_of_kernel_rank_le_norm_valuation : ∀ (E : Type) [Field E] [NumberField E] (k W : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] [AddCommGroup W] [Module k W] [FiniteDimensional k W] (r : ℕ) (ρ : 𝓞 E →+* Module.End k W), (∀ a : 𝓞 E, (ρ a).charpoly = ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom k)) ^ r) → (∀ a : 𝓞 E, a ≠ 0 → Module.finrank k (LinearMap.ker (ρ a)) ≤ r * padicValNat p (Algebra.norm ℤ a).natAbs) → ∃ x : Fin r → W, LinearIndependent k (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ρ (RingOfIntegers.basis E q.2) (x q.1)) ∧ Submodule.span k (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ρ (RingOfIntegers.basis E q.2) (x q.1)) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.lemF_algebra | exact GlobalTheory.CompanionTheory.Ar.Flat.lemF_algebra | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.lemF_algebra <;> assumption)
