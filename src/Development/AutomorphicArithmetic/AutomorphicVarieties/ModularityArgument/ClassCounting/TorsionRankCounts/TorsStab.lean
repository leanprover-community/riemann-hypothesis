module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.RankCount
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Assembly
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.KStability
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.DedekindSR
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
import Mathlib.Tactic.Linter.HaveILetI
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

open CategoryTheory NumberField UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Up

private theorem UpperTheory.V.ZK.Up.card_tors_eq {M N : Type} [AddCommGroup M] [AddCommGroup N] (e : M ≃+ N) :
    Nat.card (AddCommGroup.torsion M) = Nat.card (AddCommGroup.torsion N) := by
  have key : ∀ x : M, x ∈ AddCommGroup.torsion M ↔ e x ∈ AddCommGroup.torsion N := by
    intro x
    rw [AddCommGroup.mem_torsion, AddCommGroup.mem_torsion]
    exact (Function.Injective.isOfFinAddOrder_iff (f := e.toAddMonoidHom) e.injective).symm
  exact Nat.card_congr (e.toEquiv.subtypeEquiv key)

theorem UpperTheory.V.ZK.Up.torsStab :
    UpperTheory.V.ZK.Up.TorsStab := by
  intro L _ _ hL m n n' hn hnn'
  haveI := hL
  have hiso : ∀ k, 2 * m + 4 ≤ k → IsIso (grpHMap (stab (𝓞 L) k (k + 1) (Nat.le_succ k)) m) :=
    fun k hk => PositivityTheory.v8.KStability.kStability (𝓞 L) 2 (dedekindSR (𝓞 L)) m k (by omega)
  have he : Nonempty ((grpH (GL (Fin n) (𝓞 L)) m : Type) ≃+ (grpH (GL (Fin n') (𝓞 L)) m : Type)) := by
    induction n', hnn' using Nat.le_induction with
    | base => exact ⟨AddEquiv.refl _⟩
    | succ k hk ih =>
      obtain ⟨e⟩ := ih
      haveI := hiso k (by omega)
      exact ⟨e.trans (asIso (grpHMap (stab (𝓞 L) k (k + 1) (Nat.le_succ k)) m)).toLinearEquiv.toAddEquiv⟩
  obtain ⟨e⟩ := he
  have key : ∀ x, x ∈ AddCommGroup.torsion (grpH (GL (Fin n) (𝓞 L)) m : Type) ↔
      e x ∈ AddCommGroup.torsion (grpH (GL (Fin n') (𝓞 L)) m : Type) := by
    intro x
    rw [AddCommGroup.mem_torsion, AddCommGroup.mem_torsion]
    exact (Function.Injective.isOfFinAddOrder_iff (f := e.toAddMonoidHom) e.injective).symm
  have hfin : Finite (AddCommGroup.torsion (grpH (GL (Fin n) (𝓞 L)) m : Type)) :=
    (UpperTheory.V.KT.tors_le L n m).1
  refine ⟨Finite.of_equiv _ (e.toEquiv.subtypeEquiv key), ?_⟩
  rw [← UpperTheory.V.ZK.Up.card_tors_eq e]
  rfl
