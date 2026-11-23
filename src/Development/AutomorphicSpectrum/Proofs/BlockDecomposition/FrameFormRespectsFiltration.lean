module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight
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

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.FormMem

theorem prod_fil_mem {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) (T : C) : ∀ (n : ℕ) (f : Fin n → Φ.A.obj T), (∀ k, f k ∈ (Fil 1).S T) →
      ∏ k, f k ∈ (Fil (n : ℤ)).S T := by
  intro n
  induction n with
  | zero =>
    intro f _
    rw [hF.top ((0 : ℕ) : ℤ) (by simp) T]
    exact Submodule.mem_top
  | succ n ih =>
    intro f h
    rw [Fin.prod_univ_succ]
    simpa only [Nat.add_comm 1 n] using
      hF.mul 1 n T (h 0) (ih (fun k => f k.succ) fun k => h k.succ)

theorem form_mem : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil)
    {d : ℕ} (E : Frame (Φ := Φ) d) (σ : ∀ T : C, E.D ⟶ T) (j q : ℕ) (I : Fin j → Fin d) (x : Φ.A.obj E.D), x ∈ (Fil q).S E.D →
    ∀ s : ComposableArrows C j, E.form σ I x s ∈ (Fil ((j + q : ℕ) : ℤ)).S (s.obj (Fin.last j)) := by
  intro R _ C _ Φ Fil hF d E σ j q I x hx s
  refine hF.mul j q _ (prod_fil_mem hF _ j _ fun k => (Fil 1).map_mem _ ?_) ((Fil q).map_mem (σ _) hx)
  rw [hF.one]
  exact E.mem _ _ _

end GlobalTheory.CompanionTheory.FormMem
