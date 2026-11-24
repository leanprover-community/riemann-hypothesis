module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.GrSplitField

theorem exists_step {K B : Type} [Field K] [CommRing B] [Algebra K B] {I : Ideal B}
    (γ : DividedPowers I) (i : ℕ) :
    ∃ C : Submodule K B, (∀ n ∈ C, n ∈ pdP γ i) ∧ (∀ n ∈ C, n ∈ pdP γ (i + 1) → n = 0) ∧
      ∀ x ∈ pdP γ i, ∃ n ∈ C, x - n ∈ pdP γ (i + 1) := by
  have hQ : (pdP γ (i + 1)).restrictScalars K ≤ (pdP γ i).restrictScalars K :=
    fun x hx => (Ideal.span_mono fun _ ⟨l, hl, hr, hz⟩ => ⟨l, hl, (Nat.le_succ i).trans hr, hz⟩ :
      pdP γ (i + 1) ≤ pdP γ i) hx
  obtain ⟨c, hc⟩ := exists_isCompl
    (⟨(pdP γ (i + 1)).restrictScalars K, hQ⟩ : Set.Iic ((pdP γ i).restrictScalars K))
  have hinf : (pdP γ (i + 1)).restrictScalars K ⊓ c.1 = ⊥ := congrArg Subtype.val hc.inf_eq_bot
  have hsup : (pdP γ (i + 1)).restrictScalars K ⊔ c.1 = (pdP γ i).restrictScalars K :=
    congrArg Subtype.val hc.sup_eq_top
  refine ⟨c.1, fun n hn => c.2 hn, fun n hn hn' => ?_, fun x hx => ?_⟩
  · have : n ∈ (pdP γ (i + 1)).restrictScalars K ⊓ c.1 := ⟨hn', hn⟩
    rw [hinf] at this
    simpa using this
  · have hx' : x ∈ (pdP γ (i + 1)).restrictScalars K ⊔ c.1 := by
      rw [hsup]
      exact hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx'
    exact ⟨z, hz, by simpa using hy⟩

theorem nonempty_grSplit : ∀ {K B : Type} [Field K] [CommRing B] [Algebra K B] {I : Ideal B} (γ : DividedPowers I) (m : ℕ),
    pdP γ m = ⊥ → Nonempty (GrSplit K γ m) := by
  intro K B _ _ _ I γ m hm
  choose C hC₁ hC₂ hC₃ using fun i : ℕ => exists_step (K := K) γ i
  exact ⟨{
    N := fun i => C i
    ν := fun i => (C i).subtype
    mem := fun i n => hC₁ i n n.2
    inj := fun i n h => Subtype.ext (hC₂ i n n.2 h)
    surj := fun i x hx => by
      obtain ⟨n, hn, h⟩ := hC₃ i x hx
      exact ⟨⟨n, hn⟩, h⟩
    nil := hm }⟩

end GlobalTheory.CompanionTheory.GrSplitField
