module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.RedMk
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsQ

namespace GlobalTheory.CompanionTheory.LsCmp

theorem cmpq_bijective (R : Type) [CommRing R] (C : Type 1) [Category.{0} C]
    (A : C ⥤ CommAlgCat.{0} R) (l n i : ℕ) : Function.Bijective ((cmpq A l n).f i) := by
  have hmk := cmpq_mk A l n i
  constructor
  · rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [hmk] at hq
    rw [Submodule.Quotient.mk_eq_zero]
    have hy : ∀ s : ComposableArrows C i, ∃ a : ↑(A.obj (s.obj (Fin.last i))),
        a * algebraMap R ↑(A.obj (s.obj (Fin.last i))) ((l : R) ^ n) = y s := by
      intro s
      have h1 : ((qM A l n).pullC i y) s = 0 := by
        rw [hq]
        rfl
      have h2 : Ideal.Quotient.mk (Ideal.span {algebraMap R ↑(A.obj (s.obj (Fin.last i))) ((l : R) ^ n)}) (y s) = 0 :=
        congrArg Subtype.val h1
      exact Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp h2)
    choose a ha using hy
    rw [CrystallineSemistableComparison.Ls.lpow, LinearMap.mem_range]
    refine ⟨a, ?_⟩
    funext s
    show ((l : R) ^ n) • a s = y s
    rw [Algebra.smul_def, mul_comm]
    exact ha s
  · intro g
    have hx : ∀ s : ComposableArrows C i, ∃ x : ↑(A.obj (s.obj (Fin.last i))),
        Ideal.Quotient.mk (Ideal.span {algebraMap R ↑(A.obj (s.obj (Fin.last i))) ((l : R) ^ n)}) x =
          Subtype.val (g s) := fun s => Ideal.Quotient.mk_surjective _
    choose x hx using hx
    refine ⟨Submodule.Quotient.mk x, ?_⟩
    rw [hmk]
    funext s
    apply Subtype.ext
    exact hx s

end GlobalTheory.CompanionTheory.LsCmp

end
