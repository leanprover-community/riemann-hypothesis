module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SharpSurjectiveKerSpan
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

theorem isUnit_of_isUnit_sharp {l : ℕ} [Fact l.Prime] (A : PAlg l) (a : A.A)
    (h : IsUnit (A.sharp a)) : IsUnit a := by
  have hu : IsUnit (A.aToU1 a) := by
    rw [CrystallineSemistableComparison.PAlg.sharpMap_eq]
    exact h.map _
  obtain ⟨hsurj, hker⟩ := sharp_map_surjective_ker A
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  obtain ⟨b, rfl⟩ := hsurj v
  have hmem : a * b - 1 ∈ Ideal.span {A.pi} := by
    rw [← hker, RingHom.mem_ker, map_sub, map_mul, hv, map_one, sub_self]
  have hjac : Ideal.span {A.pi} ≤ (⊥ : Ideal A.A).jacobson := by
    haveI : IsAdicComplete (Ideal.span {A.pi}) A.A := A.compl
    exact IsAdicComplete.le_jacobson_bot _
  have hunit := Ideal.mem_jacobson_bot.mp (hjac hmem) 1
  rw [mul_one, sub_add_cancel] at hunit
  exact isUnit_of_mul_isUnit_left hunit

end GlobalTheory.CompanionTheory.Untilt
