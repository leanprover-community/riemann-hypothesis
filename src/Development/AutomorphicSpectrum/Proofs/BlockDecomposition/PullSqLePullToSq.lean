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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.RedTower

section Sq
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

theorem pull_sqLe_pull_toSq {a b a' b' : IdF A} (ha : ∀ T, a.S T = ⊤) (ha' : ∀ T, a'.S T = ⊤)
    (hle : ∀ T, a.S T ≤ a'.S T) (hb : ∀ T, b.S T ≤ b'.S T) (j : ℕ) (z : CH.H (CH.modF A) j) :
    (sqLe hle hb).pull j ((toSq a b ha).pull j z) = (toSq a' b' ha').pull j z := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rfl

end Sq

theorem trM_redM {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) (r : Option ℤ) (c : b.R) (n j : ℕ) (z : HO Q j) :
    trM Q r c n j (redM Q r (c ^ (n + 1)) j z) = redM Q r (c ^ n) j z :=
  pull_sqLe_pull_toSq (fun _ => rfl) (fun _ => rfl) (fun _ => le_rfl) (stdI_le Q r c n) j z

end GlobalTheory.CompanionTheory.RedTower
