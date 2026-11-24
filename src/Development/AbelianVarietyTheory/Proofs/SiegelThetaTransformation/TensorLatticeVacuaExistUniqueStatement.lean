module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.tensorLattice_vacua_exist_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L, SelfD X L → ∀ (M : ℕ), ∀ Λ ∈ Vset E n M, (∃ v, IsVac X bas w (tens Λ L) v) ∧ (∀ v v', IsVac X bas w (tens Λ L) v → IsSB v' → (∀ y ∈ tens Λ L, epsW X w y • heisG X bas y v' = v') → v' = ip v' v • v) ∧ (∀ φ : TF n g, IsSB φ → ∀ v, IsVac X bas w (tens Λ L) v → projA X bas w (tens Λ L) φ = ip φ v • v) ∧ ∀ L', SelfD X L' → ∀ Λ' ∈ Vset E n M, ∀ v v', IsVac X bas w (tens Λ L) v → IsVac X bas w (tens Λ' L') v' → ((tens Λ' L').relIndex (tens Λ L) : ℝ) * ‖ip v v'‖ ^ 2 = 1 := by
  first | exact @GlobalTheory.SW.TensVac.vacua | exact GlobalTheory.SW.TensVac.vacua | (intros; apply GlobalTheory.SW.TensVac.vacua <;> assumption)
