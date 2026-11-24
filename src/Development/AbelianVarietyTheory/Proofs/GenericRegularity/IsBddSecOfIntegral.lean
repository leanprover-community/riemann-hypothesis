module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.BddOfMemHolSub
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem isBddSec_of_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), ∀ (la : Wt X.Ψ r) (N k m : ℕ) (w : Fin N → Frame X.Ψ r → ℂ) (cf : ℕ → MvPolynomial (Fin N) ℂ) (g : Frame X.Ψ r → ℂ), (∀ i, X.IsBddSec la (w i)) → (∀ i < m, (cf i).IsHomogeneous ((m - i) * k)) → X.IsSec (k • la) g → (∀ x ∈ X.dom, g x * g x ^ m + ∑ i ∈ Finset.range m, (g x * MvPolynomial.eval (fun s => w s x) (cf i)) * g x ^ i = 0) → X.IsBddSec (k • la) g := by
  intro E _ _ _ r X la N k m w cf g hw hcf hg heq
  refine ⟨hg, ?_⟩
  choose B hB using fun i => (hw i).2
  obtain ⟨C, hC0, hC⟩ := IntegralCusp.exists_root_bound N k m cf hcf
  refine ⟨C * (∑ i, |B i|) ^ k, fun x hx => ?_⟩
  have h2 := hC _ _ (heq x hx)
  set ν := X.nfac la x with hν
  have hν0 : 0 ≤ ν := Formalism.L2.PjFree.pnorm_fac_nonneg _ _ _
  have h3 : ‖fun i => w i x‖ * ν ≤ ∑ i, |B i| := by
    rw [mul_comm, ← Real.norm_of_nonneg hν0, ← norm_smul,
      pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
    intro i
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hν0, mul_comm]
    exact ((hB i x hx).trans (le_abs_self _)).trans
      (Finset.single_le_sum (f := fun i => |B i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  show ‖g x‖ * X.nfac _ x ≤ _
  rw [IntegralCusp.nfac_nsmul X la (k • la) k (fun τ i => by simp), ← hν]
  calc _ ≤ C * ‖fun i => w i x‖ ^ k * ν ^ k :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = C * (‖fun i => w i x‖ * ν) ^ k := by ring
    _ ≤ _ := by gcongr

end GlobalTheory
