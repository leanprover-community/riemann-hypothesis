module

public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInNormalFormAndArchimedeanConstant
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ValueAtNormalForm
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

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.KeyPow

theorem keyFormulaPow_of_keyRule :
    ThetaUnifAV → ∀ N : ℕ → ℕ, (∀ g, 1 ≤ N g) → GlobalTheory.KeyPow.KeyRule N 1 GlobalTheory.KeyPow.charHalf → GlobalTheory.KeyFormulaPow := by
  rintro hT N hN ⟨κ, hH, hF, hU, hK⟩
  refine ⟨N, hN, κ, fun K _ _ P hg rig hr th hth v hv th' hth' v' hv' a M =>
      hH K P hg rig hr th hth v hv th' hth' v' hv' a M hg,
    fun K K' _ _ _ _ f x x' => hF K K' f x x' x.g_pos,
    fun R K _ _ _ _ _ _ _ x xK => hU R K x xK x.g_pos,
    fun x u τ a b h₁ h₂ ha hb h₃ h₄ h₅ h₆ =>
      hK x τ a b x.g_pos ⟨ha, hb⟩ ((normalAt_one_iff x τ a b).2 ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩), ?_⟩
  intro x u Hm W χ θ Fd nth nη h₁ h₂ h₃ h₄ h₅ h₆ h₇
  obtain ⟨u', τ, M, a, b, c, k₁, k₂, ha, hb, k₃, k₄, hc, k₅, hM, k₆, hn⟩ :=
    keyIn_normal_form_and_archimedean_constant hT x u Hm W χ θ Fd nth nη h₁ h₂ h₃ h₄ h₅ h₆ h₇
  have hv := value_at_normalForm N 1 (κ ℂ) x.P.g a b x.g_pos (hH ℂ)
    (fun y h τ' hy => hK y τ' _ _ y.g_pos ⟨fun i => ha _, fun i => hb _⟩ hy) x rfl τ M c hc hM
    ⟨u', k₁, k₂, k₃, k₄, k₅, k₆⟩
  rw [hv, norm_pow, pow_mul nth, pow_mul nη, ← mul_pow, ← mul_pow, hn, ← pow_mul]

end GlobalTheory.KeyPow
