module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OptionEquivLeftRenameSomeComplexEqC
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

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

theorem coefM_apply_eq_coeff {n L : ℕ} (k : ℕ) (s : PolyM n L) :
    coefM n L k s = (optionEquivLeft ℂ (Fin L ⊕ EntIdx n) s).coeff k := by
  simp only [coefM, LinearMap.comp_apply, LinearMap.restrictScalars_apply, AlgEquiv.toLinearMap_apply,
    Polynomial.lcoeff_apply]

theorem dMu_eq_extDerivation {n L : ℕ} (ε : Fin n → Bool) (x : Mode ε) :
    dMu L ε x = mkDerivation ℂ (fun w : Option (Fin L ⊕ EntIdx n) => match w with
      | none => (0 : MvPolynomial (Option (Fin L ⊕ EntIdx n)) ℂ)
      | some v => rename some (dL L ε x (X v))) := by
  unfold dMu
  refine congrArg _ (funext fun w => ?_)
  cases w with
  | none => rfl
  | some v => simp only [inM]

theorem coefM_dMu : T_coefM_dMu := by
  intro n L ε x k s
  have h := GlobalTheory.coeff_optionEquivLeft_extDerivation (dL L ε x) k s
  rw [coefM_apply_eq_coeff, coefM_apply_eq_coeff, ← h]
  have e : dMu L ε x = mkDerivation ℂ (fun w : Option (Fin L ⊕ EntIdx n) => match w with
      | none => (0 : MvPolynomial (Option (Fin L ⊕ EntIdx n)) ℂ)
      | some v => rename some (dL L ε x (X v))) := dMu_eq_extDerivation ε x
  refine congrArg (fun D : Derivation ℂ (PolyM n L) (PolyM n L) => (optionEquivLeft ℂ (Fin L ⊕ EntIdx n) (D s)).coeff k) (e.trans ?_)
  refine congrArg _ (funext fun w => ?_)
  cases w <;> rfl

end GlobalTheory.PsCo.Cw2a
