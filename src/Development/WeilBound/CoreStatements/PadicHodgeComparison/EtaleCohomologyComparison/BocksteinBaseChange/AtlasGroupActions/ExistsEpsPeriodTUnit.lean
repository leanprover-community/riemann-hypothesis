module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BcrisRegularPeriodRing
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
public import GroundTheory.PAdicHodge.FontaineLemmaPeriod
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

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge Formalism.Per6 DeRhamPotentiallySemistable.DRPst

namespace CrystallineSemistableComparison.GlueBE

variable (l : ℕ) [Fact l.Prime]

theorem isUnit_epsilon : IsUnit (epsilon l : Ob l) := by
  have h := (AInf.isUnit_teichmuller_of_untilt_eq_one (K := ℂ_[l]) (p := l) (untilt_epsilon (p := l))).map
    (WittVector.constantCoeff (p := l) (R := Ob l))
  rwa [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero] at h

def eU (k : ℕ) : (Ob l)ˣ :=
  (Units.map ((frobeniusEquiv (Ob l) l).symm : Ob l →+* Ob l).toMonoidHom)^[k] (isUnit_epsilon l).unit

theorem eU_succ (k : ℕ) : eU l (k + 1) = Units.map ((frobeniusEquiv (Ob l) l).symm : Ob l →+* Ob l).toMonoidHom (eU l k) := by
  rw [eU, Function.iterate_succ_apply']
  rfl

theorem eU_zero : (eU l 0 : Ob l) = epsilon l := rfl

theorem eU_one : (eU l 1 : Ob l) = (frobeniusEquiv (Ob l) l).symm (epsilon l) := rfl

def eps : B.Eps l where
  e := eU l
  succ k := by
    ext
    rw [eU_succ, Units.val_pow_eq_pow_val, Units.coe_map]
    exact (frobenius_apply_frobeniusEquiv_symm (Ob l) l _)
  one := by
    rw [eU_zero, WittVector.fontaineTheta_teichmuller]
    exact untilt_epsilon
  prim := by
    rw [eU_one, WittVector.fontaineTheta_teichmuller]
    exact untilt_frobeniusEquiv_symm_epsilon_ne_one

theorem eps_μ : (eps l).μ = algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) (AInf.mu (epsilon l)) := by
  rw [B.Eps.μ, B.Eps.qk, AInf.mu, map_sub, map_one]
  rfl

theorem exists_eps_period_t_unit (K : IntermediateField ℚ_[l] (PadicAlgCl l)) : ∃ ε : B.Eps l, ∃ u : (per l K).A, IsUnit u ∧ (per l K).t = (show (per l K).A from ε.μ) * u := by
  obtain ⟨u, hu, e⟩ := ACris.exists_periodT_eq_mu_mul_unit (K := ℂ_[l]) (p := l) (untilt_epsilon (p := l))
    untilt_frobeniusEquiv_symm_epsilon_ne_one
  exact ⟨eps l, u, hu, by rw [eps_μ]; exact e⟩

end CrystallineSemistableComparison.GlueBE
