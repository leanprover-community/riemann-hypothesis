module

public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff

namespace GlobalTheory.HolDict

theorem lamAt_last {R : Ranks} (h : HCParam R) (i : Fin R.m) (n : ℕ) (hn : n + 1 = R.k + i) :
    Formalism.L2.NTheta.lamAt h n = -h.b i := by
  have hk := R.m_add_three_le_k
  have hi := i.2
  have e : n - (R.k - 1) = i := by omega
  unfold Formalism.L2.NTheta.lamAt
  rw [dite_eq_right (by omega), dite_eq_left (by omega)]
  congr 2
  exact Fin.ext e

theorem lastPos_of_kapIs :
    ∀ (D : D7) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), KapIs κ → ∀ i, (κ i).LastPos := by
  intro D κ h i τ k hk
  rw [(h i τ).1 k,
    show (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ (inR i).1 (inR i).2 _]
  have hp : (k : ℕ) + 1 = D.R.k + i := by
    rw [hk]
    simp only [Ranks.sigW]
    omega
  have hg := (D.hc τ).gap_be i
  have hq : (((D.R.sigW ((i : ℕ) + 1)).1 : ℕ) : ℚ) = ((k : ℕ) : ℚ) + 1 := by
    exact_mod_cast hk.symm
  simp only [aPl, if_pos k.2]
  rw [lamAt_last (D.hc τ) i k hp, hq]
  have h1 : (1 : ℤ) ≤ ⌊-(D.hc τ).b i + (D.hc τ).e i - (((k : ℕ) : ℚ) + 1 - (((k : ℕ) : ℚ) + 1)) -
      ((D.R.t : ℚ) + 1) / 2⌋ := by
    rw [Int.le_floor]
    push_cast
    linarith
  omega

end GlobalTheory.HolDict
