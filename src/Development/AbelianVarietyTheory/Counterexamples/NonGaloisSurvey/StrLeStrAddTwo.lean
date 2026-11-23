module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.PtStringTest

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem aPl_last_pos (i : Fin D.R.m) (τ : D.what₂.Tau) : 0 < aPl D i (D.R.k + i) τ (D.R.k + i - 1) := by
  have hk : 1 ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    omega
  have hn : D.R.k + (i : ℕ) - 1 < D.R.k + (i : ℕ) := by omega
  have hlam : Formalism.L2.NTheta.lamAt (D.hc τ) (D.R.k + (i : ℕ) - 1) = -(D.hc τ).b i := by
    unfold Formalism.L2.NTheta.lamAt
    rw [dite_eq_right (by omega), dite_eq_left (by omega)]
    congr 2
    ext
    simp only
    omega
  have hc : ((D.R.k + (i : ℕ) - 1 : ℕ) : ℚ) + 1 = ((D.R.k + (i : ℕ) : ℕ) : ℚ) := by
    have : D.R.k + (i : ℕ) - 1 + 1 = D.R.k + (i : ℕ) := by omega
    exact_mod_cast this
  have hgap := (D.hc τ).gap_be i
  have h1 : (1 : ℚ) ≤ -(D.hc τ).b i + (D.hc τ).e i
      - (((D.R.k + (i : ℕ) : ℕ) : ℚ) - (((D.R.k + (i : ℕ) - 1 : ℕ) : ℚ) + 1)) - ((D.R.t : ℚ) + 1) / 2 := by
    linarith
  have h2 := Int.floor_pos.2 h1
  unfold aPl
  rw [if_pos hn, hlam]
  omega

end GlobalTheory.PtStringTest

end
