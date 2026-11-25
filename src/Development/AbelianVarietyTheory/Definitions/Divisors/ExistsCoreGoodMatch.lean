module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.AdelEqZeroOfOffDom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
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

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop

namespace GlobalTheory.CovTop.Model

variable {D : D7}

section Cover

variable {T : Core D} {j : ℕ} {Y : Deep T j} {e e' : ℕ} {o o' : ℝ}

theorem chi_eq_one (h : Y.Good e o) (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) (k) (la) (γ)
    (hγ : γ ∈ ((Y.U σ).X k).Γ) : ((Y.U σ).X k).χ la γ = 1 :=
  GlobalTheory.OneEmbeddingProbe.chi_eq_one _ (h.chiTriv σ hσ) k la γ hγ

end Cover

section Base

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (i : Fin D.R.m)

end Base

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
  (a : (E →+* ℂ) × ℕ → ℕ) (m : ℕ)

theorem exZ_shiftG (s : ℤ) : exZ Dw (shiftG Dw a (2 * m) s) = exOf Dw (laOf Dw a (2 * m) + s • hodgeWt Dw) m := by
  have h1 := exOf_add (laOf Dw a (2 * m)) (s • hodgeWt Dw) (m : ℤ) 0
  have h2 := exOf_weightOf (Dw := Dw) (fun x => (a x : ℤ)) m
  have h3 : laOf Dw a (2 * m) = weightOf Dw (fun x => (a x : ℤ)) m := by simp [laOf]
  rw [add_zero] at h1
  rw [h1, h3, h2]
  funext x
  rw [shiftG, exZ_add]
  simp only [wtZ, exOf, Pi.add_apply]
  push_cast
  rfl

end Weights

end GlobalTheory.CovTop.Model

end
