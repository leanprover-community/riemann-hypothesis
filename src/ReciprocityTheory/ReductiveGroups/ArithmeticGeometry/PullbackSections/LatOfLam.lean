module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.TBDisc

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.TB

theorem latOfLam : LatOfLamSt := by
  intro D B P j X S ka wL wF large₂ C A hg hs hlam hspan hH2
  let Nf : NormFam B.KO (B.Cusp j ka) :=
    { N := B.supN j ka
      nonneg := B.supN_nonneg j ka
      eq_zero := fun σ v h => (B.supN_eq_zero j ka σ v).mp h
      smul := B.supN_smul j ka
      add := B.supN_add j ka }
  have hPL : ProdLower Nf (B.Mlat j ka)
      ((Fintype.card (B.KO →+* ℂ) : ℝ) * (WeightFamilies.PP0v D large₂ C A * (1 + Real.log ka.size) * ka.size)) := by
    intro f hf hne
    have h1 := hlam f hf hne
    unfold WeightFamilies.meanLogSup at h1
    by_cases hc : (Fintype.card (B.KO →+* ℂ) : ℝ) = 0
    · have hc' : Fintype.card (B.KO →+* ℂ) = 0 := by exact_mod_cast hc
      have hempty : IsEmpty (B.KO →+* ℂ) := Fintype.card_eq_zero_iff.mp hc'
      rw [hc, zero_mul, neg_zero]
      simp
    · have hpos : (0 : ℝ) < Fintype.card (B.KO →+* ℂ) :=
        lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hc)
      have h2 := (le_div_iff₀ hpos).mp h1
      show -((Fintype.card (B.KO →+* ℂ) : ℝ) * _) ≤ ∑ σ : B.KO →+* ℂ, Real.log (B.supN j ka σ f)
      linarith
  have hUD := _root_.PI.UnitaryGroupMassFormula.TBDisc.discOfProdLower B.KO (B.Cusp j ka) Nf (B.Mlat j ka) _ hPL
  have hFG := _root_.PI.UnitaryGroupMassFormula.TBDisc.fGOfDisc B.KO (B.Cusp j ka) Nf (B.Mlat j ka) hUD
  exact Submodule.IsLattice.of_fg B.KO hFG

end ReciprocityTheory.ChartRestriction.G.PullbackSections
