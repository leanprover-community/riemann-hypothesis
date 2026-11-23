module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchB
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchBPf
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.MB

open PositivityTheory.Rg.BcB.F.U (lpow lone)

def MatchBadIOf2 : Prop := M2 → LponeIdem → MatchBadI

theorem matchBadIOf2 : MatchBadIOf2 := by
  intro h2 hI E _ _ _ hU w hw n a b k hab hk K' hK hmem m
  rw [hI E n w K' hK m]
  have hM := h2 E hU w hw n a b k hab hk
  have hf : lone K' = fun γ => ((K'.relIndex (KL n w) : ℕ) : ℂ) *
      (({γ : UL n w | γ.1 ∈ congK n w k} : Set (UL n w)).indicator 1 γ) := by
    funext γ
    rw [mb_lone_apply]
    by_cases h : γ ∈ K'
    · have h' : γ ∈ ({γ : UL n w | γ.1 ∈ congK n w k} : Set (UL n w)) := (hmem γ).1 h
      rw [if_pos h, Set.indicator_of_mem h', Pi.one_apply, mul_one]
    · have h' : γ ∉ ({γ : UL n w | γ.1 ∈ congK n w k} : Set (UL n w)) := fun h' => h ((hmem γ).2 h')
      simp [h, h']
  rw [hf]
  have hM' : Match n a b w 1 ({γ : UL n w | γ.1 ∈ congK n w k}.indicator 1) (pairIndicatorMatch n a b w k) := by
    convert hM using 2
    · rfl
    · unfold pairIndicatorMatch congK
      congr 1
      split_ifs <;> rfl
  exact mb_match_smul _ hM'

end PositivityTheory.Rg.BcB.F.MB

end
