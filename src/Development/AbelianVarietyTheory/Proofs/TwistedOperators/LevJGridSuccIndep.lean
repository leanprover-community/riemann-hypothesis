module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridVertexMeasureEqOfSameNormalisation
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagGenDiag
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowBesZeroE
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowVal

theorem levJ_grid_succ_indep {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t t' : T) (i j : ℕ) :
    levJ G t (.grid (i + 1) (j + 1)) = levJ G t' (.grid (i + 1) (j + 1)) := rfl

theorem levJ_top_indep {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t t' : T) (j : ℕ) :
    levJ G t (.top j) = levJ G t' (.top j) := by
  cases j <;> rfl

theorem vol_row_top_indep : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t t' : T) (M M' : Vol G), M.Is t → M'.Is t' → (∀ j, 1 ≤ j → j ≤ D.R.m → M.ν (.grid D.R.m j) = M'.ν (.grid D.R.m j)) ∧ ∀ j, j ≤ D.R.m → M.ν (.top j) = M'.ν (.top j) := by
  intro D T L sc G t t' M M' hM hM'
  refine ⟨fun j hj1 hjm => ?_, fun j hj => ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i, D.R.m = i + 1 := ⟨D.R.m - 1, by omega⟩
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hX : levJ G t (.grid D.R.m (j' + 1)) = levJ G t' (.grid D.R.m (j' + 1)) := by
      rw [hi]; exact levJ_grid_succ_indep G t t' i j'
    have h1 := hM.vtx (.grid D.R.m (j' + 1)) ⟨le_rfl, hjm⟩
    have h2 := hM'.vtx (.grid D.R.m (j' + 1)) ⟨le_rfl, hjm⟩
    rw [← hX] at h2
    exact GlobalTheory.HaarNorm.vol_nu_eq_of_isAt M M' _ _ h1 h2
  · have h1 := hM.vtx (.top j) hj
    have h2 := hM'.vtx (.top j) hj
    rw [← levJ_top_indep G t t' j] at h2
    exact GlobalTheory.HaarNorm.vol_nu_eq_of_isAt M M' _ _ h1 h2

end GlobalTheory.RowVal
