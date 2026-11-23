module

public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.InvEqWww
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTH

open PositivityTheory.Rg.Sw.Glob.FTP PositivityTheory.Rg.Sw.Glob.PlaceFactsH
open Classical

variable {D : D7} {n m : ℕ}


theorem ww_act {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D} {V : HSp D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    (w : G D n) (hw : mat w = blk4 0 1 (-1) 0) :
    ∃ c₀ : ℂ, ∀ (Φ : schwartzA θ V.rank n) x, (ω (w * w) Φ).1 x = c₀ * Φ.1 (-x) := by
  refine ⟨(χ (Matrix.GeneralLinearGroup.det (-1 : GL (Fin n) (AE D))) : ℂ) *
      npow (absA D (Matrix.GeneralLinearGroup.det (-1 : GL (Fin n) (AE D)))) ((V.rank : ℂ) / 2), fun Φ x => ?_⟩
  have hm : mat (w * w) = blk4 (-1 : GL (Fin n) (AE D)).1 0 0 (adj ((-1 : GL (Fin n) (AE D))⁻¹).1) := by
    rw [mat_ww w hw, inv_neg_one, Units.val_neg, Units.val_one, adj_neg, adj_one]
  rw [hω.levi (w * w) (-1) hm Φ x]
  congr 2
  rw [Units.val_neg, Units.val_one]
  exact congrArg _ ((Matrix.mul_neg x 1).trans (by rw [Matrix.mul_one]))


theorem compAt_neg (θ : InfFam D) (τ : D.what₂.Tau) (x : Mx D m n) : compAt θ τ (-x) = -compAt θ τ x := by
  ext i j; simp only [compAt, Matrix.map_apply, Matrix.neg_apply, RingHom.map_neg]

end PositivityTheory.Rg.Sw.Glob.FTH
