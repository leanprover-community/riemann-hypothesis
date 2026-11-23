module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ContinuousKer
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HalfTrAddSwap
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.CompAtSubSIns
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.PlaceFacts
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open Formalism.IndefR.Eqv (psiT eq_thetaC)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTH

open PositivityTheory.Rg.Sw.Glob.FTP PositivityTheory.Rg.Sw.Glob.PlaceFactsH
open Classical

variable {D : D7} {n m : ℕ}

theorem Aw_away {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hdet : IsUnit fr.det) (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D V.rank n)) (Ψ : Mx D V.rank n → ℂ) (x x' : Mx D V.rank n)
    (hx : ∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x') (hf : x.map (finPart D) = x'.map (finPart D)) :
    Aw ψ V θ τ fr μ Ψ x = Aw ψ V θ τ fr μ Ψ x' := by
  have e : Bw ψ V θ τ fr Ψ x = Bw ψ V θ τ fr Ψ x' := by
    funext y
    unfold Bw
    rw [inner_away hθ x x' _ hx hf (compAt_sub_sIns hθ hdet y)]
  unfold Aw
  rw [e]


theorem mat_ww (w : G D n) (hw : mat w = blk4 0 1 (-1) 0) : mat (w * w) = blk4 (-1) 0 0 (-1) := by
  rw [mat_mul', hw, submatrix_fromBlocks_mul]
  simp


theorem inv_eq_www (w : G D n) (hw : mat w = blk4 0 1 (-1) 0) : w⁻¹ = w * w * w := by
  apply mat_inj
  rw [GlobalTheory.CompanionTheory.EisCovar.Weyl.mat_inv_eq w hw, mat_mul', mat_ww w hw, hw, submatrix_fromBlocks_mul]
  simp

end PositivityTheory.Rg.Sw.Glob.FTH
