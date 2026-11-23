module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlIntegralInvMulOfLatticeMapEq
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


theorem _root_.GlobalTheory.T.glIntegral_inv_mul_of_lattice_map_eq : ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (r : ℕ) (h h' : GL (Fin r) K), (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((h : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) = (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((h' : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) → GlobalTheory.SplitHecke.GInt O (h⁻¹ * h') := by
  first | exact @GlobalTheory.SplitHecke.gInt_inv_mul_of_map_eq | exact GlobalTheory.SplitHecke.gInt_inv_mul_of_map_eq | (intros; apply GlobalTheory.SplitHecke.gInt_inv_mul_of_map_eq <;> assumption)
