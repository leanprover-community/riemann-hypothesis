module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDetResMat
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.ResR

theorem latC_smul_of_fr_fixed : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x y : Fin r × n) (a : n → P.R.B) (e : ↥(MaximalUnramifiedExtension l)), fr l r e = e → LatC P U x y a → LatC P U x y (e • a) := by
  intro l _ P r n _ _ U x y a e he h
  obtain ⟨h1, h2⟩ := h
  have hsm : ∀ i, (e • a) i = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B e * a i := fun i => by
    rw [Pi.smul_apply, Algebra.smul_def]
  have hev : ∀ (m : ℕ) (b : P.R.B), ev P m (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B e * b) = kd P (fr l m e) * ev P m b := by
    intro m b
    rw [← evHom_apply, map_mul, evHom_apply, evHom_apply, ev_kur]
  refine ⟨fun i => ?_, fun m => ?_⟩
  · rw [hsm]
    have key : ∀ k : ℕ, P.φB^[k] (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B e * a i) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (fr l k e) * P.φB^[k] (a i) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [Function.iterate_succ_apply', ih, map_mul, Function.iterate_succ_apply', phiB_algebraMap, add_comm, fr_add, fr_one]
    rw [key, he, h1]
  · obtain ⟨w, hw, hw'⟩ := h2 m
    refine ⟨fun i => kd P (fr l m e) * w i, fun i => Fil_mul_left (kd_mem_Fil P _) (hw i), ?_⟩
    funext i
    rw [hsm, hev]
    have := congrFun hw' i
    rw [this]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.PMon.ResR
