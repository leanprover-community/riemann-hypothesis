module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.VecP


open scoped ComplexOrder in
theorem isCartanInv_one_of_onb {k : ℕ} {G B : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis G 1 B k) : IsCartanInv G 1 := by
  obtain ⟨ε, hε, hB, -⟩ := h
  have hε1 : ∀ a, ε a = 1 := fun a =>
    ((hε a).resolve_right fun h' => absurd h'.2 (not_le.mpr a.2)).1
  have hB1 : Bᴴ * G * B = 1 := by simpa [hε1] using hB
  have hBC : B * (Bᴴ * G) = 1 := mul_eq_one_comm.mp hB1
  have hGB : G * B = (Bᴴ * G)ᴴ := by
    calc G * B = (B * (Bᴴ * G))ᴴ * (G * B) := by rw [hBC, conjTranspose_one, Matrix.one_mul]
      _ = (Bᴴ * G)ᴴ * (Bᴴ * G * B) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (Bᴴ * G)ᴴ := by rw [hB1, Matrix.mul_one]
  have hG : G = (Bᴴ * G)ᴴ * (Bᴴ * G) := by
    calc G = G * (B * (Bᴴ * G)) := by rw [hBC, Matrix.mul_one]
      _ = G * B * (Bᴴ * G) := by rw [Matrix.mul_assoc]
      _ = (Bᴴ * G)ᴴ * (Bᴴ * G) := by rw [hGB]
  have hinj : Function.Injective (Bᴴ * G).mulVec := by
    intro v w hvw
    have h2 := congrArg (fun x => B *ᵥ x) hvw
    simpa only [Matrix.mulVec_mulVec, hBC, Matrix.one_mulVec] using h2
  unfold IsCartanInv
  refine ⟨by simp, by simp, ?_⟩
  rw [Matrix.mul_one, hG]
  exact Matrix.PosDef.conjTranspose_mul_self _ hinj

end GlobalTheory.OneMapRef.VecP
