module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowPolarizationOperatorsRelationsDivPowBaseChangStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TraceRowOperatorPowerDualWeylHighestWeightStatement
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalC
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

noncomputable section
namespace GlobalTheory.Alc

theorem hcVal_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {N : ℕ} (μ : Fin N → R) (k : ℕ) :
    hcVal S (fun i => φ (μ i)) k = φ (hcVal R μ k) := by
  have hM : hcMat S (fun i => φ (μ i)) = (hcMat R μ).map φ := by
    ext i l
    simp only [hcMat, shift, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  have hP : (hcMat S (fun i => φ (μ i))) ^ k = ((hcMat R μ) ^ k).map φ := by
    rw [hM]
    exact (map_pow (RingHom.mapMatrix φ) (hcMat R μ) k).symm

  simp only [hcVal, hP, Matrix.map_apply, map_sum]

theorem gel_dualWeyl_int (N : ℕ) (ν : Fin N → ℕ) (hν : Antitone ν) (j : ℕ) (f : MvPolynomial (Fin N × Fin N) ℤ)
    (hf : f ∈ dualWeyl ℤ N N ν) : gel ℤ N N j f = hcVal ℤ (fun i => (ν i : ℤ)) j • f := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
  rw [(GlobalTheory.T.rowPolarizationOperators_relations_divPow_baseChange ℤ N N).2.2 ℚ (Int.castRingHom ℚ) j f,
    GlobalTheory.T.traceRowOperatorPower_dualWeyl_highestWeight N ν hν j _ (dualWeylMap ℤ ℚ (Int.castRingHom ℚ) N N ν f hf),
    smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]
  congr 2
  rw [← hcVal_map]
  simp

theorem gel_dualWeyl_field : ∀ (k : Type) [Field k] (N : ℕ) (ν : Fin N → ℕ), Antitone ν → ∀ j : ℕ,
    ∀ f ∈ dualWeyl k N N ν, gel k N N j f = hcVal k (fun i => (ν i : k)) j • f := by
  intro k _ N ν hν j f hf
  rw [standardMonomialSpanDomain k N N ν] at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨K, sz, hsz, I, hsh, rfl⟩ := hg
    have hb : bideterminant k sz hsz I = map (Int.castRingHom k) (bideterminant ℤ sz hsz I) := by
      simp only [bideterminant, initMinor, map_prod]
      refine Finset.prod_congr rfl fun x _ => ?_
      rw [RingHom.map_det]
      congr 1
      ext p q
      simp
    have hmem : bideterminant ℤ sz hsz I ∈ dualWeyl ℤ N N ν := hsh ▸ bidetMem ℤ N N K sz hsz I
    rw [hb, ← (GlobalTheory.T.rowPolarizationOperators_relations_divPow_baseChange ℤ N N).2.2 k (Int.castRingHom k) j, gel_dualWeyl_int N ν hν j _ hmem,
      smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]
    congr 2
    rw [← hcVal_map]
    simp
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, hx, smul_comm]

end GlobalTheory.Alc
