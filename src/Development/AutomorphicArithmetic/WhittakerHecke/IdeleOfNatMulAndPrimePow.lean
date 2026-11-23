module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
public import Development.AutomorphicArithmetic.WhittakerHecke.HeightOneSpectrumRatCorrespondPrimes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.ideleOfNat_mul_and_prime_pow :
    (∀ m n : ℕ, 0 < m → 0 < n → pin (m * n) = pin m * pin n) ∧ (∀ (v : H.P ℚ) (k : ℕ), pin (normV v ^ k) = pv v ^ k) := by
  obtain ⟨hp, -, hinj, -⟩ := UpperTheory.heightOneSpectrum_rat_correspond_primes
  have hfin : ∀ n : ℕ, (Function.mulSupport fun v : H.P ℚ => pv v ^ (n.factorization (normV v))).Finite := by
    intro n
    have h1 : ((fun v : H.P ℚ => normV v) ⁻¹' (n.factorization.support : Set ℕ)).Finite :=
      Set.Finite.preimage (fun a _ b _ h => hinj a b h) (Finset.finite_toSet _)
    refine h1.subset fun v hv => ?_
    simp only [Set.mem_preimage, Finset.mem_coe, Finsupp.mem_support_iff]
    intro h0
    exact hv (by simp only [h0, pow_zero])
  refine ⟨fun m n hm hn => ?_, fun v k => ?_⟩
  · unfold pin
    rw [← finprod_mul_distrib (hfin m) (hfin n), Nat.factorization_mul hm.ne' hn.ne']
    exact finprod_congr fun v => by rw [Finsupp.add_apply, pow_add]
  · unfold pin
    rw [(hp v).factorization_pow, finprod_eq_single _ v]
    · rw [Finsupp.single_eq_same]
    · intro w hw
      rw [Finsupp.single_eq_of_ne (fun h => hw (hinj _ _ h)), pow_zero]
