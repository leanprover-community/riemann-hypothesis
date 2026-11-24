module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import GroundTheory.GlobalFields.ComplexMultiplication.IdeleAction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

namespace GlobalTheory.CompanionTheory.EllipticCM

theorem ord_eq_ord_vw_finitePart {K : Type} [Field K] [NumberField K]
    (s : GroundTheory.Global.IdeleGroup K) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    GroundTheory.Global.IdeleGroup.ord v s =
      GlobalTheory.Idele.ord_vw (GlobalTheory.EllipticCM.finitePart (K := K) s) v :=
  rfl

theorem coe_smul_eq_finitePart_smul {K : Type} [Field K] [NumberField K]
    (s : GroundTheory.Global.IdeleGroup K) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((s • 𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (GlobalTheory.EllipticCM.finitePart (K := K) s) • (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := by
  refine GlobalTheory.Idele.eq_of_count_eq (Units.ne_zero _)
    (GlobalTheory.Idele.smul_ne_zero _ (Units.ne_zero _)) fun v => ?_
  rw [GroundTheory.Global.IdeleGroup.count_smul, GlobalTheory.Idele.count_smul _ (Units.ne_zero _),
    ord_eq_ord_vw_finitePart]

theorem inv_smul_eq_finitePart_inv_smul {K : Type} [Field K] [NumberField K]
    (s : GroundTheory.Global.IdeleGroup K) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((s⁻¹ • 𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (GlobalTheory.EllipticCM.finitePart (K := K) s)⁻¹ • (𝔞 : FractionalIdeal (𝓞 K)⁰ K) :=
  coe_smul_eq_finitePart_smul s⁻¹ 𝔞

end GlobalTheory.CompanionTheory.EllipticCM
