module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StLocB
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationDetEqOne
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen GLnLocal

theorem UpperTheory.Gal.Gen.gammaEig_pf :
    UpperTheory.Gal.Gen.GammaEig := by
  intro F _ _ _ _ n _ _ μ _ z h g
  have hf : ∀ (g k : GL (Fin n) F), k ∈ integralGL F n →
      zonalSpherical μ z (g * k) = zonalSpherical μ z g :=
    fun g k hk => zonalSpherical_mul_right z g hk
  have hpos : (0 : ℝ) < μ.real ↑(integralGL F n) :=
    HeckeAlgebra.measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)
  have hne : (μ.real ↑(integralGL F n) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 hpos.ne'
  have hmin : ∀ r, minusculeHecke μ r ∈ eigenSubalgebra μ z (zonalSpherical μ z) hf := by
    intro r y
    rw [integral_minusculeHecke_mul hf y r, sum_zonalSpherical_gMat z r y]
    simp only [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  have htop : eigenSubalgebra μ z (zonalSpherical μ z) hf = ⊤ :=
    eigenSubalgebra_eq_top z hf (fun r _ => hmin r)
      (GlobalTheory.HenQ.ShellOp.central_mem_of_top z hf (hmin n))
  have hmem : h ∈ eigenSubalgebra μ z (zonalSpherical μ z) hf := by
    rw [htop]
    exact Algebra.mem_top
  exact hmem g
