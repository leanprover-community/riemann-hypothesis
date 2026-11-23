module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsBasisEmbedding
public import Formalism.SharpRestriction.Divisibility.JetPolynomialLogs.AnnihilatorMulRelativeDifferent
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField

namespace GlobalTheory.HostQuadUnits

theorem four_lt_d (D : Formalism.BasicNotions.D7) : 4 < D.host.d := by
  have h := D.host.hyp.2.2.2.1
  omega

theorem isGalois_and_units (D : Formalism.BasicNotions.D7) :
    IsGalois ℚ D.host.K ∧ ∀ u : (𝓞 D.host.K)ˣ, u = 1 ∨ u = -1 := by
  have h2 : Module.finrank ℚ D.host.K = 2 := Formalism.MainNotions.DIV.Bridge.LogAbsNormDifferent.finrank_K D
  refine ⟨?_, fun u => ?_⟩
  · haveI : Algebra.IsQuadraticExtension ℚ D.host.K := ⟨h2⟩
    infer_instance
  · let σ : D.host.K →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := D.host.K)).toRingHom
    exact GlobalTheory.QuadraticZeta.unit_eq h2 (Formalism.MainNotions.DIV.Bridge.LogAbsNormDifferent.discr_K D) σ (four_lt_d D) u

theorem main : ∀ D : Formalism.BasicNotions.D7, IsGalois ℚ D.host.K ∧ ∀ u : (𝓞 D.host.K)ˣ, u = 1 ∨ u = -1 :=
  isGalois_and_units

end GlobalTheory.HostQuadUnits
