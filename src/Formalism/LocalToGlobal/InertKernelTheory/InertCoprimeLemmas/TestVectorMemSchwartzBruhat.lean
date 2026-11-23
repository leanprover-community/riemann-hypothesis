module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.GlobalTheory.GL3.NormNatCoprime
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.GlobalTheory.GL3.Statement

@[expose] public section

noncomputable section

namespace Formalism.L2.KerInert

namespace JetIntegrality

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

section Good

variable {p : ℕ} [Fact p.Prime] {σ ι : Type*}

variable (δ : ι → MvPowerSeries σ ℂ_[p] →+ MvPowerSeries σ ℂ_[p])

def Wd (l : List ι) (G : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  l.foldr (fun j H => δ j H) G

def Good (G : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ l : List ι, IsIntP (MvPowerSeries.constantCoeff (Wd δ l G))

variable {δ}

end Good

section Ring

variable {p : ℕ} [Fact p.Prime]

end Ring

section Deriv

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

variable {p : ℕ} [Fact p.Prime] {r : ℕ}

end Deriv

section Chain


variable {D : D7} {N N' r : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
  (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)

end Chain

section Lin


variable {D : D7} {N N' r : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

theorem test_vector_mem_schwartz_bruhat (x : D.host.E) : D.host.φ₀ x ∈ Qbar := by
  rw [mem_algebraicClosure_iff']
  exact (Algebra.IsIntegral.isIntegral x).map D.host.φ₀.toRatAlgHom

theorem isPadicIntegral_lamC_K (c : 𝓞 D.host.K) : IsIntP (lamC lam (D.host.φ₀ ((c : D.host.K) : D.host.E))) := by
  have hI : IsIntegral ℤ ((c : D.host.K) : D.host.E) :=
    map_isIntegral_int (algebraMap D.host.K D.host.E) (NumberField.RingOfIntegers.isIntegral_coe c)
  unfold lamC
  rw [dite_eq_left (test_vector_mem_schwartz_bruhat _)]
  exact RestC.norm_le_one_of_int (map_isIntegral_int (lam.comp (D.host.φ₀.codRestrict Qbar test_vector_mem_schwartz_bruhat)) hI)

variable (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)

end Lin

section Core


end Core

section Log


variable {p : ℕ} [Fact p.Prime]

end Log

end JetIntegrality


end Formalism.L2.KerInert
