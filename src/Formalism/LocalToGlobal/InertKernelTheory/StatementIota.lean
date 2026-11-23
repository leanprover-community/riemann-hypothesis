module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions

def IotaExt {p : ℕ} [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]) : Prop :=
  ∀ x : Formalism.MainNotions.TaylorLogMetric.Qbar, ι (x : ℂ) = lam x

def taylorSer (D : D7) {N N' : ℕ} (G : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ) :
    MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ :=
  fun α => Formalism.MainNotions.TaylorLogMetric.taylor D G α

def AlgCoef (D : D7) {N N' : ℕ} (G : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ) : Prop :=
  ∀ α : Formalism.MainNotions.TaylorLogMetric.Mono D N N', Formalism.MainNotions.TaylorLogMetric.taylor D G α ∈ Formalism.MainNotions.TaylorLogMetric.Qbar

def LamExt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]), ∃ ι : ℂ ≃+* ℂ_[p], IotaExt lam ι

def LamCIota : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), IotaExt lam ι →
    (∀ x : ℂ, x ∈ Formalism.MainNotions.TaylorLogMetric.Qbar → Formalism.MainNotions.TaylorLogMetric.lamC lam x = ι x) ∧
    (∀ x : ℂ, x ∉ Formalism.MainNotions.TaylorLogMetric.Qbar → Formalism.MainNotions.TaylorLogMetric.lamC lam x = 0)

def PSerIota : Prop :=
  ∀ (D : D7) (N N' p : ℕ) [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), IotaExt lam ι →
    ∀ G : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ, AlgCoef D G →
      Formalism.MainNotions.TaylorLogMetric.pSer D lam G = MvPowerSeries.map ι.toRingHom (taylorSer D G)

end Formalism.L2.KerInert
