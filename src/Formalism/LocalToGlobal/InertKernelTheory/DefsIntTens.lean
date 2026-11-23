module

public import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
public import Mathlib.RingTheory.MvPowerSeries.Rename
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

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

def blkPt (D : D7) {N N' n n' m m' : ℕ} (eR : Fin N' ≃ Fin n' × Fin m') (eC : Fin N ≃ Fin n × Fin m)
    (I : Fin n') (J : Fin n) (z : VC D N N') : VC D m m' :=
  fun τ u v => z τ (eR.symm (I, u)) (eC.symm (J, v))

def blkIdx (D : D7) {N N' n n' m m' : ℕ} (eR : Fin N' ≃ Fin n' × Fin m') (eC : Fin N ≃ Fin n × Fin m)
    (I : Fin n') (J : Fin n) (k : D.what₂.Tau × Fin m' × Fin m) : D.what₂.Tau × Fin N' × Fin N :=
  (k.1, eR.symm (I, k.2.1), eC.symm (J, k.2.2))

def TaylorProductOverBlocks : Prop :=
  ∀ (D : D7) (N N' n n' m m' : ℕ) (eR : Fin N' ≃ Fin n' × Fin m') (eC : Fin N ≃ Fin n × Fin m)
    (G : Fin n' → Fin n → VC D m m' → ℂ), (∀ I J, AnalyticOnNhd ℂ (G I J) Set.univ) →
    taylorSer D (fun z => ∏ I, ∏ J, G I J (blkPt D eR eC I J z)) =
      ∏ I, ∏ J, MvPowerSeries.rename (blkIdx D eR eC I J) (taylorSer D (G I J))

end Formalism.L2.KerInert
