module

public import Formalism.LocalToGlobal.PairingIndexBounds.PendingAdmissibility.LocalFDerivAdmissibility.AdmRed
public import Formalism.LocalToGlobal.PairingIndexBounds.PendingAdmissibility.LocalFDerivAdmissibility.RepRed
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.PowerSeriesNecessity

namespace Formalism.L2.KerInert

def LowZC {p : ℕ} [Fact p.Prime] (X : Sys p) (be : MvPowerSeries (Fin 2) (Formalism.MainNotions.FormalGroupSystem.K0 p)) (j : ℕ) (v : X.Pl) : Prop :=
  letI := wittFractionAlgebraCp p
  ∀ U : MvPowerSeries (X.EA j ⊕ X.EA j) ℂ_[p], IntR (OcC p) (inParamK p ℂ_[p] U) →
    ∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
      GeZ (AddMonoidAlgebra.coeff (applyD (X.PIv j I v)
        (X.ThZA ℂ_[p] j (MvPowerSeries.map (algebraMap (Formalism.MainNotions.FormalGroupSystem.K0 p) ℂ_[p])
          (expS p (-(∑ e : Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)),
            sub2 p be (MvPowerSeries.X (Sum.inl (⟨v, e⟩ : X.EA j))) (MvPowerSeries.X (Sum.inr (⟨v, e⟩ : X.EA j)))))) * U))) n)

def FirstKernelLocalOfGeneral : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (be : MvPowerSeries (Fin 2) (Formalism.MainNotions.FormalGroupSystem.K0 p)) {T : Type}
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]),
    RepresentativeCondition X E hfin be pos F → LocalRepresentativeCondition X E hfin be pos F

def Adm3OfK1LowerBound : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (be : MvPowerSeries (Fin 2) (Formalism.MainNotions.FormalGroupSystem.K0 p)) {T : Type}
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]),
    (∀ j < X.mm, ∀ v, LowZC X be j v) → RepresentativeCondition X E hfin be pos F → Adm3Rep X E hfin pos F

end Formalism.L2.KerInert
