module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevTransportHer
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PTie

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

def LevTransportU : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq))
    (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (Bs : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → Bs.z = z → Bs.z' = z' → Bs.π = π → Bs.π' = π' →
    ∀ (i : Fin (P.r + 1)),
    ∃ Tw : D.LevTower P.k P.r Wp Wq, D.TowerNormalised Tw ∧
      Tw.base.z = z ∧ Tw.base.z' = z' ∧ Tw.base.π = π ∧ Tw.base.π' = π' ∧
    ∃ (Di : B.RealPlaceData P.k (P.r - i) Wp Wq)
      (Xi : ActualOps (JC.parLev P i).k (JC.parLev P i).r Di.z Di.z' Di.π Di.π') (μi : Measure (Mt P.k (P.r - i)))
      (Li : R.LevelData (Pr (RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π')) (P.r - i))
      (sti : Fr.Start (Pr (RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π'))) (κ : ℝ),
      Di = Tw.bs i ∧ 0 < κ ∧ IsData (JC.parLev P i) Di.z Di.z' Di.π Di.π' Xi μi Li sti l0 ∧
      ∀ (c : Fin P.r → ℂ), (∀ l : Fin P.r, l.val < i.val → c l ≠ 0) →
      ∃ T : RadSp P.k P.r z z' π π' →ₗ[ℂ] RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π',
        LevTrClauses P μ L st l0 i c Di μi Li sti T ∧
        ∀ Φ Ψ c'', pairAt μi (T Φ) (T Ψ) c'' = (κ : ℂ) * pairAt μ Φ Ψ (glue i c (shiftCf i c''))

end Formalism.FourierDecayAlt.P.PTie
