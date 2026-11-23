module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IoYStOfIoPair
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.Chain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.InnerLift

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def InnerSteps : Prop :=
  ∀ t (k : Fin D.R.m), (k : ℕ) + 1 < D.R.m → IsStepWeil k R.ψ (Yc D k) (Yc D (k + 1)) (R.ωY t k) ∧
    IsVacVec R.ψ R.θ (R.MY k) (R.MY (k + 1)) (R.vY t k)

def InnerLaws : Prop :=
  ∀ t k, k + 1 < D.R.m → ∀ κ ∈ levS _ (R.βY k) (R.datYt t k R.triv), κ ∈ GfC (Yc D k) ∧
    R.ωY t k (κ, 1) (R.vY t k) = levChi _ (R.βY k) (R.datYt t k R.triv) κ • R.vY t k

theorem haar_fund (hν : R.models_νY) (hν' : R.models_νY') (t : T) (j : ℕ) (hj : j < D.R.m) :
    (R.νY t j).IsHaarMeasure ∧ MeasureTheory.IsFundamentalDomain (GQ (Yc D j)) (R.fdY t j) (R.νY t j) := by
  by_cases h : j + 1 < D.R.m
  · exact ⟨(hν t j h).1.1, (hν t j h).2⟩
  · have e : j = D.R.m - 1 := by omega
    subst e
    exact ⟨(hν' t).1.1, (hν' t).2⟩

theorem ioYSt_of_inner (hP : IoPair D) (hC : ∀ k, ChainPar D k) (hθ : IsInfFam R.θ) (hS : InnerSteps R)
    (hL : InnerLaws R) (hν : R.models_νY) (hν' : R.models_νY') (hI : R.chain_ItY) : IoYSt R := by
  intro t k hk
  have hk0 : k < D.R.m := by omega
  obtain ⟨hW, hV⟩ := hS t ⟨k, hk0⟩ hk
  exact hP.of_index_eq ⟨k, hk0⟩ (min k D.R.m) (min (k + 1) D.R.m) (min_eq_left hk0.le) (min_eq_left hk.le)
    (Yc D k) (Yc D (k + 1)) (R.MY k) (R.MY (k + 1)) R.θ R.ψ hθ (hC _) (R.ωY t k) (R.vY t k) hW hV
    (R.ItY k) (hI t k hk) _ _ (hL t k hk) _ _ (haar_fund R hν hν' t _ hk).1 (haar_fund R hν hν' t _ hk).2
    _ _ (R.CC t (k + 1)) le_rfl

theorem exists_ioY_of_ioYSt (h : IoYSt R) : ∃ io, ({ R with ioY := io } : RealDat D A Ks).chain_ioY := by
  classical
  have key : ∀ t k, ∃ io : R.CC t (k + 1) →ₗ[ℂ] R.CC t k, k + 1 < D.R.m →
      Lift.IsIo (R.νY t (k + 1)) (R.fdY t (k + 1)) (thetaKO (R.ωY t k)) (R.ptY t k) (R.ItY k)
        (R.CC t (k + 1)) (R.CC t k) io := by
    intro t k
    by_cases hk : k + 1 < D.R.m
    · obtain ⟨io, hio⟩ := h t k hk
      exact ⟨io, fun _ => hio⟩
    · exact ⟨0, fun h' => absurd h' hk⟩
  choose io hio using key
  exact ⟨io, fun t k hk => hio t k (by omega)⟩

theorem exists_ioY_of_pair (hP : IoPair D) (hC : ∀ k, ChainPar D k) (hS : InnerSteps R) (hL : InnerLaws R)
    (hM : R.IsModels) (hI : R.chain_ItY) : ∃ io, ({ R with ioY := io } : RealDat D A Ks).chain_ioY :=
  exists_ioY_of_ioYSt R (ioYSt_of_inner R hP hC hM.inf hS hL hM.νY hM.νY' hI)

end GlobalTheory.Chain.InnerLift

end
