module

public import Formalism.PeriodIntegrals.WfSubst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.InvNatMemWf
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.WfSubstProof

theorem exists_lift {A : Type} [CommRing A] (S : Subring A) {σ : Type} (f : MvPowerSeries σ A)
    (h : ∀ e, MvPowerSeries.coeff e f ∈ S) :
    ∃ g : MvPowerSeries σ S, MvPowerSeries.map S.subtype g = f := by
  let g : MvPowerSeries σ S := fun e => ⟨MvPowerSeries.coeff e f, h e⟩
  refine ⟨g, ?_⟩
  ext e
  rw [MvPowerSeries.coeff_map]
  rfl

theorem coeff_map_mem {A : Type} [CommRing A] (S : Subring A) {σ : Type} (g : MvPowerSeries σ S)
    (e : σ →₀ ℕ) : MvPowerSeries.coeff e (MvPowerSeries.map S.subtype g) ∈ S := by
  rw [MvPowerSeries.coeff_map]
  exact (MvPowerSeries.coeff e g).2

theorem substSub : PI.SubstSub := by
  intro A _ S σ f a hf ha ha0 n
  have hf' : ∀ e : Unit →₀ ℕ, MvPowerSeries.coeff e f ∈ S := fun e => by
    have he : e = Finsupp.single () (e ()) := by
      ext
      simp
    rw [he]
    exact hf (e ())
  obtain ⟨fS, rfl⟩ := exists_lift S f hf'
  obtain ⟨aS, rfl⟩ := exists_lift S a ha
  have haS0 : MvPowerSeries.constantCoeff aS = 0 := by
    have h0 := ha0
    rw [MvPowerSeries.constantCoeff_map] at h0
    exact Subtype.val_injective h0
  have hsub : PowerSeries.HasSubst aS := PowerSeries.HasSubst.of_constantCoeff_zero haS0
  have key : PowerSeries.subst (MvPowerSeries.map S.subtype aS) (MvPowerSeries.map S.subtype fS : PowerSeries A) =
      MvPowerSeries.map S.subtype (PowerSeries.subst aS fS) :=
    (PowerSeries.map_subst hsub fS).symm
  rw [key]
  exact coeff_map_mem S _ n

theorem wfSubst : PI.WfSubst := by
  intro p _ σ f a hf ha ha0 n
  have h := substSub ℂ_[p] (ExpIntWProof.Wf p) σ f a (fun m => ExpIntWProof.mem_Wf.2 (hf _))
    (fun m => ExpIntWProof.mem_Wf.2 (ha m)) ha0
  exact ExpIntWProof.mem_Wf.1 (h n)

end PI.WfSubstProof
