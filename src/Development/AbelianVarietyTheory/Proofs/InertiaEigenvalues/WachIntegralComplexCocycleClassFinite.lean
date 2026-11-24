module

public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GeomSumOneAddPrime
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrCocyclePolesFrobeniusQCrystallineStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrH1Description
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachOfFrobeniusGammaStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingsCyclotomic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.IntComplex



theorem ring_part (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL) :
    let W := (HW l).W K s LL h
    (∃ w, W.γA W.gam W.Q = w * W.Q ∧ w - 1 ∈ Ideal.span {W.X}) ∧ ∃ b, W.X = letπ * b := by
  intro W
  obtain ⟨χ, -, -, hγ, hX, hQ, -, -⟩ := GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL h
  have hs : 1 ≤ s := h.1
  obtain ⟨-, -, -, -, -, hact, -⟩ := GlobalTheory.Cyc.XX_QQ_properties l ↥(OL LL) s hs
  obtain ⟨-, b, hb⟩ := hact (χ W.gam)
  refine ⟨⟨1 + W.X * fun _ => b, ?_, ?_⟩, ?_⟩
  · funext i
    change W.γ₀ W.gam (W.Q i) = (1 + W.X i * b) * W.Q i
    rw [hγ, hX, hQ, hb, mul_comm]
  · rw [add_sub_cancel_left]
    exact Ideal.mem_span_singleton.2 (dvd_mul_right _ _)
  · obtain ⟨c, hc⟩ : (PowerSeries.X : PowerSeries ↥(OL LL)) ∣ GlobalTheory.Cyc.XX l ↥(OL LL) s := by
      rw [PowerSeries.X_dvd_iff, GlobalTheory.Cyc.XX]
      simp
    refine ⟨fun _ => c, ?_⟩
    funext i
    change W.X i = PowerSeries.X * c
    rw [hX, hc]



theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Pr2c D HW F := by
  intro D HW F l _ K s LL h T M hh hT _
  obtain ⟨h1, b, hb⟩ := ring_part D HW l K s LL h
  refine ⟨h1, fun y z hy hz hc => ?_⟩
  have hz' : z ∈ aN ((HW l).W K s LL h) T letπ := by
    obtain ⟨x, hx, rfl⟩ := hz
    refine ⟨b • x, Submodule.smul_mem _ b hx, ?_⟩
    simp only [smulA, LinearMap.smul_apply, LinearMap.id_apply]
    rw [hb, mul_smul]
  refine ⟨?_, fun h0 => ?_⟩
  · refine GlobalTheory.T.herrCocycle_poles_frobeniusQ_crystalline D HW F l K s LL h T hT (Multiset.replicate (mx M) 0) y z ?_ hz' hc
    rw [Multiset.map_replicate, Multiset.prod_replicate, pow_zero]
    exact hy
  · obtain ⟨m, hm⟩ := ((GlobalTheory.NL.HerrComplexH1.herr_H1_description D HW F l K s LL h T hT).1.2 ⟨(y, z), hc⟩).1 h0
    have hm1 : y = ((HW l).W K s LL h).φD T m - m := congrArg Prod.fst hm
    have hm2 : z = ((HW l).W K s LL h).γ T m - m := congrArg Prod.snd hm
    refine ⟨m, GlobalTheory.T.mem_wach_of_frobenius_gamma D HW F l K s LL h T hT (mx M) m ?_ ?_, hm1, hm2⟩
    · exact hm1 ▸ hy
    · exact hm2 ▸ hz'

end GlobalTheory.NL.IntComplex
