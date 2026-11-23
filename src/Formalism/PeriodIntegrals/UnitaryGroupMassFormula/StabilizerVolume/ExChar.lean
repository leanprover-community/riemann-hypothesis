module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.VolStabFromSWS
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem exChar_holds : ExChar := by
  intro F E _ _ _ _ _ σ hE M J _hJ _ha hc a _ha1 ha2 _X0 _hT _hdet
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hE.2.2.1]; norm_num)
  let b := Module.finBasis F E
  have h0 : 2 * 0 < M := by omega
  have hrd : RapidDecay b (fun _ : Fin 0 → Fin M → Ainf F ⊗[F] E => (1 : ℂ)) :=
    fun N => ⟨1, fun X => by simp [sizeTup]⟩
  have hpf : IsPureFin b (fun _ : Fin 0 → Fin M → Af F ⊗[F] E => (1 : ℂ))
      (fun v (_ : Fin 0 → Fin M → Fv F v ⊗[F] E) => (1 : ℂ)) := by
    refine ⟨fun v => ⟨IsLocallyConstant.const 1, ?_⟩, Filter.Eventually.of_forall fun v => ?_,
      fun X => by simp⟩
    · exact (Set.subsingleton_of_subsingleton).isCompact
    · funext X
      simp [latV, Set.indicator]
  have hS := hc 0 h0 (0 : Matrix (Fin 0) (Fin 0) E) (fun i => Fin.elim0 i) (by simp)
    (Module.finrank F E) b (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ _ => 1)
    continuous_const hrd (Formalism.L2.SG.Pf.NcWeil.isSmoothCc_empty _) hpf (fun _ => by simp)
  obtain ⟨μ, hμ⟩ := hS.1
  obtain ⟨𝓕, h𝓕⟩ := (hS.2 μ hμ).1
  exact ((hS.2 μ hμ).2 𝓕 h𝓕).1

end PI.VolStabS
