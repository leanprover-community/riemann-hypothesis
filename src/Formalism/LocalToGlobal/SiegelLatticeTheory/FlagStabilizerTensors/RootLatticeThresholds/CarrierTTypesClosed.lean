module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTTypes
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowKAllPos
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NotCdomRaiseOfLt
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianCurvature.CapelliDeterminantAndBranching
public import Formalism.HermitianCurvature.FrameExists2
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BaseOfCore
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BuiltPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierParts

@[expose] public section

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built

private theorem list_prod_apply_eq_foldr {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (l : List (Module.End ℂ W)) (v : W) :
    l.prod v = List.foldr (fun (T : W → W) (h : W) => T h) v
      (l.map (fun (T : Module.End ℂ W) => (T : W → W))) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.prod_cons, Module.End.mul_apply, ih]

private theorem qmF_eq_qdet_apply {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℕ}
    (E : Fin m → Fin m → Module.End ℂ W) (w : ℂ) (v : W) :
    Formalism.FourierDecayAlt.Q.qmF (fun a b => (E a b : W → W)) id id w v = (Formalism.REAL.qdet E w) v := by
  simp only [Formalism.FourierDecayAlt.Q.qmF, Formalism.REAL.qdet, Formalism.REAL.qminor]
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Module.End.mul_apply, Module.End.intCast_apply, list_prod_apply_eq_foldr, List.map_ofFn]
  rw [← Int.cast_smul_eq_zsmul ℂ]
  congr 2
  congr 1
  funext j y
  simp only [Function.comp, Formalism.REAL.Tm, id]
  split_ifs <;> simp [Module.algebraMap_end_apply, sub_smul, Nat.cast_smul_eq_nsmul]

theorem capacity_from_hermitian_char : CapFromHC := by
  intro Wp _ _ k r z u π hz hT hrep hcont hHC
  obtain ⟨g, ⟨hgU, hgfix, hgz⟩, hU⟩ := hHC
  haveI : FiniteDimensional ℂ Wp := hU.2.1
  intro Bs hBs w v
  have hfr := Formalism.FourierDecayAlt.P.QrCap.fr_frame hgU hgfix _ hgz
  have hcore := Formalism.FourierDecayAlt.P.QrCap.core (u := u) hz hT ⟨hrep, hcont⟩ hgU hgfix _ hgz hU.2.2.2 w v
  have hE : (fun a b => Formalism.FourierDecayAlt.Q.EcRep (Formalism.QuantumDeterminants.Hpk k r) π (Formalism.FourierDecayAlt.Q.unitB (Formalism.QuantumDeterminants.Hpk k r) Bs a b))
      = fun a b => ((Formalism.FourierDecayAlt.Qr.EB π Bs a b : Module.End ℂ Wp) : Wp → Wp) := by
    funext a b y
    exact Formalism.FourierDecayAlt.P.QrD.ecRep_eq hrep hcont (Formalism.FourierDecayAlt.P.QrD.frame_lie hBs a b).1
      (Formalism.FourierDecayAlt.P.QrD.frame_lie hBs a b).2 y
  have hcap : Formalism.FourierDecayAlt.Q.capRep k r π Bs w v = (Formalism.REAL.qdet (Formalism.FourierDecayAlt.Qr.EB π Bs) w) v := by
    simp only [Formalism.FourierDecayAlt.Q.capRep]
    rw [hE, qmF_eq_qdet_apply]
  rw [hcap, Formalism.FourierDecayAlt.P.QrCap.capChange hz hT ⟨hrep, hcont⟩ hBs hfr w, hcore]
  congr 1
  simp only [Formalism.FourierDecayAlt.Qr.cpol, Formalism.FourierDecayAlt.P.QrCap.lowK_allPos]
  have hI : Finset.Icc 1 k = (Finset.range k).map ⟨Nat.succ, Nat.succ_injective⟩ := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · intro h
      exact ⟨i - 1, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩
      omega
  rw [hI, Finset.prod_map, Finset.prod_range]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  simp [Nat.succ_sub_one, j.isLt]
  push_cast
  ring

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)

end Formalism.L2.SG.Pf.CarrierT
