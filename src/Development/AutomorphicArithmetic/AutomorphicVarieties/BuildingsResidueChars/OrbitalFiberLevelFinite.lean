module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibCon
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberDetEqOne
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Loc

private theorem comap_relIndex_ne_zero {G H : Type} [Group G] [Group H] (p : G →* H) (A B : Subgroup H)
    (T : Subgroup G) (hAB : A.relIndex B ≠ 0) (hT : ∀ g ∈ T, p g ∈ B) : (A.comap p).relIndex T ≠ 0 := by
  rw [Subgroup.relIndex_comap]
  intro h
  exact hAB (Subgroup.relIndex_eq_zero_of_le_right (Subgroup.map_le_iff_le_comap.mpr hT) h)

private theorem finset_relIndex_ne_zero {G I : Type} [Group G] (H : I → Subgroup G) (T : Subgroup G) (S : Finset I)
    (h : ∀ v ∈ S, (H v).relIndex T ≠ 0) : ∃ W : Subgroup G, W.relIndex T ≠ 0 ∧ ∀ v ∈ S, W ≤ H v := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨⊤, by simp, by simp⟩
  | insert a S ha ih =>
    obtain ⟨W, hW, hWS⟩ := ih (fun v hv => h v (Finset.mem_insert_of_mem hv))
    refine ⟨H a ⊓ W, Subgroup.relIndex_inf_ne_zero (h a (Finset.mem_insert_self a S)) hW, ?_⟩
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact inf_le_left
    · exact inf_le_right.trans (hWS v hv)

theorem UpperTheory.orbitalFiber_level_finite :
    UpperTheory.V.Z.Sym.Glob.Fib.LevFin := by
  unfold Fib.LevFin
  intro F _ _ Δ D hD
  have hDet : Fib.DetOne := UpperTheory.orbitalFiber_det_eq_one
  unfold Fib.DetOne at hDet
  set P := rpg (fun v => ↥(DX ((cv v) Δ))) (fun v => KD ((cv v) Δ) (Ov v)) with hP
  have hle : ∀ v, D.J2v v ≤ KD ((cv v) Δ) (Ov v) := by
    intro v
    rw [Dat.J2v.eq_1]
    split_ifs with hv
    · exact SigOk.levelTwoLeIntegral (hD.sig v hv)
    · exact le_rfl
  have hT : ∀ v, ∀ g ∈ D.UZ ⊓ SA Δ, P.p v g ∈ KD ((cv v) Δ) (Ov v) := by
    intro v g hg
    have h1 : g ∈ D.UZ := hg.1
    have h2 : g ∈ SA Δ := hg.2
    rw [Dat.UZ.eq_1, RPG.box.eq_1, Subgroup.mem_iInf] at h1
    rw [SA.eq_1, Subgroup.mem_iInf] at h2
    have a := h1 v
    have b := h2 v
    rw [Subgroup.mem_comap] at a b
    exact hDet _ _ _ _ (sup_le_sup_left (hle v) _ a) b
  have hfin : ∀ v ∈ D.Sg, ((D.J2v v).comap (P.p v)).relIndex (D.UZ ⊓ SA Δ) ≠ 0 := by
    intro v hv
    apply comap_relIndex_ne_zero (P.p v) (D.J2v v) (KD ((cv v) Δ) (Ov v))
    · rw [Dat.J2v.eq_1, if_pos hv]
      exact SigOk.levelTwoFiniteIndex (hD.sig v hv)
    · exact hT v
  obtain ⟨W, hW, hWS⟩ := finset_relIndex_ne_zero (fun v => (D.J2v v).comap (P.p v)) _ D.Sg hfin
  have hsub : W ⊓ (D.UZ ⊓ SA Δ) ≤ D.U2 := by
    intro g hg
    rw [Dat.U2.eq_1, RPG.box.eq_1, Subgroup.mem_iInf]
    intro v
    rw [Subgroup.mem_comap]
    by_cases hv : v ∈ D.Sg
    · exact hWS v hv hg.1
    · have e := hT v g hg.2
      rw [Dat.J2v.eq_1, if_neg hv]
      exact e
  refine ⟨?_, ?_⟩
  · rw [Dat.U2.eq_1, Dat.UZ.eq_1, RPG.box.eq_1, RPG.box.eq_1]
    exact iInf_mono fun v => Subgroup.comap_mono le_sup_right
  · intro h
    apply hW
    rw [← Subgroup.inf_relIndex_right]
    exact Subgroup.relIndex_eq_zero_of_le_left hsub h
