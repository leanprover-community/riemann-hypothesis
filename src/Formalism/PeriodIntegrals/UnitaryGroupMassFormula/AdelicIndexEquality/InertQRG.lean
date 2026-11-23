module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.ChiEqOneOfClosure
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.InertGen
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

namespace PI.UnitaryGroupMassFormula.AdIndexEq

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S

theorem sigV_tmul (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v)
    (e : I.E) : sigV I v (x ⊗ₜ e) = x ⊗ₜ star e := by
  change (Algebra.TensorProduct.map (AlgHom.id I.F _) I.cm.sig) (x ⊗ₜ e) = _
  exact Algebra.TensorProduct.map_tmul _ _ _ _

theorem sigV_invol (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) : sigV I v (sigV I v a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul x e => rw [sigV_tmul, sigV_tmul, star_star]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem sigV_inclV (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (e : I.E) :
    sigV I v (inclV I v e) = inclV I v (star e) := by
  exact sigV_tmul I v 1 e

theorem herm_V (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    Formalism.UG.cT (sigV I v) (I.J.map (inclV I v)) = I.J.map (inclV I v) := by
  funext i j
  have h : starRingEnd I.E (I.J j i) = I.J i j := congrFun (congrFun I.J_herm i) j
  show sigV I v (inclV I v (I.J j i)) = inclV I v (I.J i j)
  rw [sigV_inclV]
  exact congrArg (inclV I v) h

theorem q_reflection_generation : QReflGen := by
  intro I v hv g
  let _ : Field (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) := hv.toField
  have hinj : Function.Injective (inclV I v) := (inclV I v).injective
  have hdet : (I.J.map (inclV I v)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    intro h
    exact I.J_det (hinj (by rw [h, map_zero]))
  have h2 : (2 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) ≠ 0 := by
    intro h
    have : inclV I v 2 = inclV I v 0 := by rw [map_ofNat, map_zero]; exact h
    exact two_ne_zero (hinj this)
  exact QRG.mem_S (sigV I v) (I.J.map (inclV I v)) (sigV_invol I v) (herm_V I v) hdet h2 g

theorem locInertChi_of_qReflPow (hP : QReflPow) : LocInertChi := by
  intro I v hv χ _ _ hK g
  have hq : {s : Uv I v | IsQRefl I v s} ⊆ (χ.ker : Set (Uv I v)) := by
    intro s hs
    obtain ⟨m, hm, hmK⟩ := hP I v hv s hs
    exact MonoidHom.mem_ker.mpr (hK s ⟨m, hm, hmK⟩)
  exact MonoidHom.mem_ker.mp ((Subgroup.closure_le _).mpr hq (q_reflection_generation I v hv g))

end PI.UnitaryGroupMassFormula.AdIndexEq

end
