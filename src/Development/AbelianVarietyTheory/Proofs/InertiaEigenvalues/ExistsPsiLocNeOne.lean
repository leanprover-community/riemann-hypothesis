module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionHeisenbergInvariant
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep Formalism.UG

namespace GlobalTheory.StdCharConductor

variable (E : Type) [Field E] [NumberField E]

def psi : AddChar (Ad E) ℂ := Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)

theorem psi_apply (x : Ad E) : psi E x = (GroundTheory.Global.adelicChar E x : ℂ) := rfl

variable {E}

theorem psi_loc (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    psi E (sFin E (sLoc E w y)) = (GroundTheory.Global.localAdelicChar E w y : ℂ) := by
  classical
  rw [psi_apply, GroundTheory.Global.localAdelicChar_apply]
  congr 2

theorem psi_loc_eq_one_iff (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    psi E (sFin E (sLoc E w y)) = 1 ↔ GroundTheory.Global.localAdelicChar E w y = 1 := by
  rw [psi_loc]
  exact Circle.coe_eq_one

theorem exists_psi_loc_ne_one (w : HeightOneSpectrum (𝓞 E)) :
    ∃ y : w.adicCompletion E, psi E (sFin E (sLoc E w y)) ≠ 1 := by
  by_contra h
  push Not at h
  refine GroundTheory.Global.localAdelicChar_ne_one (K := E) w (DFunLike.ext _ _ fun y => ?_)
  rw [AddChar.one_apply]
  exact (psi_loc_eq_one_iff w y).1 (h y)


variable (E) in
theorem stdPsi_psi : StdPsi (psi E) := by
  have hc : Continuous (psi E) := continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar (K := E))
  have hr : ∀ c : E, psi E (algebraMap E (Ad E) c) = 1 := fun c => by
    rw [psi_apply, GroundTheory.Global.adelicChar_algebraMap]
    rfl
  have hne : psi E ≠ 1 := fun h => GroundTheory.Global.adelicChar_ne_one (K := E) (DFunLike.ext _ _ fun x => by
    have := DFunLike.congr_fun h x
    rw [psi_apply, AddChar.one_apply] at this
    rw [AddChar.one_apply]
    exact Circle.coe_eq_one.1 this)
  letI : Invertible (2 : E) := invertibleOfNonzero two_ne_zero
  letI : Invertible (2 : Ad E) := (Invertible.map (algebraMap E (Ad E)) 2).copy 2 (map_ofNat _ 2).symm
  have h := _root_.UpperTheory.Reformulated.B.UnitaryAnnihilator.unitary_and_annihilator_eq E (psi E) hc hne hr
  exact ⟨hc, h.1, hr, h.2, exists_psi_loc_ne_one⟩

end GlobalTheory.StdCharConductor

end
