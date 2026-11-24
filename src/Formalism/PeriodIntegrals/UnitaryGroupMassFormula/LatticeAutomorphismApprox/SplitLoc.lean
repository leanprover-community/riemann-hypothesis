module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.LocDefs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.LocSplitChiOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.NatCastTmul
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.SplitGen
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
import Mathlib.RingTheory.Valuation.AlgebraInstances
public import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists

theorem locSplitP_dec (I : AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E) (Rf : RefData I g r k e f)
    (v : HeightOneSpectrum (𝓞 I.F)) (hsum : SumOne I v (PI.FinKW.psiV I v Rf.ew)) :
    ∃ p1 : RV I v →+* KV I v, IsAdaptedFirstProjection I v (PI.FinKW.psiV I v Rf.ew) p1 ∧
      ∀ x : RV I v, x = algebraMap (KV I v) (RV I v) (p1 x) * PI.FinKW.psiV I v Rf.ew +
        algebraMap (KV I v) (RV I v) (p1 (PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v x)) *
          PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew) := by
  have : CharZero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) :=
    charZero_of_injective_algebraMap (algebraMap I.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v)).injective
  have h2K : (2 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) ≠ 0 := two_ne_zero
  obtain ⟨p1, h1, h2, h3, h4⟩ := exists_adapted_first_projection (K := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) I.cm.sig
    (PI.UnitaryGroupMassFormula.AdIndexEq.spl_sig_sig I) (PI.UnitaryGroupMassFormula.AdIndexEq.spl_sig_fix I) I.cm.deg2 h2K
    (PI.FinKW.psiV I v Rf.ew) hsum (eps_orth Rf v)
  refine ⟨p1, ⟨h1, h2, h3, ?_⟩, h4⟩
  rintro x ⟨z, rfl⟩
  obtain ⟨fp, hm, hf⟩ := NumberField.RingOfIntegers.isIntegral_coe z
  have hf' : Polynomial.eval₂ (algebraMap ℤ I.E) (algebraMap (𝓞 I.E) I.E z) fp = 0 := hf
  show (p1.comp (PI.UnitaryGroupMassFormula.AdIndexEq.inclV I v)) (algebraMap (𝓞 I.E) I.E z) ∈ OV I v
  refine (Valuation.valuationSubring.integers (Valued.v (R := v.adicCompletion I.F))).mem_of_integral
    ⟨fp.map (Int.castRingHom _), hm.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have hc : (algebraMap (Valued.v (R := v.adicCompletion I.F)).valuationSubring (v.adicCompletion I.F)).comp
      (Int.castRingHom (Valued.v (R := v.adicCompletion I.F)).valuationSubring) =
      (p1.comp (PI.UnitaryGroupMassFormula.AdIndexEq.inclV I v)).comp (algebraMap ℤ I.E) := RingHom.ext_int _ _
  rw [hc, ← Polynomial.hom_eval₂, hf', map_zero]

theorem local_splitting_projection : LocSplitP := by
  intro I g r k e f Rf v hsum
  obtain ⟨p1, hp, -⟩ := locSplitP_dec I g r k e f Rf v hsum
  exact ⟨p1, hp⟩

end PI.UnitaryGroupMassFormula.ScXuExists
