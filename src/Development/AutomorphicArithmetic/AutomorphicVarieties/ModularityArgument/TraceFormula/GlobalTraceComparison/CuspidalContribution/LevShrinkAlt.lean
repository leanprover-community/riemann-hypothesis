module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.LevShrink
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsOpenLevelNormalizedByIntegralFiniteGL
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.IwasawaCompletion.AwayPartMulIotaWPart
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.BindPow

@[expose] public section

open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp
open GroundTheory.Automorphic.AdelicGLn

private theorem int_iff {E : Type} [Field E] [NumberField E] {N : ℕ} (u : GL (Fin N) (Af E)) :
    u ∈ integralFiniteGL E N ↔ ∀ w, GeneralLinearGroup.map (pLoc E w) u ∈ KGL w (n := N) := by
  rw [mem_integralFiniteGL_iff]
  refine ⟨fun h w => GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => h.1 i j w, fun i j => ?_⟩, fun h => ⟨fun i j w =>
    (GlobalTheory.AdelicU.mem_GLint_iff.1 (h w)).1 i j, fun i j w => ?_⟩⟩
  · rw [← map_inv]
    exact h.2 i j w
  · have := (GlobalTheory.AdelicU.mem_GLint_iff.1 (h w)).2 i j
    rwa [← map_inv] at this

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.levShrink :
    LevShrink := by
  intro E _ _ _ N bad K ho hl
  obtain ⟨L, hL, hle, hconj, -⟩ := UpperTheory.exists_open_level_normalized_by_integralFiniteGL E N K ho
  let K' : Subgroup (GL (Fin N) (Af E)) :=
    { carrier := {u | u ∈ integralFiniteGL E N ∧ ∀ c ∈ integralFiniteGL E N, c⁻¹ * u * c ∈ K}
      one_mem' := ⟨one_mem _, fun c _ => by simpa using K.one_mem⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun c hc => by
        simpa [mul_assoc] using K.mul_mem (ha.2 c hc) (hb.2 c hc)⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun c hc => by simpa [mul_assoc] using K.inv_mem (ha.2 c hc)⟩ }
  refine ⟨K', fun u hu => by simpa using hu.2 1 (one_mem _), ⟨?_, fun u hu => (int_iff u).1 hu.1, fun w hw k hk => ⟨?_, fun c hc => ?_⟩⟩,
    fun c hc u hu => ?_⟩
  · exact Subgroup.isOpen_mono (H₁ := L ⊓ integralFiniteGL E N) (fun u hu => ⟨hu.2, fun c hc => hle (hconj c hc u hu.1)⟩)
      (hL.inter (isOpen_integralFiniteGL E N))
  · refine (int_iff _).2 fun v => ?_
    by_cases h : v = w
    · subst h; rwa [pLoc_locGL]
    · rw [pLoc_locGL_of_ne h]; exact one_mem _
  · have h1 := (int_iff c).1 hc w
    have e : c⁻¹ * locGL E N w k * c = locGL E N w ((GeneralLinearGroup.map (pLoc E w) c)⁻¹ * k * GeneralLinearGroup.map (pLoc E w) c) :=
      PositivityTheory.Rg.Rs.C3.Fl.glAf_ext fun v => by
        by_cases h : v = w
        · subst h; simp only [map_mul, map_inv, pLoc_locGL]
        · simp only [map_mul, map_inv, pLoc_locGL_of_ne h, mul_one, inv_mul_cancel, inv_one]
    rw [e]
    exact hl w hw _ (mul_mem (mul_mem (inv_mem h1) hk) h1)
  · have h1 := (int_iff c).2 hc
    exact ⟨mul_mem (mul_mem (inv_mem h1) hu.1) h1, fun c' hc' => by simpa [mul_assoc] using hu.2 (c * c') (mul_mem h1 hc')⟩
