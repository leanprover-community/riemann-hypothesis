module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LMulBeta
public import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.NonemptyAlgebra
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

theorem acris0_le_sa : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), ϖ.untilt = ((l : ℕ) : Per.OC l) →
    ∀ a : Per.Acris0 l, (a : Per.AinfP l) ∈ Sa ϖ := by
  intro l _ ϖ hϖ a
  obtain ⟨_, _, -, -, hK, -⟩ := GlobalTheory.AinfChecks.padicComplex l
  have hk : RingHom.ker (Per.θ l) = Ideal.span {((l : ℕ) : Per.Ainf l) - Per.tm ϖ} := (hK ϖ hϖ).1
  refine GlobalTheory.RingIface.acris0_le l (Sa ϖ) ?_ a.2
  intro x hx n y hn
  have hx2 : x ∈ Ideal.span {((l : ℕ) : Per.Ainf l) - Per.tm ϖ} := hk ▸ RingHom.mem_ker.2 hx
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx2
  obtain ⟨c', hc⟩ := GlobalTheory.RingBasics.exists_pow_div_factorial l n
  have hc' : ((n.factorial : ℕ) : Per.AinfP l) * algebraMap (Per.Ainf l) (Per.AinfP l) (Per.zA l c') =
      ((l : ℕ) : Per.AinfP l) ^ n := by
    have h := congrArg ((algebraMap (Per.Ainf l) (Per.AinfP l)).comp (Per.zA l)) hc
    rwa [map_mul, map_natCast, map_pow, map_natCast, RingHom.comp_apply] at h
  have hX : algebraMap (Per.Ainf l) (Per.AinfP l) (c * (((l : ℕ) : Per.Ainf l) - Per.tm ϖ)) =
      -algebraMap (Per.Ainf l) (Per.AinfP l) c * (((l : ℕ) : Per.AinfP l) * beta ϖ) := by
    rw [l_mul_beta, map_mul, map_sub, map_natCast]; ring
  have key : y = algebraMap (Per.Ainf l) (Per.AinfP l) (Per.zA l c') *
      (-algebraMap (Per.Ainf l) (Per.AinfP l) c) ^ n * beta ϖ ^ n := by
    apply (GlobalTheory.RingBasics.isUnit_nat l n.factorial n.factorial_ne_zero).mul_left_cancel
    rw [hn, hX, mul_pow, mul_pow, ← hc']
    ring
  rw [key]
  exact mul_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (pow_mem (neg_mem (Subalgebra.algebraMap_mem _ _)) _))
    (pow_mem (Algebra.self_mem_adjoin_singleton _ _) _)

end GlobalTheory.Pst.StLat
