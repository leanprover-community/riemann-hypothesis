module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LMulBeta
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Acris0TorsionFree
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFiltrationApproxByEnvelopeKernelPower
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

theorem acris_mem_clos : ∀ (l : ℕ) [Fact l.Prime] (j : Per.Acris l →+* Per.BdRp l), IsCrisP j → ∀ (ϖ : Per.Fl l),
  (∀ a : Per.Acris0 l, (a : Per.AinfP l) ∈ Sa ϖ) → (∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n}) →
  ∀ x : Per.Acris l, j x ∈ Clos (Sg ϖ) (betaD ϖ) := by
  intro l _ j hj ϖ hS hF x n
  obtain ⟨N, hN⟩ := hj.bdd n
  obtain ⟨s, z, rfl⟩ := (acris_basic l).2.2.1 x N
  obtain ⟨a, ha⟩ := hN z
  refine ⟨algebraMap (Per.AinfP l) (Per.BdRp l) ((s : Per.AinfP l) + algebraMap (Per.Ainf l) (Per.AinfP l) a),
    ⟨_, add_mem (hS s) (Subalgebra.algebraMap_mem _ a), rfl⟩, ?_⟩
  rw [← Ideal.mem_span_singleton, ← hF, GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, map_sub, map_add (f := _), map_add (f := _), map_mul, map_pow,
    map_natCast, hj.on0, ev_algebraMap, ev_algebraMap]
  rw [ha, map_add (f := _)]
  ring

end GlobalTheory.Pst.StLat
