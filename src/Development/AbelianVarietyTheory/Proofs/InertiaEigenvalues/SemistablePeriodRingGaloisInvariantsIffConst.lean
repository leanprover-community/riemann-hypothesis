module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KummerNotFrac
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem stInv_iff : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l)
    (x : Bst P), (∀ g : ↥(GK K), actSt P (g : GQ l) x = x) ↔
      ∃ c : ↥(K0 K), x = Polynomial.C (algebraMap ↥(K0 K) P.R.B c) := by
  intro l _ P AI T K x
  constructor
  · intro h
    obtain ⟨hdom, h2, -⟩ := GlobalTheory.Pst.stRegular l P AI ⟨T⟩
    haveI := hdom
    obtain ⟨c, hcK, hc⟩ := h2 K 1 x one_ne_zero fun g => by rw [map_one, h g, one_mul]
    have hmem : (c : Om l) ∈ K0 K := IntermediateField.mem_inf.2 ⟨hcK, c.2⟩
    refine ⟨⟨c, hmem⟩, ?_⟩
    rw [hc, mul_one, Polynomial.algebraMap_apply]
    rfl
  · rintro ⟨c, rfl⟩ g
    have hc : (c : Om l) ∈ (K.1 : IntermediateField ℚ_[l] (Om l)) := (IntermediateField.mem_inf.1 c.2).1
    have hg : (g : GQ l) (c : Om l) = (c : Om l) := (mem_fixingSubgroup_iff _).1 g.2 _ hc
    have hK0 : algebraMap ↥(K0 K) P.R.B c =
        algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ⟨c, (IntermediateField.mem_inf.1 c.2).2⟩ := rfl
    rw [actSt]
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, stHom_apply, Polynomial.map_C, Polynomial.C_comp]
    congr 1
    rw [hK0]
    exact P.actQ_Kur _ _ _ hg

end GlobalTheory.PMon
