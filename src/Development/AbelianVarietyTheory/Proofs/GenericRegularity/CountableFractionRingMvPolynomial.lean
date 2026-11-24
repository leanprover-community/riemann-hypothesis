module

public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.KapFgTrdeg
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRingHomComplexCompEqOfCountable
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Mathlib.Algebra.MvPolynomial.Cardinal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Algebraic.Cardinality
public import Mathlib.RingTheory.Localization.Cardinality
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open NumberField Topology ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory.GenericReading

theorem countable_of_fg_top {K L : Type} [Field K] [Countable K] [Field L] [Algebra K L]
    (h : (⊤ : IntermediateField K L).FG) : Countable L := by
  obtain ⟨s, hs⟩ := h
  have h1 := IntermediateField.cardinalMk_adjoin_le K (s : Set L)
  rw [hs, Cardinal.mk_congr (IntermediateField.topEquiv (F := K) (E := L)).toEquiv] at h1
  refine Cardinal.mk_le_aleph0_iff.1 (h1.trans (max_le (max_le ?_ ?_) le_rfl))
  · exact Cardinal.mk_le_aleph0
  · exact Cardinal.mk_le_aleph0

theorem countable_fractionRing_mvPolynomial (ι L : Type) [Countable ι] [Field L] [Countable L] :
    Countable (FractionRing (MvPolynomial ι L)) := by
  have h : Countable (MvPolynomial ι L) := by
    refine Cardinal.mk_le_aleph0_iff.1 (MvPolynomial.cardinalMk_le_max.trans (max_le (max_le ?_ ?_) le_rfl))
    · exact Cardinal.mk_le_aleph0
    · exact Cardinal.mk_le_aleph0
  refine Cardinal.mk_le_aleph0_iff.1 ?_
  rw [FractionRing.cardinalMk]
  exact Cardinal.mk_le_aleph0

theorem embedding_read_at_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ (h : GenFrEx Xo c) (Z : Comp Xo c), Nonempty (Om Z →ₐ[c.F] CAt σ) ∧ ∀ φ : Om Z →ₐ[c.F] CAt σ, ∃ (k : U.Comp) (x : (U.X k).dom) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k x) y' := by
  intro E _ _ _ H Dw l Xo c σ r U _ hU h Z
  refine ⟨?_, fun φ => ?_⟩
  · have hfin : FiniteDimensional ℚ c.F := c.fin
    have hcF : Countable c.F := Cardinal.mk_le_aleph0_iff.1 (by
      simpa [Cardinal.mkRat] using Algebra.IsAlgebraic.cardinalMk_le_max ℚ c.F)
    have hk : Countable (kap Z) := countable_of_fg_top ((GlobalTheory.Reg.kap_fg_trdeg E H Dw l Xo c).1 Z)
    have hO : Countable (Om Z) := countable_fractionRing_mvPolynomial _ _
    let _ : Algebra c.F ℂ := σ.toAlgebra
    exact GlobalTheory.nonempty_algHom_complex_of_countable c.F (Om Z)
  · obtain ⟨y', hy⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c (Om Z)
      (CAt σ) φ (genFr h Z)
    obtain ⟨k, x, t, ht⟩ := hU.2.2.1 y'
    exact ⟨k, x, y', t, hy, ht⟩

end GlobalTheory.GenericReading
