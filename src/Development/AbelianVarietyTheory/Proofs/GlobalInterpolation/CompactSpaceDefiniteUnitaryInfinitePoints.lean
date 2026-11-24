module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteUnitaryAutFormEqZeroOfFinitePoints
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompactSpaceMaximalCompactUnitaryInfinite
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

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

noncomputable section

open Formalism.UG

namespace GlobalTheory.InfUCompact

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem compactSpace_UJ (E : Type) [Field E] (n : ℕ) :
    CompactSpace (UJ (starRingEnd (Cinf E)) (1 : Matrix (Fin n) (Fin n) (Cinf E))) := by
  haveI : CompactSpace (Matrix.unitaryGroup (Fin n) (Cinf E)) := GlobalTheory.KinfCompactness.compactSpace_Kinf E n
  let f : Matrix.unitaryGroup (Fin n) (Cinf E) → GL (Fin n) (Cinf E) := fun u =>
    ⟨u.1, star u.1, Matrix.mem_unitaryGroup_iff.1 u.2, Matrix.mem_unitaryGroup_iff'.1 u.2⟩
  have hf : Continuous f :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_star.comp continuous_subtype_val⟩
  have hr : Set.range f =
      (UJ (starRingEnd (Cinf E)) (1 : Matrix (Fin n) (Fin n) (Cinf E)) : Set (GL (Fin n) (Cinf E))) := by
    ext g
    constructor
    · rintro ⟨u, rfl⟩
      change cT (starRingEnd (Cinf E)) u.1 * 1 * u.1 = 1
      rw [mul_one]
      exact Matrix.mem_unitaryGroup_iff'.1 u.2
    · intro hg
      have h : cT (starRingEnd (Cinf E)) (g : Matrix (Fin n) (Fin n) (Cinf E)) * 1 * g = 1 := hg
      rw [mul_one] at h
      exact ⟨⟨g.1, Matrix.mem_unitaryGroup_iff'.2 h⟩, Units.ext rfl⟩
  exact isCompact_iff_compactSpace.1 (hr ▸ isCompact_range hf)

theorem range_infPt : Set.range (GlobalTheory.DefiniteDense.infPt (E := E) (n := n)) = (infU E n : Set (UA E n)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact pFin_infGL _
  · intro hx
    have hp : ∀ a : Ad E, pInf E (conjAd E a) = starRingEnd (Cinf E) (pInf E a) :=
      fun a => (infEq E).symm_apply_apply _
    have hM : GeneralLinearGroup.map (pInf E) x.1 ∈
        UJ (starRingEnd (Cinf E)) (1 : Matrix (Fin n) (Fin n) (Cinf E)) := by
      have h0 : cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * x.1 = 1 := x.2
      rw [mul_one] at h0
      have e : cT (starRingEnd (Cinf E)) ((x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E)) =
          (cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E))).map (pInf E) := by
        ext i j
        simp [Formalism.UG.cT, hp]
      change cT (starRingEnd (Cinf E)) ((x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E)) * 1 *
        (x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E) = 1
      rw [e, mul_one, ← Matrix.map_mul, h0, Matrix.map_one _ (map_zero _) (map_one _)]
    refine ⟨⟨_, hM⟩, Subtype.ext (ga_ext ?_ ?_)⟩
    · exact pInf_infGL _
    · exact (pFin_infGL _).trans (Eq.symm hx)

theorem compactSpace_infU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
    CompactSpace (infU E n) := by
  intro E _ _ _ n
  haveI := compactSpace_UJ E n
  have h : IsCompact (infU E n : Set (UA E n)) :=
    range_infPt (E := E) (n := n) ▸ isCompact_range GlobalTheory.DefiniteDense.continuous_infPt
  exact isCompact_iff_compactSpace.1 h

end GlobalTheory.InfUCompact
