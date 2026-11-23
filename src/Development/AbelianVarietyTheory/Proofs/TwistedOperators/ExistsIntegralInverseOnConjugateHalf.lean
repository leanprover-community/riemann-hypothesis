module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThPDatumEq
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

namespace GlobalTheory.HalfUnit

theorem cc_star (D : D7) (x : D.host.E) : cc (star x) = x := by
  first
  | exact star_star x
  | rfl
  | simp [cc]

theorem mem_conjI_of (D : D7) (P : Ideal (𝓞 D.host.E)) (s : 𝓞 D.host.E)
    (h : Formalism.L2.Col.cO D.host.E s ∈ P) : s ∈ conjI P :=
  Ideal.subset_span ⟨_, h, (cc_star D (s : D.host.E)).symm⟩

theorem exists_int_inv_half : ∀ (D : D7) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
    ∀ s : 𝓞 D.host.E, (∀ PP ∈ P, s ∉ conjI PP.asIdeal) →
    ∃ t : AE D, finPart D t ∈ intAE D ∧ t * incA D (s : D.host.E) * cA D e = cA D e := by
  intro D P e he s hs
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  by_cases hP : P = ∅
  · subst hP
    refine ⟨0, by rw [map_zero]; exact zero_mem _, ?_⟩
    simp
  obtain ⟨tableDegreeThreeBase, hPP0⟩ := Finset.nonempty_iff_ne_empty.2 hP
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hs tableDegreeThreeBase hPP0 (zero_mem _)
  have hsE : (s : D.host.E) ≠ 0 := by
    intro h; apply hs0; exact RingOfIntegers.ext (by simpa using h)
  refine ⟨cA D (∑ PP ∈ P, es PP) * incA D ((s : D.host.E)⁻¹), ?_, ?_⟩

  · rw [map_sum, Finset.sum_mul, map_sum]
    refine sum_mem fun PP hPP => ?_
    have hc0 : Formalism.L2.Col.cO D.host.E s ≠ 0 := by
      intro h0; apply hs0
      rw [← Formalism.L2.Col.cO_cO s, h0, map_zero]
    have hnot : Formalism.L2.Col.cO D.host.E s ∉ PP.asIdeal := fun hm => hs PP hPP (mem_conjI_of D _ s hm)
    have hint := not_not.1 (mt ((hes PP hPP).2 _ hc0).2 hnot)
    have := GlobalTheory.MovedIdem.finPart_conj_mem hint
    have hst : star (((Formalism.L2.Col.cO D.host.E s : 𝓞 D.host.E) : D.host.E)⁻¹) = (s : D.host.E)⁻¹ := by
      rw [star_inv₀]
      congr 1
      exact star_star (s : D.host.E)
    rwa [hst] at this
  · have h1 : incA D ((s : D.host.E)⁻¹) * incA D (s : D.host.E) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hsE, map_one]
    calc cA D (∑ PP ∈ P, es PP) * incA D ((s : D.host.E)⁻¹) * incA D (s : D.host.E) * cA D (∑ PP ∈ P, es PP)
        = cA D ((∑ PP ∈ P, es PP) * (∑ PP ∈ P, es PP)) := by
          rw [mul_assoc (cA D _), h1, mul_one, map_mul]
      _ = cA D (∑ PP ∈ P, es PP) := by rw [hee]

end GlobalTheory.HalfUnit
