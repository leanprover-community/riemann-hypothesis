module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
public import Formalism.LocalToGlobal.LatticeGeometry.GeoTiedP
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RamifiedRationalPrimesOfTupleBaseTupleEqEmpty
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertAtLeCongN
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTwistOfIsDelta
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyRingHomComplexOfLeContinuum
public import Formalism.LocalToGlobal.HilbertRowConditions.KaTiedIffKapDef
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GeoTiedPGraft
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OverIx
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MapSeqIndAll
public import Formalism.LocalRingCardinality.SpanPowerMembership.DivXExample
public import Formalism.LocalRingCardinality.SpanPowerMembership.UnitsPowSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyFiniteTypeIndexOfRowsPos
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Linter.Style
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRingEquivComplexCompEq
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.GaloisValuations.GlobalB
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.ClsSum

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffZeroEqZeroIff, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QpIsQpSet, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupPinsOfMuIs, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationLtOneOfInvNotMem, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToIntBijective, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupPinsOfMuIsW

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffZeroEqZeroIff =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffZeroEqZeroIff", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase\npublic import Formalism.LocalToGlobal.LatticeGeometry.GeoTiedP\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Geo GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam.PinPlace

theorem mem_mul_iff {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) (y : K) :
    (∃ a : R, y = algebraMap R K (ϖ * a)) ↔ y = 0 ∨ y⁻¹ ∉ (algebraMap R K).range := by
  have hinj := IsFractionRing.injective R K
  constructor
  · rintro ⟨a, rfl⟩
    by_contra hc
    push Not at hc
    obtain ⟨h0, b, hb⟩ := hc
    have h1 : ϖ * a * b = 1 := hinj (by rw [map_mul, hb, mul_inv_cancel₀ h0, map_one])
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one (a * b) (by rw [← mul_assoc, h1]))
  · rintro (rfl | h)
    · exact ⟨0, by simp⟩
    · rcases ValuationRing.isInteger_or_isInteger R y with ⟨b, rfl⟩ | hb
      · have hb : ¬ IsUnit b := by
          rintro ⟨u, rfl⟩
          refine h ⟨(u⁻¹ : Rˣ), ?_⟩
          exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
        have hm : b ∈ IsLocalRing.maximalIdeal R := hb
        rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
        obtain ⟨a, rfl⟩ := hm
        exact ⟨a, rfl⟩
      · exact absurd hb h

variable {D : D7} {p : ℕ} [Fact p.Prime] {la : PlL D p} {jc : DV.KW p →+* ℂ}

theorem mem_range_iff (h : JcPin D p la jc) {y : DV.KW p} {z : D.what₂.LL} (hyz : jc y = D.what₂.embLL z) :
    y ∈ (algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p)).range ↔
      la.1.valuation D.what₂.LL z ≤ 1 := by
  obtain ⟨W, h1, h2⟩ := h
  rw [← h2, hyz, h1]

theorem mem_pW_iff (h : JcPin D p la jc) {y : DV.KW p} {z : D.what₂.LL} (hyz : jc y = D.what₂.embLL z) :
    (∃ a : WittVector p (AlgebraicClosure (ZMod p)),
        y = algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p) (p * a)) ↔
      la.1.valuation D.what₂.LL z < 1 := by
  rw [mem_mul_iff (WittVector.irreducible p) y,
    mem_range_iff h (y := y⁻¹) (z := z⁻¹) (by rw [map_inv₀, map_inv₀, hyz])]
  have h0 : y = 0 ↔ z = 0 := by
    rw [← map_eq_zero_iff jc jc.injective, hyz, map_eq_zero_iff _ D.what₂.embLL.injective]
  rw [h0, map_inv₀, not_le]
  by_cases hz : z = 0
  · simp [hz]
  · have hv : 0 < la.1.valuation D.what₂.LL z := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hz)
    rw [one_lt_inv₀ hv]
    simp [hz]

theorem pinned_reads_place : ∀ (D : D7) (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)),
    (∀ (p : ℕ) [Fact p.Prime] (la : PlL D p), JcPin D p la (jC p la)) →
    ∀ (p : ℕ) [Fact p.Prime] (la : PlL D p) (τ : DV.Emb D p) (e : D.host.E →+* D.what₂.LL),
      (jC p la).comp τ = D.what₂.embLL.comp e → ∀ x : 𝓞 D.host.E,
        τ x ∈ (algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p)).range ∧
        ((∃ a : WittVector p (AlgebraicClosure (ZMod p)),
            τ x = algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p) (p * a)) ↔
          la.1.valuation D.what₂.LL (e x) < 1) ∧
        (la.1.valuation D.what₂.LL (e x) < 1 ↔ RingOfIntegers.mapRingHom e x ∈ la.1.asIdeal) := by
  intro D jC h p _ la τ e hτ x
  have hx : jC p la (τ x) = D.what₂.embLL (e x) := RingHom.congr_fun hτ (x : D.host.E)
  have he : e x = algebraMap (𝓞 D.what₂.LL) D.what₂.LL (RingOfIntegers.mapRingHom e x) := rfl
  refine ⟨(mem_range_iff (h p la) hx).2 ?_, mem_pW_iff (h p la) hx, ?_⟩
  · rw [he]; exact la.1.valuation_le_one _
  · rw [he]; exact la.1.valuation_lt_one_iff_mem _

theorem coeff_zero_eq_zero_iff {k : Type} [Field k] [CharP k p] [PerfectRing k p] (b : WittVector p k) :
    b.coeff 0 = 0 ↔ ∃ a : WittVector p k, b = p * a := by
  constructor
  · intro h0
    have hb : ¬ IsUnit b := by
      rintro ⟨u, rfl⟩
      have h1 := congrArg (fun w : WittVector p k => w.coeff 0) u.mul_inv
      simp only [WittVector.mul_coeff_zero, WittVector.one_coeff_zero] at h1
      rw [h0, zero_mul] at h1
      exact zero_ne_one h1
    have hm : b ∈ IsLocalRing.maximalIdeal (WittVector p k) := hb
    rw [(WittVector.irreducible p).maximalIdeal_eq, Ideal.mem_span_singleton] at hm
    obtain ⟨a, rfl⟩ := hm
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    rw [WittVector.mul_coeff_zero]
    have : ((p : WittVector p k)).coeff 0 = 0 := by simp
    rw [this, zero_mul]

theorem pinned_tiedFor : ∀ (D : D7) (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)),
    (∀ (p : ℕ) [Fact p.Prime] (la : PlL D p), JcPin D p la (jC p la)) → Formalism.L2.Geo.ComplexEmbeddingsCompatible jC := by
  intro D jC h p _ la τ e hτ x
  obtain ⟨-, h2, -⟩ := pinned_reads_place D jC h p la τ e hτ x
  rw [← h2]
  constructor
  · rintro ⟨b, hb, h0⟩
    obtain ⟨a, rfl⟩ := (coeff_zero_eq_zero_iff b).1 h0
    exact ⟨a, hb.symm⟩
  · rintro ⟨a, ha⟩
    exact ⟨p * a, ha.symm, (coeff_zero_eq_zero_iff _).2 ⟨a, rfl⟩⟩

end GlobalTheory.ShFam.PinPlace
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffZeroEqZeroIff =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QpIsQpSet =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QpIsQpSet", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RamifiedRationalPrimesOfTupleBaseTupleEqEmpty\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertAtLeCongN\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl.QpIsOf

theorem qpIs_qpSet : ∀ {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), ColPin w → ∀ (Z : w.Lt) {nch : NChoice (w.D Z)}
    (tp : TupTied (w.D Z) (TC.cf w.I w.l Z) nch), tp.xi = w.I.xi → GlobalTheory.Mem.HD.TupPins tp →
    TC.QpIs w.I (GlobalTheory.Mem.HD.ReQ.qpSet tp) := by
  intro B f T w _ Z nch tp hxi _ a p
  classical
  have hr := w.ok.xi_reads a
  have hsel : Formalism.L2.Col.IsSel B.fields w.I.sel := w.ok.sel_ok
  have hf := GlobalTheory.OpenChrRam.qprime_finite B.fields.F B.fields.E B.fields.K ((w.I.tup a : Formalism.L2.DIV.Chr _ _ _))
    (w.I.tup a).2.1.1.1.1.2
  have hpm : ∀ (v : HeightOneSpectrum (𝓞 B.fields.F)) (P : HeightOneSpectrum (𝓞 B.fields.E)),
      Ideal.under (𝓞 B.fields.F) P.asIdeal = v.asIdeal → ((p : 𝓞 B.fields.E) ∈ P.asIdeal ↔ (p : 𝓞 B.fields.F) ∈ v.asIdeal) := by
    intro v P h
    rw [← h, Ideal.under, Ideal.mem_comap, map_natCast]
  have hx : ∀ P, (tp.xi a).UnrAt P ↔ (w.I.xi a).UnrAt P := fun P => by rw [congrFun hxi a]; exact Iff.rfl
  refine (GlobalTheory.Mem.HD.ReQ.mem_qpSet tp a p).trans ?_
  refine Iff.trans (and_congr_right fun _ => exists_congr fun P => and_congr_right fun _ => not_congr (hx P)) ?_
  show (p.Prime ∧ ∃ P, (p : 𝓞 B.fields.E) ∈ P.asIdeal ∧ ¬ (w.I.xi a).UnrAt P) ↔
    p.Prime ∧ ∃ P ∈ Formalism.L2.Col.QE w.I.sel (w.I.tup a : Formalism.L2.DIV.Chr _ _ _), (p : 𝓞 B.fields.E) ∈ P.asIdeal
  rw [Formalism.L2.Col.QE, dite_eq_left hf]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨P, hp, hP⟩
    refine ⟨w.I.sel (P.under (𝓞 B.fields.F)),
      Finset.mem_image_of_mem _ (hf.mem_toFinset.2 ((GlobalTheory.Mem.ReadTwist.mem_qprime_iff hr _).2 ⟨P, rfl, hP⟩)), ?_⟩
    rw [hpm _ _ (hsel _), ← hpm _ P rfl]
    exact hp
  · rintro ⟨P, hP, hp⟩
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP
    obtain ⟨P', hP', hr'⟩ := (GlobalTheory.Mem.ReadTwist.mem_qprime_iff hr v).1 (hf.mem_toFinset.1 hv)
    refine ⟨P', ?_, hr'⟩
    rw [hpm v P' (by rw [← hP']; rfl), ← hpm v _ (hsel v)]
    exact hp

end GlobalTheory.Mem.Top.Bl.QpIsOf
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QpIsQpSet =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupPinsOfMuIs =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupPinsOfMuIs", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTwistOfIsDelta\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer\nimport Formalism.LocalToGlobal.UnitaryNorms.CharUniq\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.HD.TupPin

theorem isTwist_types (B : Base) (f : Fr B.toPre) (T : TwDat B) :
    ∀ ξ ∈ T.set f, Chr.IsTwist B.host (Set.range B.host.g) ξ := by
  have a1 : Chr.IsTwist B.host (Set.range B.host.g) f.del := Chr.isTwist_of_isDelta B.host.pde_prime
    (GlobalTheory.HostSplit.split_of_one_mod B.R B.host _ B.host.pde_prime B.pde_cond.1).1
    (fun ⟨i, h⟩ => (B.host.pde_ne_g i).1 h.symm) f.isDel
  have a2 : Chr.IsTwist B.host (Set.range B.host.g) f.del' := Chr.isTwist_of_isDelta B.host.pde'_prime
    (GlobalTheory.HostSplit.split_of_one_mod B.R B.host _ B.host.pde'_prime B.pde_cond.2).1
    (fun ⟨i, h⟩ => (B.host.pde_ne_g i).2 h.symm) f.isDel'
  rintro ξ ((rfl | rfl | rfl) | ⟨w, rfl⟩)
  · exact Chr.isTwist_one _ _
  · exact a1
  · exact a2
  · have h := T.psi_tw w
    have a3 : Chr.IsTwist B.host (Set.range B.host.g) (T.psi w) := ⟨h.1, h.2.1, h.2.2.1, fun v hv =>
      ⟨(h.2.2.2 v hv).1, (h.2.2.2 v hv).2.1, (h.2.2.2 v hv).2.2.1,
        fun ⟨i, hi⟩ => (h.2.2.2 v hv).2.2.2 (Or.inr (Or.inl ⟨i, hi.symm⟩))⟩⟩
    unfold TwDat.xiTw
    split_ifs
    exacts [a2.mul_twist a3, a1.mul_twist a3]

theorem xiTw_unr (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : B.places.Pl) (v : HeightOneSpectrum (𝓞 B.host.E))
    (hv : OverP B.host (B.places.resChar w) v) : (T.xiTw f w).UnrAt v := by
  have hψ : (T.psi w).UnrAt v := fun x _ => (T.psi_is w).atl v hv x
  unfold TwDat.xiTw
  split_ifs with h
  · refine (f.isDel'.unr v fun hn => B.host.pde_ne ?_).mul hψ
    rw [h] at hv
    exact Examples₂.PlacesToy.prime_mem_unique v B.host.pde_prime B.host.pde'_prime hv hn
  · exact (f.isDel.unr v fun hn => h
      (Examples₂.PlacesToy.prime_mem_unique v (B.places.resChar_prime w) B.host.pde_prime hv hn)).mul hψ

end GlobalTheory.Mem.HD.TupPin
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupPinsOfMuIs =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationLtOneOfInvNotMem =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationLtOneOfInvNotMem", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyRingHomComplexOfLeContinuum\nimport Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring\nimport Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRingEquivComplexCompEq\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Rat\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Algebraic.Cardinality\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport ReciprocityTheory.GaloisValuations.GlobalB\nimport Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open Pointwise

namespace GlobalTheory.WittFracPlace

theorem valuation_intCast_lt_one_iff {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) {p : ℕ} (hp : p.Prime)
    (h : A.valuation (p : Ω) < 1) (n : ℤ) : A.valuation (n : Ω) < 1 ↔ (p : ℤ) ∣ n := by
  have hle : ∀ m : ℤ, A.valuation (m : Ω) ≤ 1 := fun m => (A.valuation_le_one_iff _).2 (intCast_mem A m)
  have hmul : ∀ (m : ℤ) (x : Ω), A.valuation x < 1 → A.valuation (m * x) < 1 := fun m x hx => by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle m)) hx
  constructor
  · intro hn
    by_contra hd
    obtain ⟨a, b, hab⟩ := ((Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd).2 hd
    have e : (a : Ω) * p + b * n = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
    have := Valuation.map_add_lt _ (hmul a _ h) (hmul b _ hn)
    rw [e, map_one] at this
    exact lt_irrefl _ this
  · rintro ⟨m, rfl⟩
    rw [Int.cast_mul, mul_comm, Int.cast_natCast]
    exact hmul m _ h

theorem exists_smul_eq {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {p : ℕ} (hp : p.Prime)
    (A A' : ValuationSubring Ω) (h : A.valuation (p : Ω) < 1) (h' : A'.valuation (p : Ω) < 1) :
    ∃ g : Ω ≃ₐ[ℚ] Ω, g • A = A' := by
  have hpr : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)
  let v : HeightOneSpectrum (𝓞 ℚ) :=
    ⟨(Ideal.span {(p : ℤ)}).comap Rat.ringOfIntegersEquiv.toRingHom, Ideal.comap_isPrime _ _, fun hb => by
      have h1 : (p : 𝓞 ℚ) ∈ (Ideal.span {(p : ℤ)}).comap Rat.ringOfIntegersEquiv.toRingHom := by
        rw [Ideal.mem_comap, map_natCast]; exact Ideal.subset_span rfl
      rw [hb, Ideal.mem_bot] at h1
      exact hp.ne_zero (by exact_mod_cast h1)⟩
  have key : ∀ B : ValuationSubring Ω, B.valuation (p : Ω) < 1 →
      ∀ x : 𝓞 ℚ, B.valuation (algebraMap ℚ Ω (x : ℚ)) < 1 ↔ x ∈ v.asIdeal := by
    intro B hB x
    obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective x
    have e : Rat.ringOfIntegersEquiv.symm n = (n : 𝓞 ℚ) := eq_intCast Rat.ringOfIntegersEquiv.symm.toRingHom n
    have e2 : algebraMap ℚ Ω ((n : 𝓞 ℚ) : ℚ) = (n : Ω) :=
      map_intCast ((algebraMap ℚ Ω).comp (algebraMap (𝓞 ℚ) ℚ)) n
    rw [e, e2, valuation_intCast_lt_one_iff B hp hB]
    change _ ↔ (n : 𝓞 ℚ) ∈ Ideal.comap _ _
    rw [Ideal.mem_comap, map_intCast, Int.cast_id, Ideal.mem_span_singleton]
  exact ReciprocityTheory.Gal.exists_smul_eq_of_over (key A h) (key A' h')

theorem valuation_lt_one_of_inv_notMem {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) {x : Ω} (h : x⁻¹ ∉ A) :
    A.valuation x < 1 := by
  rw [← A.valuation_le_one_iff, map_inv₀, not_le] at h
  have h0 : A.valuation x ≠ 0 := fun e => by simp [e] at h
  exact (one_lt_inv₀ (zero_lt_iff.2 h0)).1 h

theorem exists_emb_inducing (L : Type) [Field L] [NumberField L] {p : ℕ} (hp : p.Prime)
    (v : HeightOneSpectrum (𝓞 L)) (hv : (p : 𝓞 L) ∈ v.asIdeal) (V : ValuationSubring ℂ) (hV : (p : ℂ)⁻¹ ∉ V) :
    ∃ e : L →+* ℂ, ∀ x, e x ∈ V ↔ v.valuation L x ≤ 1 := by
  let Ω := AlgebraicClosure L
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ L Ω
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  let ι : Ω →ₐ[ℚ] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  obtain ⟨A', hA'⟩ := GlobalTheory.exists_valuationSubring_comap_eq (v.valuation L).valuationSubring (algebraMap L Ω)
  have hm : ∀ x : L, algebraMap L Ω x ∈ A' ↔ v.valuation L x ≤ 1 := fun x => by
    rw [← ValuationSubring.mem_comap, hA', Valuation.mem_valuationSubring_iff]
  have h1 : (V.comap ι.toRingHom).valuation (p : Ω) < 1 := valuation_lt_one_of_inv_notMem _ (by
    rwa [ValuationSubring.mem_comap, map_inv₀, map_natCast])
  have h2 : A'.valuation (p : Ω) < 1 := valuation_lt_one_of_inv_notMem _ (by
    have h3 : v.valuation L (p : L) < 1 := by
      have := (v.valuation_lt_one_iff_mem (K := L) (p : 𝓞 L)).2 hv
      rw [← map_natCast (algebraMap (𝓞 L) L) p]
      exact this
    have h4 : v.valuation L (p : L) ≠ 0 := by simpa using hp.ne_zero
    rw [← map_natCast (algebraMap L Ω), ← map_inv₀, hm, map_inv₀, not_le]
    exact (one_lt_inv₀ (zero_lt_iff.2 h4)).2 h3)
  obtain ⟨g, hg⟩ := exists_smul_eq hp _ _ h1 h2
  refine ⟨(ι.toRingHom.comp g.symm.toRingEquiv.toRingHom).comp (algebraMap L Ω), fun x => ?_⟩
  rw [← hm, ← hg, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem exists_jcPin : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (la : PlL D p), ∃ jc : DV.KW p →+* ℂ, JcPin D p la jc := by
  intro D p hp la
  obtain ⟨j⟩ := GlobalTheory.WittFracComplex.nonempty_ringHom_complex p
  obtain ⟨V, -, -, -, hV⟩ :=
    GlobalTheory.exists_valuationSubring_dominating (V := WittVector p (AlgebraicClosure (ZMod p))) j
  have hp' : (p : ℂ)⁻¹ ∉ V := by
    rw [← map_natCast j, ← map_inv₀, hV]
    rintro ⟨a, ha⟩
    have hinj := IsFractionRing.injective (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p)
    have h0 : (p : DV.KW p) ≠ 0 := fun e => hp.out.ne_zero (by
      have := congrArg j e
      rw [map_natCast, map_zero] at this
      exact_mod_cast this)
    refine (WittVector.irreducible p (k := AlgebraicClosure (ZMod p))).not_isUnit
      (isUnit_iff_exists_inv.2 ⟨a, hinj ?_⟩)
    rw [map_mul, ha, map_natCast, map_one, mul_inv_cancel₀ h0]
  obtain ⟨e, he⟩ := exists_emb_inducing D.what₂.LL hp.out la.1 la.2 V hp'
  have : Countable D.what₂.LL := Cardinal.mk_le_aleph0_iff.1
    ((Algebra.IsAlgebraic.cardinalMk_le_max ℚ D.what₂.LL).trans (by simp))
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq D.what₂.LL e D.what₂.embLL
  refine ⟨τ.toRingHom.comp j, V.comap τ.symm.toRingHom, fun x => ?_, fun a => ?_⟩
  · rw [← he, ← hτ, ValuationSubring.mem_comap]
    simp
  · rw [← hV, ValuationSubring.mem_comap]
    simp

end GlobalTheory.WittFracPlace
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationLtOneOfInvNotMem =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToIntBijective =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToIntBijective", "h": "module\n\npublic import Formalism.LocalToGlobal.HilbertRowConditions.KaTiedIffKapDef\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GeoTiedPGraft\nimport Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.ClsSum\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.L2.Host Formalism.L2.Rows Formalism.L2.Geo GlobalTheory.GeoGraft NumberField

namespace GlobalTheory.GeoModel

variable (D : D7)

def fracO : IntermediateField ℚ D.what₂.LL := IntermediateField.adjoin ℚ (Set.range D.what₂.OtoLL)

theorem otoLL_mem (y : D.what₂.O) : D.what₂.OtoLL y ∈ fracO D :=
  IntermediateField.subset_adjoin ℚ _ ⟨y, rfl⟩

variable {D} {T : HostTied D} {C : CharFrame D}

def toInt (h : OTied D T C) : D.what₂.O →+* 𝓞 (fracO D) where
  toFun y := ⟨⟨D.what₂.OtoLL y, otoLL_mem D y⟩, by
    have hq : IsIntegral ℤ (T.jLL (D.what₂.OtoLL y)) := ((h.range _).1 ⟨y, rfl⟩).2
    let f : (fracO D) →ₐ[ℤ] Qb := (T.jLL.comp (fracO D).val.toRingHom).toIntAlgHom
    have hf : Function.Injective f := (T.jLL.comp (fracO D).val.toRingHom).injective
    exact (isIntegral_algHom_iff f hf).1 hq⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; exact map_mul D.what₂.OtoLL a b
  map_zero' := by ext; simp
  map_add' a b := by ext; exact map_add D.what₂.OtoLL a b

theorem toInt_val (h : OTied D T C) (y : D.what₂.O) : ((toInt h y : fracO D) : D.what₂.LL) = D.what₂.OtoLL y := rfl

theorem toInt_bijective (h : OTied D T C) : Function.Bijective (toInt h) := by
  refine ⟨fun a b hab => h.inj ?_, fun z => ?_⟩
  · have := congrArg (fun w : 𝓞 (fracO D) => ((w : fracO D) : D.what₂.LL)) hab
    simpa [toInt_val] using this
  · set x : D.what₂.LL := ((z : fracO D) : D.what₂.LL) with hx
    have hint : IsIntegral ℤ (T.jLL x) := by
      let f : (fracO D) →ₐ[ℤ] Qb := (T.jLL.comp (fracO D).val.toRingHom).toIntAlgHom
      have hf : Function.Injective f := (T.jLL.comp (fracO D).val.toRingHom).injective
      exact (isIntegral_algHom_iff f hf).2 z.2
    have hmem : T.jLL x ∈ KsQ D T C h.pieces := by
      have hx' : x ∈ fracO D := (z : fracO D).2
      have h1 : T.jLL x ∈ (fracO D).map T.jLL.toRatAlgHom := ⟨x, hx', rfl⟩
      rw [fracO, IntermediateField.adjoin_map] at h1
      refine (IntermediateField.adjoin_le_iff.2 ?_) h1
      rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ((h.range _).1 ⟨y, rfl⟩).1
    obtain ⟨y, hy⟩ := (h.range _).2 ⟨hmem, hint⟩
    refine ⟨y, ?_⟩
    ext
    exact T.jLL.injective hy

def eO (h : OTied D T C) : 𝓞 (fracO D) ≃+* D.what₂.O := (RingEquiv.ofBijective _ (toInt_bijective h)).symm

end GlobalTheory.GeoModel
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToIntBijective =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupPinsOfMuIsW =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupPinsOfMuIsW", "h": "module\n\npublic import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OverIx\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RamifiedRationalPrimesOfTupleBaseTupleEqEmpty\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MapSeqIndAll\npublic import Formalism.LocalRingCardinality.SpanPowerMembership.DivXExample\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GeoTiedPGraft\npublic import Formalism.LocalRingCardinality.SpanPowerMembership.UnitsPowSurjective\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyFiniteTypeIndexOfRowsPos\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffZeroEqZeroIff\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QpIsQpSet\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupPinsOfMuIs\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationLtOneOfInvNotMem\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToIntBijective\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.Top.DivRec

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {X0 : BaseLevelRowSide D} {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}

theorem nonempty_ix (hH : Holds R F) : Nonempty A3.fam3.base3.Ix :=
  GlobalTheory.Div.nonempty_ix_of_pos A3 F.P0 F.ψ0 (R.toCx3 F).zs hH.ok hH.prim.block (hH.prim.pos false)


open Classical in
def labOf (Z : ReadL R F X0 Y) (hH : Holds R F) (σ : D.what₂.FT) : A3.fam3.base3.Ix :=
  if h : ∃ c, Bl.OverIx Z σ c then h.choose else (nonempty_ix hH).some

theorem overIx_labOf (Z : ReadL R F X0 Y) (hH : Holds R F) (σ : D.what₂.FT) (h : ∃ c, Bl.OverIx Z σ c) :
    Bl.OverIx Z σ (labOf Z hH σ) := by
  rw [labOf, dite_eq_left h]
  exact h.choose_spec


open Classical in
def logLamOf (Z : ReadL R F X0 Y) (hH : Holds R F) (j : ℕ) (σ : D.what₂.FT) (e : D.what₂.LL →+* ℂ) : ℝ :=
  if e = D.what₂.embLL then Real.log (D.what₂.lamP D.what₂.mu0 j σ)
  else if h : j - 1 < D.R.m then
    if D.what₂.isot j σ = ⊥ then 0 else Real.log ((s0Of R F).lam ⟨j - 1, h⟩ A3.A.μ0 (labOf Z hH σ) (InfinitePlace.mk e))
  else 0

theorem lamAre_of_eq (Z : ReadL R F X0 Y) (hH : Holds R F) (Xd : DivX D) (hX : Xd.logLam = logLamOf Z hH) : Bl.LamAre Z Xd := by
  refine ⟨labOf Z hH, overIx_labOf Z hH, fun i σ e he => ?_⟩
  have h : (i : ℕ) + 1 - 1 < D.R.m := i.2
  rw [hX, logLamOf, if_neg he, dite_eq_left h]
  exact ⟨fun h0 => if_neg h0, fun h0 => if_pos h0⟩

def x0 (Z : ReadL R F X0 Y) (hP : Pins R F cG) (hH : Holds R F) : DivX D where
  geo := Formalism.BasicNotions.Examples₂.geoExample _
  Lev := Empty
  levPr := fun κ => κ.elim
  shv := fun _ κ => κ.elim
  shv_N := fun _ κ => κ.elim
  shv_lev := fun _ κ => κ.elim
  PlP := fun p _ => Formalism.L2.Geo.PlL D p
  plpFin := fun p _ => Formalism.L2.Geo.finPl D p
  plpNe := fun p _ => Formalism.L2.Geo.plL_ne D p
  wtP := fun p _ => Formalism.L2.Geo.wtL D p
  divisorWeight_nonneg := fun p _ => Formalism.L2.Geo.wtL_nonneg D p
  divisorWeight_sum := fun p _ => Formalism.L2.Geo.wtL_sum D p
  plP := fun p _ => Formalism.BasicNotions.Examples₂.PlOver.plLEquiv D p
  divisorWeight_def := fun p _ la => Formalism.BasicNotions.Examples₂.PlOver.wtLog_eq D p la
  jC := fun p _ _ => (Formalism.BasicNotions.Examples₂.teich_Om_equiv p).some.toRingHom.comp (algebraMap (DV.KW p) (Formalism.BasicNotions.Examples₂.TeichOm p))
  Mp := fun _ κ => κ.elim
  md := fun _ κ => κ.elim
  vdd := fun _ _ => 0
  vdd_unram := fun _ _ _ => rfl
  phiFr_unram := fun _ κ => κ.elim
  vdd_nonneg := fun _ _ => le_rfl
  CurveM := fun _ κ => κ.elim
  degM := fun _ κ => κ.elim
  htMdl := fun _ κ => κ.elim
  htCurve := fun _ κ => κ.elim
  htCurve_deg := fun _ κ => κ.elim
  MjH := mjH Z
  MjH_good := mjH_good Z hH
  jM := jM Z
  jM_basis := jM_basis Z hH
  jM_lat := jM_lat Z hP hH
  MjLat_sub := mjLat_sub Z hP hH
  jM_metric := jM_metric Z hH
  Qp := fun _ => ∅
  degreeZero_partial_set_empty := rfl
  Qp_muAt := fun _ => Finset.notMem_empty _
  Qp_g := fun _ _ _ => Finset.notMem_empty _
  QPl := fun _ => Empty
  qv := fun _ v => v.elim
  qv_gt := fun _ v => v.elim
  qv_char := fun _ _ v => v.elim
  nu := fun _ v => v.elim
  nu_ne := fun _ v => v.elim
  nu_abs := fun _ v => v.elim
  ZQ := fun _ v => v.elim
  quotientLocalValueFirst := fun _ v => v.elim
  typeDim := fun _ v => v.elim
  Comp := fun _ => Empty
  degHH := fun _ c => c.elim
  Yv := fun _ c => c.elim
  Ybd := fun _ c => c.elim
  Lw := fun _ c => c.elim
  iMj := fun _ c => c.elim
  iMj_mem := fun _ c => c.elim
  logLam := logLamOf Z hH
  logLam_base := fun _ _ => if_pos rfl
  kapR := fun _ => kapSharp D
  kapR_pos := fun _ => RowSide.kapOf_pos _ _
  kapR_conj := fun _ => rfl
  Surf := Empty
  surfCh2 := fun _ => 0
  surfDegOm := fun _ => 0
  SurfFp := Empty
  surfFpCh2 := fun _ => 0

end GlobalTheory.Mem.Top.DivRec

end

noncomputable section

namespace GlobalTheory.Mem.Top.DivRec

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
  NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem tupPins_of_muIsW (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (Wt : Set X.B.places.Pl)
    (xi : X.C.Tup → HChar X.B.host.E) (h : V4.MuIsW X f T Wt xi) {C : CharFrame X.toD7} {nch : NChoice X.toD7}
    (tp : TupTied X.toD7 C nch) (hxi : tp.xi = xi) : GlobalTheory.Mem.HD.TupPins tp := by
  refine ⟨fun μ v hv => ?_, fun w v hv => ?_⟩
  · rw [hxi] at hv
    obtain ⟨h1, h2, h3, h4⟩ :=
      (GlobalTheory.Mem.HD.TupPin.isTwist_types X.B f T (xi μ) (h.range ▸ Set.mem_range_self μ)).2.2.2 v hv
    exact ⟨h1, h2, h3, fun k hk => h4
      ⟨k, Examples₂.PlacesToy.prime_mem_unique v (X.B.host.g_prime k) h2 hk (Ideal.absNorm_mem _)⟩⟩
  · rw [hxi]
    show (xi (X.W.muAt w)).UnrAt v
    by_cases hw : w ∈ Wt
    · rw [h.on w hw, h.tw w]
      exact GlobalTheory.Mem.HD.TupPin.xiTw_unr X.B f T w v hv
    · rw [h.off w hw, h.mu0]
      exact fun _ _ => rfl


open Formalism.L2.Rows Formalism.L2.Geo GlobalTheory.GeoGraft GlobalTheory.GeoModel in
theorem geoOver_stages (X : Stages) (X₀ : DivX X.toD7) : GeoOver (fun _ => True) X₀ := by
  let D := X.toD7
  let eO : 𝓞 X.B.Ks ≃+* D.what₂.O := RingEquiv.refl _
  let kL : X.B.Ks →+* D.what₂.LL := X.B.Ks.val.toRingHom
  have hk : ∀ x : 𝓞 X.B.Ks, kL (x : X.B.Ks) = D.what₂.OtoLL (eO x) := fun _ => rfl
  let jc : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ) :=
    fun p _ la => Classical.choose (GlobalTheory.WittFracPlace.exists_jcPin D p la)
  have hjc : ComplexEmbeddingsCompatible jc := GlobalTheory.ShFam.PinPlace.pinned_tiedFor D jc
    (fun p _ la => Classical.choose_spec (GlobalTheory.WittFracPlace.exists_jcPin D p la))
  refine ⟨divXFl D jc X₀, fun _ _ => True, ⟨divXFl D jc X₀, (divXFl D jc X₀).iMj, (divXFl D jc X₀).iMj_mem, rfl⟩,
    ⟨famFlJ D jc X.B.Ks eO kL hk, fun p _ => Equiv.refl _, fun _ _ _ => Equiv.refl _, tiedX_fl D jc X₀, hjc,
      fun _ _ _ _ _ => trivial, isoInv_famFlJ D jc X.B.Ks eO kL hk, levInTie_famFlJ D jc X.B.Ks eO kL hk⟩, trivial⟩

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}

theorem exists_divT {𝒮 : Slots} {K : Ctx} (w : ColW B f T) (pin : ColPin w) (Z : w.Lt) (l : Lv4 𝒮 K w Z) :
    ∃ Y : DivX (w.D Z), Nonempty (DivT l.n Y) ∧ MjAre l.what₂.r.Z Y ∧ (∀ σ, Y.kapR σ = kapSharp (w.D Z)) ∧
      LamAre l.what₂.r.Z Y := by
  have hp : GlobalTheory.Mem.HD.TupPins l.n.tp := tupPins_of_muIsW (w.st Z) f T l.Wt w.I.xi l.what₂.mu l.n.tp l.n.xi
  let X₁ := x0 l.what₂.r.Z l.what₂.r.z.pins l.what₂.r.intersectionNumber_baseChange
  let X₂ := GlobalTheory.Mem.HD.ReQ.reQ l.n.tp hp w.I.sel pin.above X₁
  obtain ⟨X, inK, ⟨Xg, iM, hiM, rfl⟩, hG, -⟩ := geoOver_stages (w.st Z) X₂
  let c := GlobalTheory.Mem.HD.ReQ.reducedDivisorCharacter l.n.tp hp w.I.sel pin.above X₁
  obtain ⟨h1, h2⟩ := GlobalTheory.Mem.HD.ReQ.reLoc l.n.tp hp w.I.sel pin.above X₁
  let chr : DivisorCharacterCompatibility (w.D Z) (TC.cf w.I w.l Z) _ l.n.tp (GlobalTheory.GeoGraft.graft Xg X₂ iM hiM) := ⟨c.Qp_iff, c.eQPl, c.qv_eq⟩
  refine ⟨GlobalTheory.GeoGraft.graft Xg X₂ iM hiM,
    ⟨{ Qp := _root_.GlobalTheory.Mem.Top.Bl.QpIsOf.qpIs_qpSet w pin Z l.n.tp l.n.xi hp, chr := chr, loc := ⟨h1, ?_⟩, inK := inK, geo := hG }⟩,
    GlobalTheory.Mem.R3.exists_mjHTie l.what₂.r.Z _ rfl HEq.rfl, fun _ => rfl,
    lamAre_of_eq l.what₂.r.Z l.what₂.r.intersectionNumber_baseChange _ rfl⟩
  exact ⟨h2.qv_eq, h2.deg1, h2.ram, h2.off_g, h2.nu_eq, h2.typeDim_eq, h2.ZQ_eq, h2.quotientLocalValueFirst_eq⟩

theorem lamAre_heq {K : Ctx} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 p0' : BaseLevelRowSide (w.D Z)} {t : RowsT K w Z Wt p0}
    {t' : RowsT K w Z Wt p0'} (e : p0 = p0') (h : HEq t t') {X : DivX (w.D Z)} (hX : LamAre t'.r.Z X) : LamAre t.r.Z X := by
  subst e
  obtain rfl := eq_of_heq h
  exact hX

theorem divEx_prov (𝒮 : Slots) (hOx : 𝒮.Ox = OX) : DivEx 𝒮 :=
  StepW.of_all fun _ _ _ _ w _ _ hpin Z l =>
    let ⟨Y, h1, h2, h3, h4⟩ := exists_divT w hpin.some Z l
    ⟨Y, h1, h2, h3, fun O t hX hp ht => by
      rw [hOx]
      exact ⟨⟨lamAre_heq hp ht (hX ▸ h4)⟩⟩⟩

theorem divEx_of_ox : GlobalTheory.NT.RayField → GlobalTheory.Published.PrincipalIdealSt → GlobalTheory.Published.CMCurveGoodOutsidePrimeSt → ∀ 𝒮 : Slots,
    𝒮.Ox = OX → DivEx 𝒮 :=
  fun _ _ _ 𝒮 hOx => divEx_prov 𝒮 hOx

end GlobalTheory.Mem.Top.DivRec

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupPinsOfMuIsW =====
