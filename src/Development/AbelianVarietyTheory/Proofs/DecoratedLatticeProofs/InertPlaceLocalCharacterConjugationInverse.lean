module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanRhoTEqTop
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

theorem secW_cA (D : D7) {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (hc : IsConjAt D.sp.cm.sig h c)
    (z : w.adicCompletion D.host.E) : secW hw h (c z) = cA D (secW hw h z) := by
  obtain ⟨y, rfl⟩ := (GlobalTheory.LFun.InertChart.complEquiv hw h).surjective z
  have e1 : c (GlobalTheory.LFun.InertChart.complEquiv hw h y) =
      GlobalTheory.LFun.InertChart.complEquiv hw h (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ D.sp.cm.sig y) := hc y
  rw [e1]
  show GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm _) =
    cA D (GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm _))
  rw [RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
  exact (GlobalTheory.EmbChart.sigR_tensAt v _ y).symm

theorem thW_conj : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (k : w.adicCompletion D.host.E), IsConjAt D.sp.cm.sig h c → (∀ z, c (c z) = z) → ∀ z, thW ψ hw h (k * c k) (c z) * thW ψ hw h (k * c k) z = 1 := by
  intro D ψ v w hw h c k hc hcc z
  have h1 : secW hw h (k * c k * c z) = cA D (secW hw h (k * c k * z)) := by
    rw [← secW_cA D hw h c hc]
    congr 1
    rw [map_mul c, map_mul c, hcc, mul_comm k (c k)]
  rw [thW_apply, thW_apply, h1, ← GlobalTheory.DualPairCheck.trace_cA (_ * cA D _), RingHom.map_mul, GlobalTheory.DualPairCheck.cA_cA,
    GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, RingHom.map_neg, neg_mul, LinearMap.map_neg,
    ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

end GlobalTheory.InertFrameLoc
