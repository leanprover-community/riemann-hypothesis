module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LanglandsQuotientSTy
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ExtraV
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AbsCentral

@[expose] public section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Win.T2
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {rc : IrrGL (k := w.adicCompletion E) → WD h}
private theorem segmentV {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}
    (H : _root_.UpperTheory.V.Z.Win.LawsV a ha ε rc)
    {Δ : Segment (w.adicCompletion E)} {x : IrrGL (k := w.adicCompletion E)}
    (hx : IsLSeg Δ x.rep) :
    rc x = ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len) :=
  (H.langlands [Δ] x hx.isL).trans (WD.lpSum_zero _)
end UpperTheory.V.Z.Win.T2
theorem UpperTheory.V.Z.Win.T2.lQuot_alt :
    _root_.GlobalTheory.LocLanglands.IsRec.langlandsQuotient_s_ty := by
  intro E Ω i₁ i₂ i₃ i₄ i₅ A w h rc hrc 𝔪 s N δ hδ hd π hπ
  have h1 : IsL 𝔪 (GlobalTheory.LocLanglands.cls π).rep := IsL.of_equiv ⟨s, δ, hd, hδ, hπ⟩ (equivRep π)
  obtain ⟨Δ, ⟨hm, -⟩, hΔ⟩ := hδ
  obtain ⟨a, ha, ε, H⟩ := _root_.UpperTheory.V.Z.Win.toV' hrc
  simp only [fun i => UpperTheory.V.Z.Win.T2.segmentV H (hΔ i)]
  rw [H.langlands (List.ofFn Δ) (GlobalTheory.LocLanglands.cls π) (by rwa [← Fin.univ_val_map, hm]), List.map_ofFn]
  rfl
end
end
