module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointsBaseLevelLiftReadAtBaseEmbedding
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodFormsLiftBaseLevelExtensionSpan
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanImageSpan
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupLatticeExtendedDataEqCoordinatewiseImage
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.LiftForms



theorem lift_Mj_base : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        (z'.R.FW j').Mj (z'.F.lv2.lvl false).P (z'.F.lv2.lvl false).ψ⁻¹ (fun g => (idemOf (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.X).coeff g) = Submodule.span (𝓞 (w'.st Z').toD7.what₂.LL) {x' | ∃ x ∈ (z.R.FW j).Mj (z.F.lv2.lvl false).P (z.F.lv2.lvl false).ψ⁻¹ (fun g => (idemOf (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.X).coeff g), ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)}) := by
  intro h1 h2 h3 h4 h5 h6 h7
  have hGoodForms := GlobalTheory.Mem.R3.Rw.goodForms_lift_bc h1 h2 h3 h4 h5 h6 h7
  have hSupLattice := GlobalTheory.Mem.R3.MKExt.mk_ext h1 h2 h3 h4 h5 h6 h7
  refine StepW.trans (StepW.and (StepW.of_all fun _ _ _ _ _ _ _ hp => hp)
    (StepW.and hGoodForms hSupLattice)) (StepW.of_all ?_)
  rintro K B' f' T' w' - - ⟨-, H1, H2⟩ B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' e j j' hj φ hφ
  have hW := H1 B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' e j j' hj φ hφ
  have hK := H2 B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' e j j' hj φ hφ
  have hm : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := congrArg (fun P : Pre => P.R.m) hE.1
  have hn : z.R.nW j = z'.R.nW j' := GlobalTheory.Mem.R3.LiftForms.nat_eq_of_heq hm e.nW j j' hj
  have key := span_rel_inf φ hn _ _ _ _ hK hW
  refine Eq.trans ?_ (key.trans ?_)
  · ext x
    simp only [Arith.FormsL.Mj, Arith.FormsL.Mall, RealDat.WL, Arith.FormsL.Wgood, Submodule.mem_inf,
      Submodule.restrictScalars_mem, and_assoc]
  · congr 1
    ext x'
    simp only [Set.mem_ofPred_eq, Arith.FormsL.Mj, Arith.FormsL.Mall, RealDat.WL, Arith.FormsL.Wgood, Submodule.mem_inf,
      Submodule.restrictScalars_mem, and_assoc]

end GlobalTheory.Mem.R3.LiftForms
