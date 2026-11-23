module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtensionWithOrigin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteLevelAndSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupTiedOfMuIsW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsSymm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPlaceIndexMemFirstPairOfCompatibleChoice
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



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
open GlobalTheory.Mem.Top.TwChar (plUnder RootIso FrobPick avoidPlaces subset_avoidPlaces)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
theorem sFino_of_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {cDep : ℝ} (h : _root_.GlobalTheory.HeightCounting.Up.FinitenessListStatement hL cDep) : _root_.GlobalTheory.HeightCounting.Up.SpectralFiniteness hL cDep := by
  refine StepW.trans h (StepW.of_all fun K B f T w _ _ H P x l S Γ hl => ?_)
  obtain ⟨Z, v, h1, h2⟩ := H P x l S Γ hl.1
  exact ⟨Z, { g := v.g, coh := v.coh, Wt := v.Wt, p0 := v.p0, what₂ := v.what₂, rx := v.rx, nch := v.nch, n := v.n, xd := v.xd,
              chiT := v.chiT, nx := ⟨v.nx.1, v.nx.2, ⟨P, x, l, hl, h1, h2⟩⟩ }, h1, h2⟩
theorem exists_pre_point_with_henselian_level {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {cDep : ℝ} {S : SExt} {Γ : GeoP} {Z : w.Lt} {c : V4.Core K (w.st Z) f T}
    (b : Built (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) S Γ).s K w Z c) (e : ExportAt (w.st Z).toD7 c.O.nch c.O.xd) :
    ∃ (P : Pre2 K w) (x : St P) (_ : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x), (ListSt cDep x ∧ SatU P) ∧ ∀ A, Nonempty (Seed (Dof x) A) := by
  obtain ⟨P, x, l, hl, hW, hk⟩ := b.nx.2.2.down
  have key := (TupTieW.tupTied_of_muIsW (w.st Z) f T c.Wt c.xi c.mu).1
  refine ⟨P, x, l, hl, GlobalTheory.HeightCounting.Up.nonempty_seed_of_kept (Dof x) (w.st Z).toD7 l.c.ch c.O.nch c.O.xd hk rfl (fun v v₀ hv ht => ?_) l.c.side.nct
    l.c.side.choice.twI_conj ?_ B.coeffGaloisSubfield_isGalois (twistedPlaceIndex_mem_firstPair_of_compatibleChoice (w.st Z).toD7 c.O.nch c.nch_tie B.coeffGaloisSubfield_isGalois) e b.nx.2.1.1.1.xd⟩
  · obtain rfl : v = v₀ := eq_of_heq hv
    exact (key v).2 (hW ▸ (twisted_st x v).1 ht)
  · exact (TupTieW.tupTied_of_muIsW (w.st x.o.Z) f T P.Wt w.I.xi (muIsW_st x)).2.1.subset fun v hv => (twisted_st x v).1 hv
end GlobalTheory.HeightCounting.Up
end
