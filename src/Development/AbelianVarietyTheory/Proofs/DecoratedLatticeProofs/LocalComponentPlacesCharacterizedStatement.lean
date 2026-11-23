module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentPlacesCharacterized
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.local_component_places_characterized : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b : ∀ j, GA D (Yc D j)) (v : VCom (commOf (pk W) u (mkGeo m b))), (commOf (pk W) u (mkGeo m b)).Is → v.τ = y.τ → v.NT = a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → GlobalTheory.Core.Mi.IsTypePlaces (pk W).Pg → (∀ j, b j ∈ GfC (Yc D j)) → a.bT ∈ GfC D.sp.X' → IsSelfDualC D.sp.X' a.LT → (∀ P, GlobalTheory.FinPl.Moves D.sp.X' a.bT (pk W).ΛX a.LT P) → (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (v.N j) ∧ ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ p, P p → p ∉ v.gP) → GlobalTheory.FinPl.Moves (Yc D j) (b j) ((pk W).ΛY j) (v.N j) P) → v.b = b → v.bT = a.bT → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → ∃ (Ψ : ∀ j, PolF D (Yc D (j + 1)).rank (Yc D j).rank → GA D (Yc D j) → GA D (Yc D (j + 1)) → WO (Yc D j) (Yc D (j + 1)) → ℂ) (ΨT : ∀ j, j + 2 * 0 + 2 = D.R.m → PolF D D.sp.X'.rank (Yc D (j + 1)).rank → WO (Yc D (j + 1)) D.sp.X' → ℂ), (∀ j, j + 1 < D.R.m → ∀ P, ∀ x ∈ GinfC _, ∀ x' ∈ GinfC _, GlobalTheory.FinPl.Vac (pk W).ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) (Ψ j P x x')) ∧ (∀ j h P, GlobalTheory.FinPl.Vac (pk W).ψ _ _ (v.N (j + 1)) v.NT (fun _ => True) (ΨT j h P)) ∧ ∀ j row col, VTie (⟨mkGeo m b, j, row, col⟩ : FamCh W u) { v with Ψ := Ψ, ΨT := ΨT } := by
  first | exact @GlobalTheory.CommonVac.exists_common_vacua | exact GlobalTheory.CommonVac.exists_common_vacua | (intros; apply GlobalTheory.CommonVac.exists_common_vacua <;> assumption)
