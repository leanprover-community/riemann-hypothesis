module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalTermsSameDoubleCosetSameLocalData
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.global_terms_same_doubleCoset_same_local_data : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → ∀ F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), PD D Λ (lf D F0) u' F₁ → PD D Λ (lf D F0) u' F₂ → Gval (lf D F0) F₁ ≠ 0 → ∀ n ∈ Formalism.L2.SG.NGData.NRat (lf D F0), ∀ m ∈ Formalism.L2.SG.NGData.NRat F₁, Formalism.HermitianLatticesTheory.gmap (n * m) Λ = Λ → (∀ a, frame F₂ a = (n * m) (frame F₁ a)) → IotaCompat Λ (lf D F0) F₁ F₂ (n * m) (gS D) → ∀ (p : PlF D) (P : LocNG.FPair (locH Z p) D.R.rS), P.RelG (LocNG.theta (Z.M p)) → ∀ d, Over P d (locU Z p Λ (lf D F0) F₁ (Tu D u) (Tu D u')) → Over P d (locU Z p Λ (lf D F0) F₂ (Tu D u) (Tu D u')) := by
  first | exact @GlobalTheory.LocSame.over_same | exact GlobalTheory.LocSame.over_same | (intros; apply GlobalTheory.LocSame.over_same <;> assumption)
