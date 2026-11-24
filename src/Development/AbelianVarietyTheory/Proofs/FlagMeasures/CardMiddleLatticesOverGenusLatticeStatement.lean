module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardMiddleLatticesOverGenusLattice
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

@[expose] public section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.card_middleLattices_over_genus_lattice : ∀ (D : D7) (u : D.what₂.Word), (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) → ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ M ∈ Formalism.HermitianLatticesTheory.genus (D.sp.X 0).hT (L0X D Λ (lf D F0)), {𝓛 : Submodule (𝓞 D.host.E) ((D.sp.X 0).V × D.host.E) | (∃ Λ', IsRowLat D F0 Λ' ∧ (Lsub Λ' (lf D F0)).comap (((D.sp.iXY 0).coprod (LinearMap.toSpanSingleton D.host.E (VS D).V F0.z)).restrictScalars (𝓞 D.host.E)) = 𝓛) ∧ 𝓛.comap ((LinearMap.inl D.host.E (D.sp.X 0).V D.host.E).restrictScalars (𝓞 D.host.E)) = M}.ncard = (Tu D u - 1) ^ D.R.f := by
  first | exact @GlobalTheory.LoopC.GluingNum.gluingNum | exact GlobalTheory.LoopC.GluingNum.gluingNum | (intros; apply GlobalTheory.LoopC.GluingNum.gluingNum <;> assumption)
