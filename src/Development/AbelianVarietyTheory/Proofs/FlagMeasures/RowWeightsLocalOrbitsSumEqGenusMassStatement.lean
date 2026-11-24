module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowWeightsLocalOrbitsSumEqGenusMass
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

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs Formalism.FourierDecayAlt GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rowWeights_localOrbits_sum_eq_genusMass : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ {Cl : Type} (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl) (Fm : LocFam (zOf Y) Cl (NuC D)), Based (zOf Y) Fm.FP (Tu D u) (Tu D u') F F' → ClsRow TS cls → LocClosed F F' (zOf Y) Fm.FP TS → (∀ p ∈ Fm.P, ∀ d ∈ Fm.Ds p, d ∈ (Fm.R p).RD) → (∀ p, p ∉ Fm.P → ∀ t ∈ TS, ptPN t = toPts w → OverOrb Fm t p (Fm.d0 p)) → (∃ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ ∧ ∀ p, p ∉ Fm.P → ∃ τ, LocNG.IsTermOver (Fm.FP p) (Fm.d0 p) τ ∧ τ.abelian₂ = lattice₂ D (zOf Y).M p Λ₀) → (∀ c ν, (Fm.dat c ν = none → ¬ ∃ t ∈ TS, cls t = c ∧ ptPN t = toPts w ∧ nmlOf Y u u' t = ν) ∧ ∀ d, Fm.dat c ν = some d → (∃ t ∈ TS, cls t = c ∧ ptPN t = toPts w ∧ nmlOf Y u u' t = ν) ∧ ∀ t ∈ TS, cls t = c → ptPN t = toPts w → nmlOf Y u u' t = ν → (∀ p (hp : p ∈ Fm.P), OverOrb Fm t p (d ⟨p, hp⟩).1) ∧ Fm.rw c = (wt t) ^ 2) → ∀ d : (∀ p : {p // p ∈ Fm.P}, {d // d ∈ Fm.Ds p.1}), (∃ x : Cl × NuC D, Fm.dat x.1 x.2 = some d) → ∀ dd : Dat (zOf Y) Fm.FP, (∀ p (hp : p ∈ Fm.P), dd p = (d ⟨p, hp⟩).1) → (∀ p, p ∉ Fm.P → dd p = Fm.d0 p) → (∀ p, ∃ τ, LocNG.IsTermOver (Fm.FP p) (dd p) τ) ∧ ∑' x : {x : Cl × NuC D // Fm.dat x.1 x.2 = some d}, ENNReal.ofReal (Fm.rw x.1.1) = massA F F' dd := by
  first | exact @GlobalTheory.Unfold.GenusRows.rows_mass_genus | exact GlobalTheory.Unfold.GenusRows.rows_mass_genus | (intros; apply GlobalTheory.Unfold.GenusRows.rows_mass_genus <;> assumption)
