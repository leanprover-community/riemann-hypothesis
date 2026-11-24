module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SesLatticeTrivialQuotient
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

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.ses_lattice_trivial_quotient : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm5 D → adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (e : ℕ) (Yt T Z : LocLat S.G S.Qp S.LL S.O) (ι : LatHom T.L Yt.L) (π : LatHom Yt.L Z.L) (hle : Gj K s ≤ GK K), IsSESLat (Qp := S.Qp) ι π → (∀ g x, Z.ρ g x = x) → IsCrysOn S S.W.GKs Yt → ∀ yt ∈ Yt.L.T, ∀ f : S.G → ↥T.L.T, (∀ g, ι.f (f g : T.V) = Yt.ρ g yt - yt) → ∀ one : ↥(Mxi (AinfSub l) (xiU (D.locA l)) 0), (one : WCb l) = 1 → letI := zlMod LL T; ∃ k : ℕ, IsCob (repQ (D.locA l) (Gj K s) ((actTZ LL T).comp (Subgroup.inclusion hle)) 0 ((e : ℤ) + 1)) (fun g => (l : ℤ_[l]) ^ k • (f (Subgroup.inclusion hle g) ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU (D.locA l)) 0 ((e : ℤ) + 1)))) := by
  first | exact @GlobalTheory.Adopt.ses_lattice_trivial_quotient | exact GlobalTheory.Adopt.ses_lattice_trivial_quotient | (intros; apply GlobalTheory.Adopt.ses_lattice_trivial_quotient <;> assumption)
