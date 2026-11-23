module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionLayerIoCommutesFrobeniusGalois
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem _root_.GlobalTheory.T.wachInclusionLayer_io_commutes_frobenius_galois : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R) (S : Type) [CommRing S] (f f' : RA LL →+* S), ((∀ o w, f' (o ⊗ₜ[ℤ_[l]] w) = f (o ⊗ₜ[ℤ_[l]] WittVector.frobenius w)) → ∀ a, f (I.io (letφ R.φ₀ a)) = f' (I.io a)) ∧ ∀ g : ↥(GK K), (∀ o w, f' (o ⊗ₜ[ℤ_[l]] w) = f (o ⊗ₜ[ℤ_[l]] AI.actW (g : GQ l) w)) → ∀ a, f (I.io (letγ (R.γ₀ (Γ.resΓ g)) a)) = f' (I.io a) := by
  first | exact @GlobalTheory.HWL.IoComm.main | exact GlobalTheory.HWL.IoComm.main | (intros; apply GlobalTheory.HWL.IoComm.main <;> assumption)
