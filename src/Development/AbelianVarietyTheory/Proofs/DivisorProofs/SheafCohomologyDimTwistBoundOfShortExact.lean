module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem hdim_twist_bound_of_shortExact : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (L : LB X), L.IsLB → ∀ S : ShortComplex X.Modules, S.ShortExact → IsFiniteQC S.X₁ → IsFiniteQC S.X₃ → ∀ (i : ℕ) (e : ℕ → ℕ), (∃ C : ℕ, ∀ m : ℕ, hdim k (twist S.X₁ (lbPow L m)) i ≤ C * e m) → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist S.X₃ (lbPow L m)) i ≤ C * e m) → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist S.X₂ (lbPow L m)) i ≤ C * e m) := by
  intro k _ _ X _ hX L hL S hS h1 h3 i e hb1 hb3
  obtain ⟨C₁, hC₁⟩ := hb1
  obtain ⟨C₃, hC₃⟩ := hb3
  obtain ⟨hP, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB (strHom k X)).1 hX
  have hf := algebraMap_eq_strHom k X
  have F₁ : FiniteCohTwists k S.X₁ := IsAmpleLB.finiteCohTwists hf S.X₁ hA
  have F₃ : FiniteCohTwists k S.X₃ := IsAmpleLB.finiteCohTwists hf S.X₃ hA
  refine ⟨C₁ + C₃, fun m => ?_⟩
  have hLm : (lbPow L m).IsLB := isLB_lbPow hL m
  have hT := Twist.shortExact_map hLm hS
  have fin₁ := ((F₁.twist hLm).finiteCoh).finite i
  have fin₃ := ((F₃.twist hLm).finiteCoh).finite i
  have key := hdim₂_le k hT i fin₁ fin₃
  calc hdim k (twist S.X₂ (lbPow L m)) i ≤ hdim k (twist S.X₁ (lbPow L m)) i + hdim k (twist S.X₃ (lbPow L m)) i := key
    _ ≤ C₁ * e m + C₃ * e m := Nat.add_le_add (hC₁ m) (hC₃ m)
    _ = (C₁ + C₃) * e m := (Nat.add_mul C₁ C₃ (e m)).symm

end GlobalTheory
